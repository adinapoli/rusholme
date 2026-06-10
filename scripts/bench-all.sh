#!/usr/bin/env bash
# bench-all.sh — run every bench/*.hs against rhc and ghc, append a
# single dated entry to bench/results.json.
#
# Invoke manually before opening a PR (see CLAUDE.md §"Benchmarks").
# The bench/results.json file is checked in; the website's deploy
# step renders it as time-series charts at `/bench/`.
#
# Usage:
#   scripts/bench-all.sh             # 7 runs, 3 warmups, -O2
#   scripts/bench-all.sh -n 10       # 10 runs
#   scripts/bench-all.sh --dry-run   # print the JSON entry, don't append
#
# Output: appends one entry to `bench/results.json`. Each entry is:
#   {
#     "commit":     "<git rev-parse HEAD>",
#     "date":       "<ISO-8601 UTC>",
#     "host":       { "os": "...", "cpu_model": "...", "ghc_version": "..." },
#     "programs":   { "<name>": { "rhc_mean_ms": ..., "rhc_stddev_ms": ...,
#                                 "ghc_mean_ms": ..., "ghc_stddev_ms": ... } }
#   }
#
# Requirements:
#   - hyperfine on PATH (provided by the Nix dev shell)
#   - ghc on PATH (system ghcup install; bench-all.sh records its
#     version into the JSON entry for reproducibility)
#   - jq on PATH

set -euo pipefail

runs=7
warmups=3
opt_level=2
dry_run=0

while [ $# -gt 0 ]; do
    case "$1" in
        -n) runs="$2"; shift 2 ;;
        -w) warmups="$2"; shift 2 ;;
        -O) opt_level="$2"; shift 2 ;;
        --dry-run) dry_run=1; shift ;;
        -h|--help)
            sed -n '2,28p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "bench-all.sh: unknown arg: $1" >&2
            exit 1
            ;;
    esac
done

for tool in hyperfine ghc jq git; do
    if ! command -v "$tool" > /dev/null; then
        echo "bench-all.sh: $tool not on PATH" >&2
        exit 1
    fi
done

if [ ! -x "./zig-out/bin/rhc" ]; then
    echo "bench-all.sh: ./zig-out/bin/rhc missing — run \`zig build\` first" >&2
    exit 1
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [ ! -d "bench" ]; then
    echo "bench-all.sh: no bench/ directory" >&2
    exit 1
fi

shopt -s nullglob
progs=( bench/*.hs )
shopt -u nullglob

if [ ${#progs[@]} -eq 0 ]; then
    echo "bench-all.sh: no bench/*.hs files" >&2
    exit 1
fi

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/rhc-bench-all.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

ghc_version="$(ghc --numeric-version)"
rhc_commit="$(git rev-parse HEAD)"
date_iso="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
os_kernel="$(uname -sr)"
cpu_model="$(awk -F': ' '/model name/ {print $2; exit}' /proc/cpuinfo 2>/dev/null || echo unknown)"

programs_json="$tmpdir/programs.json"
echo "{}" > "$programs_json"

for src in "${progs[@]}"; do
    base="$(basename "${src%.hs}")"
    rhc_bin="$tmpdir/$base-rhc"
    ghc_bin="$tmpdir/$base-ghc"
    ghc_outdir="$tmpdir/ghc-out-$base"

    rhc_immix_bin="$tmpdir/$base-rhc-immix"

    echo "bench-all.sh: building $base"
    ./zig-out/bin/rhc build "-O$opt_level" -o "$rhc_bin" "$src" 2>&1 | grep -vE "warning|deprecat|^$" || true
    ./zig-out/bin/rhc build "-O$opt_level" --rts=immix -o "$rhc_immix_bin" "$src" 2>&1 | grep -vE "warning|deprecat|^$" || true
    # GHC's linker needs libgmp. Inside the Nix dev shell `-lgmp` is
    # not on the default search path; outside it usually is. Probe a
    # few common locations and prepend whichever holds libgmp.so.10.
    ghc_link_args=()
    for d in /usr/lib /usr/lib64 /usr/lib/x86_64-linux-gnu /lib /lib64; do
        if [ -e "$d/libgmp.so.10" ] || [ -e "$d/libgmp.so" ]; then
            # `-optl-L` finds libgmp at link time; `-optl-Wl,-rpath,$d`
            # bakes the path into the ELF so the binary still runs when
            # invoked from inside the Nix dev shell (whose
            # LD_LIBRARY_PATH does not include /usr/lib).
            ghc_link_args+=( "-optl-L$d" "-optl-Wl,-rpath,$d" )
            break
        fi
    done
    ghc -O2 -outputdir "$ghc_outdir" -o "$ghc_bin" "${ghc_link_args[@]}" "$src" > /dev/null

    rhc_out="$("$rhc_bin")"
    rhc_immix_out="$("$rhc_immix_bin")"
    ghc_out="$("$ghc_bin")"
    if [ "$rhc_out" != "$ghc_out" ]; then
        echo "bench-all.sh: SANITY $base: rhc vs ghc output differ" >&2
        echo "rhc: $rhc_out" >&2
        echo "ghc: $ghc_out" >&2
        exit 2
    fi
    if [ "$rhc_immix_out" != "$ghc_out" ]; then
        echo "bench-all.sh: SANITY $base: rhc --rts=immix output differs" >&2
        echo "rhc:immix: $rhc_immix_out" >&2
        echo "ghc:       $ghc_out" >&2
        exit 2
    fi

    echo "bench-all.sh: timing $base"
    hyperfine --shell=none --warmup "$warmups" --runs "$runs" \
        --export-json "$tmpdir/$base.json" \
        --command-name "rhc -O$opt_level" "$rhc_bin" \
        --command-name "rhc -O$opt_level --rts=immix" "$rhc_immix_bin" \
        --command-name "ghc -O2" "$ghc_bin" > /dev/null

    # hyperfine JSON gives mean/stddev in seconds — convert to ms.
    rhc_mean_ms=$(jq '.results[0].mean * 1000'   "$tmpdir/$base.json")
    rhc_std_ms=$(jq  '.results[0].stddev * 1000' "$tmpdir/$base.json")
    rhc_immix_mean_ms=$(jq '.results[1].mean * 1000'   "$tmpdir/$base.json")
    rhc_immix_std_ms=$(jq  '.results[1].stddev * 1000' "$tmpdir/$base.json")
    ghc_mean_ms=$(jq '.results[2].mean * 1000'   "$tmpdir/$base.json")
    ghc_std_ms=$(jq  '.results[2].stddev * 1000' "$tmpdir/$base.json")

    programs_json_new="$tmpdir/programs.next.json"
    jq --arg name "$base" \
       --argjson rm "$rhc_mean_ms" --argjson rs "$rhc_std_ms" \
       --argjson rim "$rhc_immix_mean_ms" --argjson ris "$rhc_immix_std_ms" \
       --argjson gm "$ghc_mean_ms" --argjson gs "$ghc_std_ms" \
       '. + { ($name): { rhc_mean_ms: $rm, rhc_stddev_ms: $rs,
                         rhc_immix_mean_ms: $rim, rhc_immix_stddev_ms: $ris,
                         ghc_mean_ms: $gm, ghc_stddev_ms: $gs } }' \
       "$programs_json" > "$programs_json_new"
    mv "$programs_json_new" "$programs_json"
done

entry="$(jq -n \
    --arg commit  "$rhc_commit" \
    --arg date    "$date_iso" \
    --arg os      "$os_kernel" \
    --arg cpu     "$cpu_model" \
    --arg ghcv    "$ghc_version" \
    --argjson opt "$opt_level" \
    --argjson runs "$runs" \
    --slurpfile programs "$programs_json" \
    '{
        commit: $commit,
        date:   $date,
        host:   { os: $os, cpu_model: $cpu, ghc_version: $ghcv },
        opt_level: $opt,
        runs:   $runs,
        programs: $programs[0]
    }')"

if [ "$dry_run" -eq 1 ]; then
    echo "$entry" | jq .
    exit 0
fi

results=bench/results.json
if [ ! -f "$results" ]; then
    jq -n '{ schema_version: 1, runs: [] }' > "$results"
fi

merged="$tmpdir/merged.json"
jq --argjson entry "$entry" '.runs += [$entry]' "$results" > "$merged"
mv "$merged" "$results"

echo "bench-all.sh: appended entry to $results"
echo "bench-all.sh: review the change, then \`git add bench/results.json\` and commit"
