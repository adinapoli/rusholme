#!/usr/bin/env bash
# bench.sh — benchmark harness for rhc-compiled programs (#758, Epic #754 D1).
#
# Builds a Haskell program with `rhc build` (default -O2), optionally builds
# a GHC baseline of the same source, sanity-checks that all binaries produce
# identical stdout, then times them under hyperfine.
#
# Usage:
#   scripts/bench.sh [options] <prog.hs>
#
# Options:
#   -n <runs>      hyperfine run count            (default: 10)
#   -w <warmups>   hyperfine warm-up count        (default: 3)
#   -O <level>     rhc optimisation level 0..3    (default: 2)
#   -g             also benchmark a GHC -O2 baseline (requires ghc on PATH)
#   -j <file>      export hyperfine results as JSON to <file>
#   -k             keep the temporary build directory (prints its path)
#   -h             show this help
#
# Environment:
#   RHC            path to the rhc binary (default: ./zig-out/bin/rhc,
#                  falling back to `rhc` on PATH)
#
# Exit codes:
#   0 success; 1 usage/build error; 2 sanity check failed (output mismatch).

set -euo pipefail

usage() { sed -n '2,24p' "$0" | sed 's/^# \{0,1\}//'; }

runs=10
warmups=3
opt_level=2
ghc_baseline=0
json_out=""
keep_tmp=0

while getopts "n:w:O:gj:kh" opt; do
    case "$opt" in
        n) runs="$OPTARG" ;;
        w) warmups="$OPTARG" ;;
        O) opt_level="$OPTARG" ;;
        g) ghc_baseline=1 ;;
        j) json_out="$OPTARG" ;;
        k) keep_tmp=1 ;;
        h) usage; exit 0 ;;
        *) usage >&2; exit 1 ;;
    esac
done
shift $((OPTIND - 1))

if [ $# -ne 1 ]; then
    echo "bench.sh: expected exactly one <prog.hs> argument" >&2
    usage >&2
    exit 1
fi

prog="$1"
if [ ! -f "$prog" ]; then
    echo "bench.sh: no such file: $prog" >&2
    exit 1
fi

if ! command -v hyperfine > /dev/null; then
    echo "bench.sh: hyperfine not found on PATH (enter the dev shell: nix develop)" >&2
    exit 1
fi

# Locate rhc: $RHC override, then the local build, then PATH.
rhc="${RHC:-}"
if [ -z "$rhc" ]; then
    if [ -x "./zig-out/bin/rhc" ]; then
        rhc="./zig-out/bin/rhc"
    elif command -v rhc > /dev/null; then
        rhc="rhc"
    else
        echo "bench.sh: rhc not found — build it first (zig build) or set \$RHC" >&2
        exit 1
    fi
fi

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/rhc-bench.XXXXXX")"
cleanup() {
    if [ "$keep_tmp" -eq 1 ]; then
        echo "bench.sh: build artifacts kept in $tmpdir"
    else
        rm -rf "$tmpdir"
    fi
}
trap cleanup EXIT

base="$(basename "${prog%.hs}")"
rhc_bin="$tmpdir/$base-rhc"
ghc_bin="$tmpdir/$base-ghc"

# ── Build ────────────────────────────────────────────────────────────────────

echo "bench.sh: rhc build -O$opt_level $prog"
"$rhc" build "-O$opt_level" -o "$rhc_bin" "$prog"

if [ "$ghc_baseline" -eq 1 ]; then
    if ! command -v ghc > /dev/null; then
        echo "bench.sh: -g given but ghc not found on PATH" >&2
        exit 1
    fi
    echo "bench.sh: ghc -O2 $prog"
    ghc -O2 -outputdir "$tmpdir/ghc-out" -o "$ghc_bin" "$prog" > /dev/null
fi

# ── Sanity check: identical stdout before timing ────────────────────────────

"$rhc_bin" > "$tmpdir/out-rhc.txt" || {
    echo "bench.sh: rhc-compiled binary failed to run" >&2
    exit 2
}

if [ "$ghc_baseline" -eq 1 ]; then
    "$ghc_bin" > "$tmpdir/out-ghc.txt" || {
        echo "bench.sh: ghc-compiled binary failed to run" >&2
        exit 2
    }
    if ! diff -u "$tmpdir/out-ghc.txt" "$tmpdir/out-rhc.txt" > "$tmpdir/out.diff"; then
        echo "bench.sh: SANITY CHECK FAILED — rhc and ghc outputs differ:" >&2
        cat "$tmpdir/out.diff" >&2
        exit 2
    fi
    echo "bench.sh: sanity check passed (outputs identical)"
fi

# ── Benchmark ────────────────────────────────────────────────────────────────

# --shell=none: we time plain binaries, and compute-bound micros can
# complete in <5ms where shell startup would dominate the measurement.
hyperfine_args=(--shell=none --warmup "$warmups" --runs "$runs")
if [ -n "$json_out" ]; then
    hyperfine_args+=(--export-json "$json_out")
fi

if [ "$ghc_baseline" -eq 1 ]; then
    hyperfine "${hyperfine_args[@]}" \
        --command-name "rhc -O$opt_level" "$rhc_bin" \
        --command-name "ghc -O2" "$ghc_bin"
else
    hyperfine "${hyperfine_args[@]}" \
        --command-name "rhc -O$opt_level" "$rhc_bin"
fi
