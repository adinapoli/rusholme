{-# LANGUAGE NoImplicitPrelude #-}
-- | RHC.Prim — the innermost boot package (placeholder).
--
-- This module will eventually own every `foreign import prim`
-- declaration in the system: the raw doorway into Rusholme's PrimOp
-- registry.  See `docs/plans/2026-06-13-ghc-internal-base-split.md`
-- §3 Milestone 1a for the contents that move here from `lib/Prelude.hs`.
--
-- For now the module is empty: it exists so that the multi-boot driver
-- pipeline (`build.zig` + `cmdBuild`) compiles it ahead of `Prelude`
-- and we can prove the layered Prelude stack works end-to-end before
-- moving real declarations.  The actual primop move is tracked
-- separately in the milestone follow-up.
module RHC.Prim where
