# Part A Integration Implementation Plan

> **For agentic workers:** Execute this already authorized integration with superpowers:executing-plans. Preserve the completed source and original evidence; do not reimplement proofs.

**Goal:** Put the verified Part A source closure on `master` through a focused, reviewed PR.

**Architecture:** Recover exactly the source bytes named by the two successful CI manifests. Combine their A3/A4 dependency closures, with the six accepted A4 overlays, and add a two-import library root. Keep the original artifacts and a reproducible provenance check.

**Tech Stack:** Lean 4.33.0-rc1, the unchanged mathlib/goldbach lockfile, Python 3, GitHub.

**Spec:** User instruction of 2026-11-25: continue only the 1106 manuscript, reuse existing reliable work, and consider merging the already compiled Part A. Scope and mathematical boundaries are recorded in `docs/PART_A_INTEGRATION_20261125.md`.

## Global Constraints

- Base: `master` at `28f47bbb3a2e8e4a85736a505462d3ff7a5fc522`.
- Frozen source: `b7b0f5613f1b34855e0da7ad44d1d79ed34519cf`.
- A3 driver: `34f7b3f0516991fe1a9dbe3a08bf76c691d09080`, run `44470415535`.
- A4 driver: `f7ea5972d361d67850dd67292c993d782a73b8a4`, run `44440822784`.
- No new mathematical claims, assumptions, `axiom`, `sorry`, `admit`, `native_decide`, or unsafe proofs.
- Never merge the surrounding unfinished P1–P5 work merely because it shares an ancestor.

## Review Focus

- All six accepted overlays must replace the older common working-tree versions.
- Every required project import must be in the 69-module closure.
- Historical acceptance and the new aggregate-root check must be reported separately.
- External dependency pins and A5 lower/upper-bound premises must remain unchanged.
- Keep the existing main-branch navigation and avoid changing other active worktrees.

## Tasks

- [x] Recover original artifacts, manifests, exact source revisions, and manuscript scope.
- [x] Materialize the 69-module closure and preserve the original artifact ZIP bytes.
- [x] Verify source hashes, declaration ownership/types/axioms, dependency pins, and import closure. Check that the older overlay version is rejected.
- [x] Commit and publish the focused candidate branch; check the new aggregate root in an isolated compiler directory using matching existing dependencies.
- [x] Obtain independent review and retain the successful build, kernel replay, complete declaration audit and validation receipt.

The final integration action is tracked by [PR #9](https://github.com/UyNewNas/goldbach-formalization/pull/9). Merge with an expected head SHA and read back the resulting default branch; the GitHub merge record is authoritative for that action.

## Execution decisions

The user has already authorized continued code submission and consideration of a verified Part A merge. Routine isolation, source selection by immutable manifest, and verification proceed without a new permission round. No proof-body edits are required. Existing successful source compilations are reused; any new root validation is separately identified.
