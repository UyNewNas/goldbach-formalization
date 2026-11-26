# P3.4 Fricke phase implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Accept the original cusp-one / literal Fricke Fourier phase proofs in their true ten-module closure.

**Architecture:** Keep the four existing owners and six accepted providers. Apply the existing terminal API repair and use a thin wrapper around the unchanged P3.4 verifier. Root coordinates exact-tree publication, the clean cloud gate and independent review.

**Tech Stack:** Lean 4.33.0-rc1, compiler `62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; Python 3; original Lake pins.

**Spec:** `docs/superpowers/specs/2026-11-26-p34-fricke-phase-design.md`

## Global Constraints

- Work only in `/workspace/library-files/p34-proof-work`, on the existing P3.4 branch. Root owns GitHub publication and cloud scheduling; no other worktree/job may be changed or cancelled.
- Reuse existing reliable work; no new outside-manuscript foundation and no substitute original or spectral type.
- Preserve all original definitions, statements, hypotheses, signed frequencies, both square-root scaling factors and normalized Haar measure.
- No `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, or kernel bypass.
- Shared verifier, package pins and previous accepted source bindings stay unchanged.
- Compilation failure requires the exact diagnostic and source/manuscript comparison; classify expression issues separately from omitted derivations or possible substantive gaps.
- Full P3.4 and historical D20 remain incomplete. Do not claim a Fourier section is already the DI/Whittaker-normalized spectral coefficient.

## Review Focus

- Every integer frequency, including zero and negative values: preserve the original quantified theorem and positive phase sign; inspect printed types after compilation.
- Level-one and small positive level: retain `0 < N`, original width/divisibility statements and exact square-root normalization; no new lower bound.
- Integrability and Gamma0 hypotheses: retain their original premises and measure; no implicit Fricke eigenfunction assumption.
- Provider ownership and caches: fresh ten-module scope, complete generated/private inventory, exact old six-provider record comparisons and resolved import paths.
- Source-only historical HOLD versus new acceptance: preserve the archival registry and document only this newly checked scope.

---

### Task 1: Restore the existing Fricke phase proof and its complete acceptance entry point

**Files:**
- Modify: `ImbalancedChen/Part3ActualFrickeCuspPhase.lean`
- Inspect and retain: `ImbalancedChen/Part3FrickeNormalizer.lean`, `ImbalancedChen/Part3Gamma0GeneralCuspWidth.lean`, `ImbalancedChen/Part3Gamma0GeneralCuspUnitPeriod.lean`
- Create: `verification/verify_p34_fricke_phase.py`, `verification/P34FrickePhaseAudit.lean`
- Create: `docs/part3-distribution/p34-fricke-phase-20261126/SOURCE_INTAKE.json`
- Read: `docs/part3-distribution/p34-fricke-phase-20261126/NEXT_ENDPOINT_AUDIT.md`

**Interfaces:**
- Consumes six exact accepted providers from `docs/part3-distribution/p34-20261126/packet-cloud-report.json`, source `145be87ff0a88914b607baa2a330bc88105a08d6`.
- Produces the existing original endpoint names and a ten-module gate. Topological module order: `Part3CuspPhaseCore`, `Part3Gamma0ActualCusps`, `Part3CuspScalingMatrices`, `Part3ActualCuspWidthNormalization`, `Part3CuspTranslationFourierPhase`, `Part3ActualCuspFourierSection`, `Part3FrickeNormalizer`, `Part3Gamma0GeneralCuspWidth`, `Part3Gamma0GeneralCuspUnitPeriod`, `Part3ActualFrickeCuspPhase`, all prefixed `ImbalancedChen.`.
- Gate CLI: `python3 -B verification/verify_p34_fricke_phase.py --expected-head <exact-source-head> --output-dir <own-evidence-directory>`; root will run it once source is published. Keep shared verifier logic unchanged. Baseline is `da576de2c91df467d1865baee9c1b1b84ddc529b`; bind the wrapper and SOURCE_INTAKE as extra_sources.

- [ ] Compare the four original owners and six accepted provider source hashes against the named provenance. Record full file hashes, original declaration names/kinds, exact repair mapping and original/repaired identities in SOURCE_INTAKE.
- [ ] Install the exact archived terminal repair at `docs/source-only/20261102-resume-30r/oldform_continuous/repairs/Part3ActualFrickeCuspPhase.lean`: donor `fa22a56829ee880404516a36d498ce27dcb32f92`, blob `8b47c8a7f053af911e13009e2a2676f9968f572c`, 8053 bytes, SHA256 `749882d348253efdfb33387299a30653f0484b0810eeac84a761c2433609fddf`. Verify equality after the nine-line header and five `AddCircle.fourier` prefix replacements. Preserve historical status comments; current acceptance is documented separately.
- [ ] Add the thin verifier entry and the ten-owner auditor. Copy only the existing audit mechanism, changing imports and owner list; no filters that omit generated/private declarations. Do not alter shared validators or their meaningful import-scope regression gate.
- [ ] Run the source-only gate and `git diff --check`, verify all previous accepted source bindings remain unchanged, and self-review the exact source delta. No local Lean compile. Commit the prepared source and notify root with exact commit/tree and bounded diff summary.
- [ ] Await root's published source mapping and full cloud receipt. If a compiler diagnostic appears, repair only its documented cause against the original source and manuscript; send each clean repair commit to root. Retain failed logs. Do not start a second compiler job or change a cloud environment yourself.
- [ ] After the complete gate passes, inspect all ten-module declarations, exact reused six-provider inventory equality, allowed transitive axioms, source/object bindings and actual terminal types. Write the assigned full report and return DONE with commit, test summary and concerns. Root will dispatch independent task review and one final publication review.

## Root closeout

Root preserves the audited source and every diagnostic, completes source-history/publication mapping, archives the full acceptance and bounded source-recovery delta, and updates existing draft PR #8. The fresh gate covers only these ten project modules. Old finite-scope receipts are retained; a union count must state it is a union of separate accepted runs. No whole-P3.4 green promotion or merge follows from this phase unit.
