# P3.4 Literal Coprime Packet Interfaces Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans to implement this plan task-by-task. The user has already authorized implementation, compilation, and GitHub submission; no new execution approval is needed.

**Goal:** Strictly compile and kernel-check the existing literal coprime packet/cusp pairing, its mode norm identities, and the manuscript's scalar oldform phase cancellation without importing unrelated distribution or spectral foundations.

**Architecture:** Move existing declarations to small modules, retaining every public qualified name and type. Reuse the previously accepted seven actual-cusp modules. Preserve original source archives and record donor blocks, hashes, and any compiler-driven proof repair. The original `OriginalData` assembly and actual spectral coefficient suppliers remain distinct obligations.

**Tech Stack:** Lean 4.33.0-rc1 at `62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; the unchanged repository manifest.

**Spec:** 1106 Appendix B in `UyNewNas/chen-imbalanced-semiprimes` commit `8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703`, `paper/release-20261106/en/analytic-appendix.tex`, cusp/packet paragraphs at lines 951–982. Existing source baseline is `f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e`; accepted cusp scope is `3b3aa92475d0d6ab12a0652cc6cf2561afb99ac7`.

## Global Constraints

- Reuse existing local/remote code. Do not repeat P3.5's accepted continuous Cauchy/exhaustion work.
- No `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, or kernel bypass. Transitive axioms must stay within `propext`, `Classical.choice`, and `Quot.sound`.
- Preserve `CoprimePacket`, its beta, multiplier, positive level, residue coprimality, and the original coefficient gate; preserve mode phases `k 2 / 64` and `k 3 / 64` with their physical scales.
- Do not replace missing `OriginalMediumPhysicalE3Block.FixedBlock` or `OriginalData` with another structure. Do not claim the old four staged row theorems compiled.
- Fixed-height Haar coefficients remain fixed-height coefficients. Neither the scalar phase identity nor chart pairing proves the oldform coefficient relation or identifies a Maass/Eisenstein `R(n)`.
- Keep the seven-module acceptance report and original archives immutable. Add new acceptance evidence for this exact source revision.
- Root owns the P3 MCP queue and GitHub publication. Source worker may use the existing local pinned runtime for focused elaboration.

## Review Focus

- Moved declarations retain their full names, parameters, conclusions, and implementation semantics; no duplicate active definition remains.
- The coprimality-false branch remains zero, including after modulation and chart multiplication.
- The two retained mode phases use indices 2 and 3 and physical denominators `64*U`, `64*Z`.
- Both choices of scalar sign leave the intended opposite cusp phase. A phase calculation is not labelled an oldform spectral theorem.
- Strict compilation, defining-module declaration enumeration, parsed import provenance, and bundled kernel replay cover every accepted module and all generated declarations.

## Task 1: Isolate, reuse, and verify the existing packet/cusp interface

**Files to create:**

- `ImbalancedChen/Part3FourierModeIndex.lean`: move `P3NativePeriod64SamplingSourceOnly.D4 := Fin 4`.
- `ImbalancedChen/Part3CoprimePacketCore.lean`: move `ImbalancedChen.Part3.CoprimePacket` and `CoprimePacket.transformedCoefficient` from `Part3DistributionTargets`.
- `ImbalancedChen/Part3CoprimePacketCoefficients.lean`: move the ten existing declarations from `signedCoefficient` through `modePacket_finite_fibre_l2` in `Part3ActualLiteralPacketIntegral`.
- `ImbalancedChen/Part3OldformCuspPhase.lean`: move `ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.signed_cusp_phase_cancel`; derive the exact exponential phase product using the existing `e_add`, and its signed actual-cusp Fourier consequence.
- `verification/P34CuspPacketAudit.lean` and `verification/verify_p34_cusp_packet.py`: reuse the existing auditor and verifier mechanics for the exact 13-module scope below.
- `docs/part3-distribution/p34-20261126/DECLARATION_MOVES.json`: record donor commit, path, declaration/type text or exact block, and original SHA-256 for every move; explicitly list proof repairs.

**Existing files to modify:**

- `Part3CuspPhaseCore.lean`: move the existing `P3Period64NativeReconstructionSourceOnly.norm_e` here, with a minimal proof from `Complex.norm_exp` if required to remove its unrelated Fourier-series import.
- `Part3NativePeriod64Sampling.lean`, `Part3NativePeriod64Reconstruction.lean`, `Part3DistributionTargets.lean`, `Part3ActualLiteralPacketIntegral.lean`, `Part3ActualPoissonNormalizedFScalar.lean`: import the moved declarations and remove only their original declaration blocks.
- `Part3ActualCuspScalingSourceOnly.lean` and `Part3ActualCuspPacketPairing.lean`: replace the large literal-integral import with the new coefficient module. Retain their seven and two existing proof declarations respectively, repairing only elaboration/API issues if needed.
- `verification/verify_p34_cusp_normalization.py`: if needed, parameterize module/auditor/scope/output-directory choices while preserving old seven-module defaults and reusing its import guard/inventory validation. Bind the new entry point's bytes in the source manifest. Do not weaken strictness or provenance checks.

**Interfaces:**

- Every moved public signature is copied from the baseline verbatim.
- New `oldform_cusp_phase_mul (eta A nu n z : ℝ)` proves `e (-eta*A*(nu*n)/z) * e (eta*n*(A*nu-1)/z) = e (-eta*n/z)` in a clearly scoped phase namespace.
- A Boolean-signed corollary uses `eta = if negative then -1 else 1`, natural frequency/level, and returns the existing `cuspPhase negative N n`.
- Its actual-cusp corollary multiplies the same two phases by `oldFourierCoeff` at signed frequency and concludes `newFourierCoeff`, keeping `0 < N`, actual Gamma0 invariance, and `0 < y`. No spectral coefficient map or spectral identity is an input or conclusion.

**Acceptance modules, in dependency order:**

1. `Part3FourierModeIndex`
2. `Part3CoprimePacketCore`
3. `Part3CuspPhaseCore`
4. `Part3Gamma0ActualCusps`
5. `Part3CuspScalingMatrices`
6. `Part3ActualCuspWidthNormalization`
7. `Part3CuspTranslationFourierPhase`
8. `Part3ActualCuspFourierSection`
9. `Part3SignedCuspFourierSection`
10. `Part3CoprimePacketCoefficients`
11. `Part3ActualCuspScalingSourceOnly`
12. `Part3ActualCuspPacketPairing`
13. `Part3OldformCuspPhase`

- [ ] Preserve donor blocks and compare public signatures before migration.
- [ ] Move definitions/proofs; update donor imports; implement only the three phase consequences above.
- [ ] Elaborate the exact acceptance modules with the pinned local runtime as needed; root runs the complete cloud acceptance.
- [ ] Record all compiler-driven repairs and verify no changes to unrelated original bodies or source archives.
- [ ] On an exact clean Git source commit, strictly compile every module with warnings as errors, check actual parsed project imports, run bundled `leanchecker`, and enumerate all defining-module declarations/transitive axioms.
- [ ] Independently review the exact source/evidence diff and publish code plus receipts to the existing P3.4 branch/PR.

## Subsequent manuscript work

After this unit, inspect the original finite tuple carrier's primary arithmetic (`rhoPrimaryNu`, exact signed quotient, original beta support, and ABL's integer K=1). This is a separate implementation decision, with the existing source objects preserved. No claim of completion of P3.4 or its four staged `OriginalData` consumers is made by Task 1.
