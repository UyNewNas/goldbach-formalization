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


## Task 2: Reuse the literal primary decomposition and close its ABL arithmetic licences

Read `docs/superpowers/plans/2026-11-26-p34-primary-arithmetic-design.md` for the exact source inventory, proposed endpoint types, and proof suppliers. That design was obtained by inspecting the frozen 1106 manuscript and existing source. This task implements its four small modules as a single dependency-ordered unit.

**Files to create:**

- `ImbalancedChen/Part3PrimaryPrimeSupport.lean`: move the nine listed prime-support declarations under their original public names.
- `ImbalancedChen/Part3LiteralReciprocalSource.lean`: move the exact signed frequency window, Inner definitions, and the original finite carrier/output/weight/fiber/beta declarations and listed proofs. Promote private `carrier_data` to the documented public name with unchanged type and body.
- `ImbalancedChen/Part3FixedRhoPrimaryFiniteCore.lean`: move the 21-declaration generic primary-decomposition prefix; retain the specialized actual-mode consumer in its old file.
- `ImbalancedChen/Part3LiteralPrimaryOldformArithmetic.lean`: promote the archived scalar `oldformCofactor`, reuse its two private arithmetic helpers, and prove the design's two endpoints on actual `primaryFibre` membership and nonzero grouped beta.
- `verification/P34PrimaryArithmeticAudit.lean` and `verification/verify_p34_primary_arithmetic.py`: use the unchanged complete auditor/verifier mechanisms for these four modules, in the order above. Bind the entry point and the new move ledger to the source manifest. Baseline is the accepted packet source `145be87ff0a88914b607baa2a330bc88105a08d6` after root aligns the checkout to its identical tree.
- `docs/part3-distribution/p34-20261126/PRIMARY_DECLARATION_MOVES.json`: record donor revision, exact blocks and SHA-256, all public signatures, the private-to-public helper change, the archive promotion, and any proof repairs.

**Existing files to modify:** only the five active donors listed in design section 4. Import the moved definitions and remove their old active blocks, preserving the retained analytic bodies and their required imports. The archived oldform source is immutable. Task 1 code, shared verifier logic, old evidence, dependency pins, and unrelated modules are outside ownership.

**Mathematical requirements:** retain the original signed integer output; `nu` is the computed primary key. For the natural quotient index derive positivity, `(n, |a|*nu)=1`, `(|a|*nu,z)=1`, and the supported cofactor integer equal to 1 for every label. Obtain all licences from the actual fixed-unit gates and prime-support proofs. For nonzero beta, obtain a source witness with the existing `beta_ne_zero_mem_image` before applying the membership endpoint. No new assumptions of these conclusions, no replacement structure, no new spectral identity, and no inference that nu divides the physical modulus c.

**Acceptance and ownership:** root owns the cloud queue and GitHub publication. The fresh implementer owns these source changes, runs necessary focused local elaboration and a complete four-module local verifier on a clean committed HEAD, records exact commands/output, and returns a commit for root's independent cloud run. The existing 13-module packet scope is reused without another full rebuild unless a concrete changed dependency requires one.

- [ ] Preserve donor text, hashes, names and signatures before migration; inspect all retained donor remainders.
- [ ] Extract the exact four-module dependency closure and implement the two endpoint proofs.
- [ ] Check unchanged signed quotient, fixed-unit gates, physical modulus, complex weights and star of the second atom.
- [ ] Strictly compile the four modules and replay each with the bundled leanchecker; check actual parsed imports and all serialized/defining-module declarations and transitive axioms.
- [ ] Record any Lean API difficulty separately from mathematical omissions or gaps, consulting the manuscript before adding facts.
- [ ] Independently review the source and precise evidence; publish source and receipts to the current P3.4 draft PR. This closes the literal finite arithmetic unit, not the missing OriginalData assembly or spectral R(n) normalization.


## Task 3: Reuse the existing dyadic assembly and short endpoint

Read `docs/superpowers/plans/2026-11-26-p34-dyadic-assembly-design.md` for the exact 20 + 28 original declaration inventory, nine-module acceptance order and manuscript linkage. The bounded reuse audit found these exact donor files recorded as source-only, with no coverage in the inspected P3.1/P3.2/P3.5 acceptance scopes. Do not repeat the already accepted common-completed interface.

**Owned source files:** create `ImbalancedChen/Part3PrimaryDyadicShortEndpoint.lean` and `ImbalancedChen/Part3PrimaryDyadicAssembly.lean`; modify only their two original `Part3ZActualPrimary*` donors to import the cores and remove the moved blocks. Retain the five short-parent and three assembly-parent actual/common consumers. Preserve original namespaces, public types, coefficients, signs and exact dyadic inequalities. Promote only the old private `finite_singleton` helper with identical type/body so the retained common consumer resolves it.

**Verification files:** create `verification/P34PrimaryDyadicAudit.lean` and `verification/verify_p34_primary_dyadic.py`, reusing the unchanged shared verification and complete audit mechanics for the nine-module order in design section 2. Baseline is `2b284342fce23962a1b431d8003cb5cdffac8128`. Bind the new entry point and `docs/part3-distribution/p34-20261126/DYADIC_DECLARATION_MOVES.json` to the source manifest. Record each exact donor block/hash/type and proof repair. Do not modify Task1/Task2 sources, shared verifier logic, dependency pins or original source archives without reporting a concrete necessity to root first.

**Required endpoints:** the original `nonempty_endpoint_bounds`, `short_nonzero_index_eq_one`, `short_mode_mass_eq_beta`, `finite_source_assembly`, `finite_beta_assembly`, `finite_beta_energy_assembly`, `signed_beta_block_eq`, `assembled_short_index_eq_one`, and `assembled_beta_coprime`. No new wrapper or theorem premise is needed.

**Review focus:** preserve the j=0 scale 1/2 and strict-lower/closed-upper convention; retain negative y and the actual beta witness; show computed output keys justify exact beta-energy decomposition with no cardinality loss. The code's U is the output coefficient scale corresponding to manuscript Y. No R(n), oldform identity, common-interval construction or full P3.4 claim follows.

**Acceptance:** implementer may use the fixed local runtime, commit its owned source and run the complete clean nine-module local gate. Root alone publishes and runs P3 cloud acceptance. Existing proof bodies are reused; checking the new nine-module import combination resolves a concrete generated-declaration ownership/composition risk and is not duplicate proof development. Every serialized/private/generated declaration remains covered.

- [ ] Preserve and compare 48 original declaration blocks/types, with the helper visibility change recorded separately.
- [ ] Move only the selected two cores; preserve all eight retained donor consumers and their required imports.
- [ ] Strictly compile and replay the nine-module joint closure, check resolved imports, and audit every serialized declaration against actual ownership and allowed transitive axioms.
- [ ] Independently review exact source/evidence, publish to the current draft PR, and report the finite endpoint scope separately from unresolved original row and spectral suppliers.
