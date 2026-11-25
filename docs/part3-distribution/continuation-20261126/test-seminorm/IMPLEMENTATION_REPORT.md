# P3.5 actual per-mode test seminorm

Draft ready for targeted compilation. No gate evidence at the time of this report.

## Owned sources

| File | Draft SHA-256 | Declarations |
| --- | --- | --- |
| ImbalancedChen/Part3ActualSpectralTestJets.lean | 1df7b6e801a222c524f84ee5f246f6f5efb6e7f89d8346c9aa922c7f4d30f85c | 20 |
| ImbalancedChen/Part3ActualSpectralTestSeminorm.lean | 2d3407eb356b62ce75c5cd6edaa076015c2c98b076915a99556e4b95cf809252 | 13 |

## Historical reuse

Donor commit `52098e403ac4b28c72ec5958fd738ae93d785ac5`. The selected text matches the donor commit's blob bytes for all six ranges, up to trailing blank lines. The public names and namespaces are preserved.

| Donor | Blob | Lines | Content |
| --- | --- | --- | --- |
| 30m/exceptional_j_large_scale/Part3ActualExceptionalJLargeTransform.lean | 43fe6493d1a4c90a252ed163aa14572ebe9e44ad | 33–34, 50–63, 136–142 | Frequency, phase derivative, frequency norm |
| 30r/full_modulus_test_support/Part3OriginalFullModulusTestJets.lean | d4ce9301a7c98f117937e614ca29577c09e98d19 | 47–54, 101–257 | Support of iterated derivatives, fixed-cutoff and test derivatives and bounds |
| 30s/S/s22_actual_spectral_energy/Part3OriginalUniformTestCutoffBudget.lean | 4ed252e2956690d46848cb14b4f8253a88050610 | 74–81 | Finite constant and positivity |

These are the directories below `docs/source-only/20261102-resume-`. The supplier includes the previously documented `open scoped ContDiff` syntax repair from `docs/source-only/20261112-resume/t03/abel-lift-next/TEST_JETS_SCOPE.patch`. Its project imports are Part3NativePeriod64Reconstruction and Part3ActualWeightedSpectralBudget. Its mathlib imports are Analysis.Calculus.Deriv.Support and Analysis.Calculus.IteratedDeriv.Lemmas. Source extraction gives no whole-historical-module validation.

## Declaration inventory

All namespaces below have prefix `ImbalancedChen.Part3`.

- `ActualExceptionalJLargeTransform20261102` — modeFrequency, phase_hasDerivAt, modeFrequency_norm_le.
- `OriginalFullModulusTestJets20261102` — iteratedDeriv_tsupport_subset (private), complexChi, nativePhase, complexChi_contDiff, nativePhase_contDiff, nativePhase_iteratedDeriv, spectralMode_iteratedDeriv, spectralTest_iteratedDeriv, complexChi_tsupport (private), exists_cutoffJetBound, cutoffJetBound, cutoffJetBound_pos, cutoffJetBound_bound, testJetConstant, testJetConstant_pos, spectralMode_jet_bound, spectralTest_jet_bound.
- `OriginalUniformTestCutoffBudget20261102` — finiteTestJetConstant, finiteTestJetConstant_pos.
- `ActualSpectralTestSeminorm` — normalizedJetSup, normalizedJetRange_nonempty, normalizedJet_le (private), normalizedJetRange_bddAbove, le_normalizedJetSup, normalizedJetSup_nonneg, normalizedJetSup_le, testSeminorm, testSeminorm_nonneg, testSeminorm_le, actual_uniform_testSeminorm_budget.

## Mathematical scope

This supplies the omitted manuscript derivation in which each fixed order and each period-64 mode has its own supremum over the real test variable (analytic appendix 705–717 and the regular-weights application at 757–776, per the frozen manuscript audit). The range has the witness q=0 for all Y. For positive Y, multiplying the donor jet bound by Y^n supplies the upper bound on the range. Conditional completeness gives domination at each q and the upper bound on the supremum. Nonnegativity follows by the q=0 witness. Monotonicity of the polynomial weight pays for all n≤d with one degree-d weight. For fixed d the constant is finiteTestJetConstant d times the witness of actual_uniform_weighted_l1 d. Positive rho is unnecessary; rho=0 is included. The theorem takes |sigma|≤1 and Y>0 and outputs both summability and the actual weighted bound. It introduces no hypotheses on test derivatives, weights, convergence, or external trace formulae.

The result supplies a test seminorm budget. Comparison of actual kernel transforms with external Bessel estimates, norm constants, and physical-row ownership stays beyond its mathematical conclusion.

## Checks and diagnostics

Both files passed whitespace and forbidden-token scans. Exact donor slices, Git blobs and definition-level agreement of actualCoeff/testWeight/actualW with the accepted weighted L1 source were inspected. The initial draft only adapts imports and namespace opening around donor declarations, without editing their proofs. Compiled declaration types, axiom inventories, kernel replay and acceptance remain with the controller. No compile diagnostic had arrived when the draft was handed off.

## P3 diagnostic f3933565759045ffb50313d6f2b73e7f

The targeted build failed during elaboration of the extracted supplier. It did not reach the seminorm module. The frozen appendix's Fourier separation and derivative-cost lines 705–717 and the use at 757–776 still give the same per-mode derivation. These diagnostics concern Lean names, parsing and coercion simplification.

| Supplier declaration | Initial diagnostic | Repair in the next candidate |
| --- | --- | --- |
| phase_hasDerivAt, nativePhase, nativePhase_contDiff | The short name e also resolved to a bounded-continuous-function declaration. | Qualify all occurrences in these declarations with P3Period64NativeReconstructionSourceOnly. Remove the redundant short-name imports. |
| phase_hasDerivAt | Conversion of the derivative left id t and the complex coercion of real one. | Simplify with the phase identity at t, id_eq, Complex.ofReal_one, mul_one and mul_comm. |
| modeFrequency_norm_le | abs_ofNat is unknown on the pinned dependency version. | Use abs_of_pos with a norm_num proof of positivity of the real numeral 64. |
| exists_cutoffJetBound | The field notation following the typed ball/interval compactness expression on a new line parsed as a separate dotted identifier. | Introduce hcompact for the closed interval and apply hcompact.exists_bound_of_continuousOn to hc.continuousOn. |

Cascading diagnostic placeholders occurred in the failed elaboration. Source scans find zero proof escapes. This revision changes the Jets SHA-256 to a809dcf39b61cc6b7eec04dba86b29e15a2da25367c5d44c9cbc414c1d2b97f8; Seminorm retains its initial SHA-256. The mathematical assertions, their selected declarations, and proof strategy are preserved. Whitespace and forbidden-token checks passed; compilation of this revision is pending.

## P3 diagnostic e475c0248bad453da0910b0f83da18b0

Two errors remained in Jets. The cutoff boundedness proof and replacement for abs_ofNat no longer produced errors. The phase derivative conversion let the simplifier commute the argument before it matched the native-phase equality. The revision now applies rw [he t] first, simplifies id_eq and the coercion of one, and proves the final product equality by mul_comm. The nativePhase_contDiff proof's fun_prop search lacked the coercion rule for Complex.ofReal. It now uses the real-linear-input, complex-coercion, constant-product and exponential composition proof already present in the accepted spectralMode_contDiff (ImbalancedChen/Part3NativePeriod64Reconstruction.lean, 372–376). The formula and all order and parameter requirements stay the same. New Jets SHA-256 is 2e582af63a626283ee492189dd293a0ca3f64808c49fbb9da88246940df582df. This is a candidate for repeat compilation.
