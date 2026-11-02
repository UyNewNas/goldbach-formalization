# T24 independent review: H247 moving mass and old profiles

Review date: 2026-11-02. Reviewer: `/root/t24_review_bank_profiles`.

**Overall: HOLD for literal bank count closure; limited SOURCE-ONLY PASS for the target-N mass/profile suppliers described below.** No compilation, kernel acceptance, finite guard evaluation, numerical replay, or formal credit is implied. `compiled=false`, `kernel_verified=false`, `formal_credit=0`. Broad nodes `P2.9.bank_endpoint_licences` and `P5.6.eight_suppliers` remain OPEN.

The review read the P BRIEF, both PRIOR_TASK files, all four O moving-mass Lean files, all seven O profile Lean files, the O moving-mass report/registry, both complete final P author packets, and relevant M/production/finite-mother suppliers. O profile REPORT/REGISTRY were absent at the initial review snapshot; P now registers those seven frozen sources. The final P review is recorded in section 7. No author file was edited.

Paths below are relative to the repository. Abbreviations:

- `OM/` = `docs/source-only/20261102-resume-30o/h247_moving_mass/`.
- `OP/` = `docs/source-only/20261102-resume-30o/h247_step_profiles/`.
- `M/` = `docs/source-only/20261102-resume-30m/h247_w2_mass_license/`.

## 1. Frozen O scope boundary: W1 physical childWindow is not the O carrier

**O alone: HOLD for literal W1/Buchstab carrier passage. P repair: limited SOURCE-ONLY PASS in the stated true-alpha range; see section 7.** This is not a counterexample to O's stated target-N theorem.

`OP/P2OriginalHalfOpenProfileCarrier.lean:145-168` identifies the filtered actual-prime tuple carrier with `primeWindow N`; `single_window_reindex` at lines 170-188 uses that same window. `OM/P2OriginalPositiveSameQMassLift.lean:80-88` and `OP/P2OriginalProfileThetaNormalization.lean:22-32` likewise enumerate actualPrimeBoxTuples with target N, so primes dividing the prefix d remain present.

The literal W1 source uses a different carrier:

- `docs/source-only/20261028-resume-30e/certificate_enhanced/P2EnhancedActualBuchstabTransfer.lean:25-26`: `childWindow N d Q s t = primeWindow (d*N) ...`.
- `docs/source-only/20261028-resume-30f/certificate_enhanced/P2FrozenReceiverCountActions.lean:67-81`: the exact selected Buchstab identity sums over `primeWindow (d*N)`.
- `docs/source-only/20261028-resume-30g/certificate_enhanced/P2AllW1FrozenReceiverFiniteAction.lean:123-134,145-163`: the actual W1 negative polynomial/count contribution uses that childWindow.

These sets are not equal when a selected prime divides d but not N. The correct repeated-prefix factor `1/p` in O does not establish equality with a source which deletes that prime. O's displayed uniform statements even allow arbitrary d and Q after the threshold. Without a size condition on d this deletion cannot be uniformly declared negligible: at a fixed nonempty window, taking d to be the product of its primes not dividing N deletes the entire window from `primeWindow (d*N)`, while it remains in `primeWindow N`; one may still set `Q=d*N^L`.

The manuscript's actual `alpha=(1-log_N d)/L >= 2` (lines 808-817) provides the relevant prefix-size restriction. A repair must derive and use that restriction, or another already justified exact physical range, to pay the prefix-prime deletion uniformly before positive summation; it must retain the same Q and both endpoint conventions. This is a fillable omitted deduction/interface obligation (difficulty class 2), not evidence here of a substantive manuscript contradiction (class 3). The authors' P repair now implements this deduction and is reviewed in section 7. No new proof code is supplied by this review.

**Do not generalize this mismatch to all W2 occurrences.** The restored W2 source already uses N-windows: `docs/source-only/20261102-resume-30i/w2_feedback/P2W2PhysicalChildFeedback.lean:138-143,179-193` for the three negative singleton windows, lines 226-229 for positive pairs, and lines 293-297 for quotient-prefix words. O's N-window geometry is compatible with these restored W2 carriers. The complete finite reindexing into the exact mother occurrences, selected histories and their remaining costs must still be supplied/identified; O's pair membership statement by itself is not that complete consumer connection.

## 2. Moving L and the actual 70/36 labels

**Limited PASS: actual target-N constant-test mass with compact-uniform L and prefix-independent error.**

- `OM/P2OriginalCompactMovingGateMass.lean:31-55` puts a changed strict gate on a **closed** fixed-center strip. Equality prime atoms are charged.
- Lines 87-111 give the finite weighted arithmetic sandwich; lines 115-128 derive kernel oscillation from compact continuity. Lines 152-202 choose a strip width and a local threshold from actual box/strip estimates. Lines 206-244 take a finite cover and a common threshold. Uniform convergence or equicontinuity is not an assumed target premise.
- `OM/P2OriginalCompactScaledPrimeMass.lean:46-82` reboxes the same actual target-N carrier by a finite sum-subset identity; lines 84-103 identify the dilated region; lines 107-123 clamp only outside the admitted L interval; lines 128-157 give the normalized uniform affine passage.
- `OM/P2OriginalCompactThetaMass.lean:21-51` bounds replacement errors by the fixed floor `N^(Lmin/10)` before L and d are selected. The statement at lines 180-196 chooses one T before N, L, d, all W1 `(Fin 7 x Fin 10)`, all W2 `Fin 36 x Fin 3` singleton labels, and all W2 `Fin 36 x Fin 4` pair labels.
- These are actual bank parameters, not an arbitrary 106-point surrogate: `ImbalancedChen/P5OriginalActionMassBound.lean:228-273` defines the original three plus 33 repaired W2 rows; lines 447-449 define the seven/ten W1 grids; lines 519-523 select actual W2 rows. Their existing finite geometry proof bodies were read, **not executed**.

The residual-kernel denominator is valid on the supplied domains. `OP/P2OriginalHalfOpenProfileCarrier.lean:86-107` retains `2v<1`, `2u+v<1` and residual floor on the half-open domains. The excluded part of D5 is not included in its `pairHalf` definition (lines 27-31). This is the good ordinary feedback geometry, not a bound on the excluded positive switching cost.

## 3. Prefix repetitions, same Q, positive sigma and zero mass

**Limited PASS on the carrier actually stated.**

`M/P2OriginalChildPhysicalNormalization.lean:19-20` uses `1/p` if p divides d and `1/(p-2)` otherwise. The pair factor at lines 46-55 is sequential, with second prefix `d*p`. `OP/P2OriginalPhysicalOldProfileMass.lean:20-27` preserves these factors; lines 37-79 and 113-164 pay their replacement uniformly in the complete prefix. Neither coprimality to d nor squarefreeness of d is silently imposed. `OP/P2OriginalHalfOpenProfileCarrier.lean:261-265` retains labelled multiplicities rather than collapsing equal child products.

`OM/P2OriginalPositiveSameQMassLift.lean:119-151,153-182,184-222` places the threshold before Q, finite support, nonnegative sigma, moving residual assignment and action assignment. Exact child-Theta identities at lines 90-102 use the same Q. Lines 105-115 identify the total with the manuscript Theta using `M/P2OriginalChildPhysicalNormalization.lean:26-33`. The positivity proof at OM lines 32-43 is from primitive d positivity, `Q/d>1` and `N>=4`; it does not assume positive total mass. Lines 226-229 prove the zero-total equality from the absolute estimate.

The profile composition is genuinely a child-Theta sum: `OP/P2OriginalProfileThetaNormalization.lean:34-92` derives the pointwise identities from the actual M singleton/pair normalization; lines 94-125 assemble W1 and W2; lines 129-179 lift arbitrary finite labelled nonnegative sigma with one Q. The denominator is the literal sum of sigma times thetaAtom. Its equality with manuscript Theta is immediate in the injective-prefix/natural-index presentation via the existing M identity; for general labels the sum preserves repeated histories explicitly. No division by this sum occurs. Zero mass follows from the same absolute algebra.

Qualification: the final labelled profile theorem chooses each displayed action uniformly across labels, after the threshold. The underlying local uniform theorem is strong enough for label-dependent selection, but no final label-dependent action/Theta profile theorem is written there. No such final API is credited by this review.

## 4. Half-open endpoints, closed knot minima and original profile kernels

**Limited PASS: endpoint payment is arithmetic, not merely real nullity.**

- `OP/P2OriginalHalfOpenProfileCarrier.lean:25-37,39-76` uses inclusive lower/strict upper windows and exposes the lower-wall remainder exactly. Lines 298-345 keep that remainder as an explicit weighted finite sum.
- The same file's lines 267-294 expand all 401 arithmetic atoms. The underlying data convention is read from `ImbalancedChen/Part5OriginalUpsilon5FloorKernel.lean:26-45`: 200 open cells, 201 knot atoms, adjacent closed-cell minimum at interior knots, grid `1+i/50`. `ImbalancedChen/P5OriginalFeedbackTableKernels.lean:21-28` uses h on [2,5] and H on [1,5].
- `OP/P2OriginalClosedCellProfileAtoms.lean:96-173` encodes both support and profile comparisons, including knots as opposite weak affine gates. The knot's strict interior is empty, but its arithmetic atom remains in the sandwich. Lines 181-244 supply the proper-wall/positive-denominator passage; the concrete profile forms in `OP/P2OriginalOldProfilePrimeLimits.lean:149-194` retain `s0*(1-u-v)` or `(1-u-v)/u` as appropriate and prove nonzero walls.
- `OP/P2OriginalAffineProfilePassage.lean:54-98` majorizes the **actual prime-sum** difference by the wall majorant before taking limits. Lines 104-159 choose the majorant and target threshold and pay it using O's moving-L theorem. Therefore real nullity at lines 27-42 is not being used as a substitute for arithmetic endpoint control.
- `OP/P2OriginalOldProfilePrimeLimits.lean:79-121` chooses a common threshold across all finitely many profile atoms and handles signed old arrays without dividing by an atom mass. `OP/P2OriginalPhysicalOldProfileMass.lean:176-219` identifies the original one/two-dimensional integrals.
- `OP/P2OriginalBankOldProfilePassage.lean:110-128` contains one W1 half factor, one W2 division by five, W2 coefficients 4 and 1, exactly three singleton and four good pair occurrences. The corresponding common-action passage is lines 148-188. Old arrays are fixed before T and are never replaced by a newly generated table in these proofs.

## 5. True alpha, ceilings, below-two use, and what remains unproved

**PASS for the stated local identities; HOLD for their complete physical/count instantiation.**

`OP/P2OriginalHalfOpenProfileCarrier.lean:348-360` transports the true child alpha symbolically, without resetting it to 2. Lines 364-379 prove the added-prime ceiling under an explicit physical ceiling assumption. Lines 397-421 use only finite cutoff antitonicity below two and preserve the full `A(w)-A(v)` correction. The hypothesis `hv` at lines 411-412 is a clearly separate old scalar licence at v, not a proof of that licence and not an assumed whole feedback theorem.

The terminal profile-Theta theorem does not contain beta, alpha>=2, the receiver predicate E, old selected-square predicates, or the physical ceiling chi. Their algebraic/local lemmas are not a proof that every actual marked history satisfies those conditions. The following remain OPEN:

1. For O alone, the W1/Buchstab prefix-deletion/actual-range connection in section 1. P now supplies the W1 profile-mass repair under true alpha>=2; arbitrary unbounded prefixes remain outside that repair. An extension to other Buchstab tests must explicitly instantiate the proved bounded-test supplier rather than merely rename its conclusion.
2. Exact assembly into the immutable original child occurrences, including all existing selected-history tests and any literal quotient-word reindexing still needed. The W2 restored N-windows must be distinguished from W1's dN-window.
3. Actual old-generation ordinary upper/lower count licences at the transported alpha, correct cutoff and same Q, including the justified below-two comparison. No H247 licence, upper endpoint or bank endpoint package is proved here.
4. The ordinary and positive-switching bases, excluded D5 cost, longer quotient words/collisions, retained unit surfaces and all other positive-product source costs. The reviewed files do not claim to close these.
5. Installation and compilation of the complete pinned dependency chain. These are uncompiled source proofs; API/tactic elaboration (difficulty class 1) has not been tested.

Manuscript alignment: lines 795-806 govern nonnegative finite sigma and one Theta_Q; 808-817 govern true residual/alpha, same Q and physical geometry; 823-855 govern the 70/36 bank and good domains; 857-865 govern old generations and closed minima. The manuscript SHA256 was checked as `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.

## 6. Static checks and reviewed bytes

The four OM source hashes match their O registry. All eleven reviewed O Lean files were searched for `sorry`, `admit`, new `axiom`, and endpoint/count-licence names. No admission or new axiom was found; relevant count-licence mentions in O are scope disclaimers, except the explicitly local below-two transfer premise discussed above. This is a text inspection, not an axiom audit from a kernel.

| O file | SHA256 |
|---|---|
| OM/P2OriginalCompactMovingGateMass.lean | f43f08a1de9e26222a66c89f4cdc8cb09bafafafdfd75304522cd4d6ca5830c6 |
| OM/P2OriginalCompactScaledPrimeMass.lean | f032298682ea0cea88809875b51e94e62bdcd59bee93fc79ab8f8a6afaf53b55 |
| OM/P2OriginalCompactThetaMass.lean | e8013e86b56748b7698bd4b0b365771a5d3bda9269346aeaa13b4801ae397ea9 |
| OM/P2OriginalPositiveSameQMassLift.lean | bec25f9fdca24ffaba071b8f49aaeb3a21fec454f3088543f04f9b1544a6e565 |
| OP/P2OriginalAffineProfilePassage.lean | 4a0b07c88de9999d5b54970ecf48f61bd79b6773d1a627cafae330fb8f5f2013 |
| OP/P2OriginalBankOldProfilePassage.lean | 1b3b1b30f10d4f2be62d71f887ba8a0e429f0260b0e31c971b21a5d5ea9374b5 |
| OP/P2OriginalClosedCellProfileAtoms.lean | 0bff036c3e3d32ecf3ec603d96f4a6017de6040de3b353109ecdcec85c44a454 |
| OP/P2OriginalHalfOpenProfileCarrier.lean | b03c234d28e28919745f5453cb23c672e6a6ce5c3b90777b3ecb26d93c820484 |
| OP/P2OriginalOldProfilePrimeLimits.lean | c0f8ee2657e3273aac0b8a040035b858a0623421a955b574e7511aaf7a6581dd |
| OP/P2OriginalPhysicalOldProfileMass.lean | 51019ee726f56172ee51d0fc3a15638d3b40d2ba2f0d4899f3f11d72b3d166dc |
| OP/P2OriginalProfileThetaNormalization.lean | b631e89aae44aed088dbc65303cf5b161a42eb711ffc533171c5b0bbbb12b7a7 |

No Lean/lake/compiler, CI, finite guard, numerical producer/search/replay or Git command was run. Only source/metadata/hash reads and this report write were performed. No child agent was created.

## 7. P packet follow-up: the W1 mask gap is repaired at source level

**Limited SOURCE-ONLY PASS for the two-file P repair, conditional only on its stated primitive range and existing source dependencies.** The proof bodies were read independently. They do not assume uniform prefix-deletion, a profile limit, or an old H247 count licence as a new premise. The exact reused removal theorem was also read at `ImbalancedChen/ChenPrimeHarmonicFinite.lean:107-135`.

`docs/source-only/20261102-resume-30p/h247_moving_mass/P2OriginalPrefixMaskMass.lean` supplies:

- Lines 26-36: the exact finite filter identity `primeWindow(d*N)=primeWindow N.filter (not p|d)`, with unchanged half-open endpoints.
- Lines 40-60: on a deleted lane, `localPrimeFactor d p=1/p`; the signed bounded-test error is at most `(C/A)*(log d/log 2)`, using the actual distinct-prime-count removal bound.
- Lines 66-97: with `0<d<=N` and `A>=N^a` for fixed `a>0`, the threshold precedes d, both window endpoints, and every signed bounded test. The convergence supplier is the existing `log N/N^a` limit.
- Lines 110-127: moving L and every original W1 lower endpoint `lo>=1/5` inherit the fixed floor `N^(Lmin/5)`. No W2 restored window is subjected to this extra deletion.

`docs/source-only/20261102-resume-30p/h247_step_profiles/P2OriginalLiteralW1OldProfile.lean` supplies:

- `prefix_le_target_of_true_alpha` (lines 28-41): the original alpha>=2 hypothesis yields d<=N by positive L and monotonicity of log. This is an explicit physical restriction, not an inference from O's arbitrary-prefix mass estimate.
- `true_single_eq_N_window`, `maskedSingleOldProfile`, `maskedW1OldProfile` (lines 44-75): reindex the actual O singleton sum first, then define the different dN mask with the same inherited old-profile test.
- `all70_masked_old_profile_passage` (lines 99-134): apply the signed deletion supplier to the proved bound `10*floorBound oldh`, combine it with the existing O old-profile passage, and retain the single W1 factor 1/2 and parent H atom.
- `literalW1ThetaOldProfile_eq` (lines 138-187): identify the literal original `childWindow N d Q` with the masked physical-power window, retain `log p/log(Q/d)`, and use exact child thetaAtom normalization at the same Q.
- `all70_literal_sameQ_Theta_profile_passage` (lines 192-232): choose one threshold before Q and the arbitrary labelled nonnegative family, use true alpha for each actual prefix, and conclude an absolute error bounded by epsilon times the literal labelled parent-Theta mass. Zero total mass again involves no division.

This genuinely eliminates the W1 profile-mass mask obligation isolated in section 1. It does **not** prove old-generation count licences, a bound for arbitrary receiver predicates, the full H247 recurrence/count induction, or the remaining W2 switched costs. The local PASS therefore leaves the overall count-closure verdict HOLD.

Both final P reports accurately retain OPEN, uncompiled, zero-credit status and the source/count boundary. The moving-mass registry's 18 encountered path/hash records were checked with no mismatch (including repeated pins and provenance). The profile registry's 72 encountered path/hash records likewise matched; its one new and seven reused profile source entries all matched their byte count, line count, direct imports and declared starting lines. Registry JSON parsed successfully. The new sources contain no `sorry`, `admit` or new `axiom`. The profile registry explicitly says its import audit is narrow rather than a certified complete transitive build closure (line 1698); the unresolved W2 evidence-only transitive import at lines 1389-1393 is not promoted to installed/kernel status.

Final pinned P snapshot:

| P packet item | SHA256 |
|---|---|
| h247_moving_mass/P2OriginalPrefixMaskMass.lean (130 lines) | 12717d05bc4ba7c92679f37eaefec969f0c7f263a38284019f64c547a21fdf49 |
| h247_moving_mass/REPORT.md | d2122afddb6b0e7285d753c2f0629e2627b464d00d635cfd8c4fe162ce314ac9 |
| h247_moving_mass/REGISTRY.json | af295ba84a4b7f5591c6c92a13d5127c8f459e3d257d851bf5cd7cc7c0c8bce0 |
| h247_step_profiles/P2OriginalLiteralW1OldProfile.lean (235 lines) | 4a55a30209362e327d91be162b305dee7990aec24d9ad46f78267f1d27968fe9 |
| h247_step_profiles/REPORT.md | a65110b49c97d3344ee0d0cdf85d7f4e9b06ce23bddf22e1feba4fbfd29ae0f8 |
| h247_step_profiles/REGISTRY.json | 02251ac7e896b71e4692181f2e91d7c08ff7cb27c96bb30cdb0e405d93d536f8 |

Final verdict: limited SOURCE-ONLY PASS for O's moving-L/half-open/closed-knot/Theta mass suppliers and P's physical-alpha literal W1 mask composition; HOLD for full bank count closure and both broad yellow nodes. No unresolved mathematical defect in the two P proof bodies was found by this static review, but no elaboration or kernel verification was performed.
