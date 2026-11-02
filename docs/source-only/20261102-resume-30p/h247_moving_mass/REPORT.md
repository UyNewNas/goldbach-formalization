# P / h247_moving_mass — original W1 prefix-mask bridge

Status: **SOURCE ONLY; OPEN; compiled=false; kernel_verified=false; formal_credit=0**.
All numerical and finite-guard proof bodies remain UNEVALUATED. One new Lean file supplies a missing finite carrier conversion. The O moving-L masses and positive-sigma lift are reused without replacement or modification.

## Manuscript and difficulty

The original manuscript `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, was read at 795–855. Lines 795–806 require a finite nonnegative marked family and one Q; 808–817 retain the actual residual, alpha, squares and physical ceiling; 823–850 specify the 70/36 original actions and their singleton/pair gates; 851–855 preserve the excluded-pair cost and switching unit surfaces. The source note `global-chen-lower-completion-20261010.txt:173–237` was also read.

The newly repaired difficulty is **(2) a fillable omitted finite deduction**, with **(1) Lean/API acceptance still unverified**. It is not evidence of a substantive mathematical gap: a logarithmic distinct-prime count pays the omitted mask. No category-(3) manuscript defect is asserted.

The precise boundary is visible in existing source:

- `docs/source-only/20261028-resume-30e/certificate_enhanced/P2EnhancedActualBuchstabTransfer.lean:25`, `childWindow`, uses `primeWindow (d*N)`.
- `docs/source-only/20261102-resume-30h/certificate_enhanced/P2AllW1StablePrefixRawInduction.lean:69`, `markedOldW1Children`, uses that same W1 child window and its actual old lower child.
- `docs/source-only/20261102-resume-30o/h247_step_profiles/P2OriginalHalfOpenProfileCarrier.lean:145`, `single_carrier_membership`, identifies the O carrier with `primeWindow N`.
- O's `localPrimeFactor d p` is correctly `1/p` when p divides d. Correctly computing that lane does not make its deletion from the original W1 count window automatic.

The additional prefix restriction is deliberately **not** imposed on W2: `docs/source-only/20261102-resume-30i/w2_feedback/P2W2PhysicalChildFeedback.lean:138`, `negativeWindow`, already uses `primeWindow N`; `negativeWindow_eq_old_children:168` and `all36_negative_children:179` identify the restored original lower-child terms with those N-masked windows. W2's repeated-prefix lanes must remain.

## Exact reuse; no repeated implementation

All four frozen O files were read. Their hashes were recomputed and agree with O's registry:

| O source | SHA256 | Reused declarations |
| --- | --- | --- |
| `P2OriginalCompactMovingGateMass.lean` | `f43f08a1de9e26222a66c89f4cdc8cb09bafafafdfd75304522cd4d6ca5830c6` | `moving_gate_sum_sandwich:87`, `compact_uniform_affine_gates:206` |
| `P2OriginalCompactScaledPrimeMass.lean` | `f032298682ea0cea88809875b51e94e62bdcd59bee93fc79ab8f8a6afaf53b55` | `scaledPrimeSum_eq_ambient:46`, `compact_uniform_scaled_affine:128` |
| `P2OriginalCompactThetaMass.lean` | `e8013e86b56748b7698bd4b0b365771a5d3bda9269346aeaa13b4801ae397ea9` | `compact_multiplier_error:21`, `all70_compact_uniform_single_mass:116`, `all36_compact_uniform_singleton_mass:139`, `all36_compact_uniform_pair_mass:164`, `bank_compact_uniform_masses:180` |
| `P2OriginalPositiveSameQMassLift.lean` | `bec25f9fdca24ffaba071b8f49aaeb3a21fec454f3088543f04f9b1544a6e565` | `finite_nonnegative_absolute_lift:21`, `singleChildTheta_eq:90`, `pairChildTheta_eq:97`, all three `all*_positive_sameQ_*_lift` at 119/153/184, `zero_mass_absolute:226` |

These filenames all reside in `docs/source-only/20261102-resume-30o/h247_moving_mass/`. All short declaration names in this report are qualified by the corresponding `ImbalancedChen.<filename-stem>` namespace. O's registry continues to own the complete inherited installation/import inventory.

The original action indices need no new encoding. Production `ImbalancedChen/P5OriginalActionMassBound.lean:447–449` defines W1 with `Fin 7 × Fin 10`; `originalW2At:519` is the exact indexed lookup in the original repaired list; `Original106Action:525` is `(Fin 7 × Fin 10) ⊕ Fin 36`. O uses these same types and lookup, including all 36×3 singleton and 36×4 good-pair domains. No new enumeration, flattened substitute, or finite bank guard was produced or evaluated.

Repeated **labels with the same prefix** also need no new grouping code for a fixed original action. Existing K source `docs/source-only/20261102-resume-30k/bank_h247/P2OriginalW2CentreThetaPayment.lean`, SHA256 `ca1c644dd724497d054f68d31bdeafdd4227507dce01aec9f4c422dce7d77b39`, already provides `groupedSigma:193`, `weighted_fiber_sum:196`, and `Theta_grouped:217`. It adds coincident-prefix weights, preserving multiplicity and the true normalizer. O's generic finite lift also permits arbitrary labelled support directly. O/profiles `P2OriginalProfileThetaNormalization.all106_sameQ_Theta_profile_passage:129` keeps an arbitrary label type and prefix map for each fixed original action. None of these statements permits grouping labels whose non-prefix data differ; no such invalid grouping is used. The manuscript's finite alternatives are not summed.

The zero-mass conversion is exactly O's `zero_mass_absolute`. Its premise is the already supplied absolute estimate, and it proves equality without normalizing by Theta. No new zero-mass wrapper is warranted.

## New source and actual eliminated obligations

`P2OriginalPrefixMaskMass.lean`, SHA256 `12717d05bc4ba7c92679f37eaefec969f0c7f263a38284019f64c547a21fdf49`, intended module `ImbalancedChen.P2OriginalPrefixMaskMass`, contains five declarations:

1. `primeWindow_prefixMask:26`: exact `[A,U)` carrier identity `primeWindow(d*N) = (primeWindow N).filter (not dividing d)`.
2. `primeWindow_prefixMask_difference_le:40`: for an arbitrary signed test bounded in absolute value by C on that literal window, the exact local-multiplier sum changes by at most `(C/A)*(log d/log 2)`. It uses the production `chen_prime_centre_removal_bound:107` and the actual repeated lane `localPrimeFactor d p=1/p`.
3. `compact_uniform_prefixMask_difference:66`: for fixed a>0, C≥0 and epsilon>0, one threshold precedes N, every positive d≤N, every A≥N^a, every upper endpoint U, and every such signed test. The proof uses the existing `tendsto_nat_log_pow_div_rpow:40`, with k=1, rather than assuming a deletion limit.
4. `prefix_le_target_of_commonQ:101`: Q≤N and Q/d>1 imply d≤N, a sufficient physical route to the needed prefix bound.
5. `compact_uniform_moving_prefixMask_difference:110`: the same absolute error for every moving L≥Lmin and lower normalized endpoint lo≥1/5. In particular it covers all 70 original W1 lower endpoints, with one threshold before labels, L and both windows.

This pays the actual W1 prefix-mask deletion, including signed and discontinuous step-profile tests. It does not replay O's convergence argument, change local factors, alter Q, require Theta>0, assume a count licence, or add an H247 consumer.

The condition d≤N is explicit and essential to this supplied bound. It is not a consequence of O's arbitrary-d mass theorem. In the manuscript's physical class it also follows from N>1, L>0 and `(1-log_N d)/L≥2`; task 9 owns that exact physical-alpha deduction and the literal old-profile composition. This packet does not add Q≤N to the original theorem as an assumed universal manuscript constraint.

## Remaining and peer interface

The broad nodes `P2.9.bank_endpoint_licences` and `P5.6.eight_suppliers` remain **OPEN**. Installation and compilation of O/M and the new file remain necessary. No ordinary child-count asymptotic, prior-generation H/h licence, seed licence, switched base, full 248/430 recurrence, or upper-supplier theorem is proved here. Half-open endpoint atoms and the W2 good-pair dictionary remain with the existing profile chain; an equality between every literal raw pair count carrier and its profile tuple sum is not claimed by this packet.

Task 9 received the stable bounded-signed-test API and source hash, and is composing it with O's existing singleton reindexing, old-profile limit, physical alpha and same-Q Theta identities. Task 24 independently read all 130 lines and the exact production distinct-prime-count API, reporting a source-only static pass for the filter, repeated lane, error bound and common-threshold logic; this is not compilation acceptance. Peer output is not treated as an assumed theorem in this source.

Only the assigned P directory was written. Static checks consisted of textual source/API inspection, declaration/import scanning and raw SHA256/byte/line checks. No Lean/lake/compiler/build/CI, finite-guard evaluation, numerical replay/producer/search, Git command, old/production/peer edit, or child agent was used.
