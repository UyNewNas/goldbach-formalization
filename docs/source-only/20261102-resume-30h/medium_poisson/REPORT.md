# H medium_poisson: actual non-Hermitian product-source polarization

The local source step is written in three Lean modules. It supplies the missing normalized non-Hermitian coefficient expansion and its exact cost at the actual original product-cutoff source. The complete medium_poisson task remains open. `local_step_complete=true`, `task_complete=false`, `compiled=false`, `kernel_verified=false`, and `formal_credit=0`. Independent review is pending; nothing has been installed or compiled.

The selected TASKS assignment is `gpt-6-astra`, `xhigh`; runtime was inherited from the parent. No child agents were started.

## Original obligation and predecessor boundary

The authoritative manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, raw SHA `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines 197–210 retain the second CRT phase and prescribe five-coordinate partial summation followed by coprime partition and polarization. The detailed module `distribution-medium-completion-20261010.txt`, raw SHA `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`, lines 299–321 fixes:

- the denominator `q*w1*w2` and the outside division by the original preliminary `d`;
- both independent `st=d` choices in the two Lambda factors;
- two product-window upper differences;
- ordered non-Hermitian polarization of the two R, two S and two n coefficient families at cost at most `4^3`;
- a single signed h interval and no new SW use after polarization.

I read the current production `ImbalancedChen/Part3DistributionTargets.lean`, raw SHA `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc`, the actual held `FixedBlock` and factor-choice definitions, all four G medium_poisson modules, and F's independent `reviews/medium.md`. F had actual independent Lambda expansion and exact source/Abel identities. G had the tight real-H caller, amplitude envelope, product-window differences and actual finite prefix/variation cost. Neither had the actual normalized polarization consumer implemented here. No old production/source pins were assumed to match without reading and hashing the selected paths.

## Mathematical content and actual caller

For fourth roots `xi = 1,i,-1,-i`, define the coefficient function

`D_xi(a,b)(n) = (a(n) + xi*b(n))/2`.

The first module proves the ordered identity

`a(m)*conj(b(n)) = sum_xi xi*D_xi(a,b)(m)*conj(D_xi(a,b)(n))`.

No symmetry of the kernel is used: the reverse cross term cancels independently. Iterating in three pairs gives the explicit 64-term identity `three_pairs`; `packetWeight_total_mass` proves that the sum of absolute coefficient weights is exactly 64. Every diagonal function is one-bounded when its two original functions are one-bounded.

The second module uses the actual coefficients `gamma2(u*s)`, `gamma3(v*t)` and `alpha(n)`. Their original factor/alpha support indicators are retained in `gamma2Slot`, `gamma3Slot` and `alphaSlot`. `actual_slots_one_bounded` derives their bounds from the unchanged current `MediumAdmissible` conjunction. No bound outside those supports is assumed. At each real source choice, the support indicators equal one; `actual_choice_three_pairs` proves the exact expansion of the independent original choice coefficients.

`actualUpperRectangle_eq_packets` applies this expansion to each of G's actual `productUpperPayload` branches. It keeps the actual clean carrier and rectangle, original inverse phase, both independent rough product fibres, both smooth choices, and both upper cutoffs. The physical kernel is literally

`B.firstPhase t / (t.q*t.w1*t.w2)`.

`norm_physicalKernel` proves its norm is exactly `1/(q*w1*w2)`. There is no extra d, Q, M, retained-phase factor or spectral parameter in this charge. The four roots are algebraic polarization parameters; they are not a proposed four-chart phase cover.

The direct original consumer is

`OriginalActualPolarizedProductCaller20261102.actual_rectangleSum_norm_le_four_kernelMass`.

Its left side is the independently defined

`(poissonAtlasBlock atom z y k hA Csep j small hd negative).rectangleSum R`.

Its exact source identity, `actual_rectangleSum_eq_four_upper`, follows from the existing G product-window theorem and current `FixedBlock.coeff`; it does not accept a source-binding hypothesis. The reusable upper-source lemma's `B.atom = atom` field is discharged by `rfl` at this actual caller. The `q` label is never changed to `q*d`, the h carrier is unchanged, and no `H >= 1` assumption is added. Empty original carriers, including H<1, therefore remain empty throughout these finite sums.

The proved quantitative bound is

`norm(rectangleSum) <= 64*(M_UU + M_LU + M_UL + M_LL)`,

where each `M_AB` is explicitly the sum, on that actual gated carrier, of

`card(productFibre(w1))*card(productFibre(w2))/(q*w1*w2)`.

All four original upper/lower combinations and their source signs appear in the exact identity before the norm. This is the native absolute counting envelope and exact polarization coefficient cost. It is not an arbitrary-log saving, a power-saving bound, a coefficient-prefix spectral estimate or the manuscript bare bound. No such estimate is a premise.

The third module removes a potential ambiguity in interpreting the diagonal sums. It defines `smoothLabels` as the image of the actual product-unrestricted choice set, independent of q,n,h and the current rough product. `actualUpperPacket_eq_frozen` proves an exhaustive disjoint regrouping over two independent such labels. `mem_smoothLabels_original_data` proves each label's own `st=d` and both original y trims. On each `frozenUpperPacket`, the two gamma2 profiles use fixed s,s', the two gamma3 profiles use fixed t,t', and the same diagonal function is evaluated at its two rough arguments. `actualUpperRectangle_eq_frozen_packets` connects this fixed-coefficient expansion to the preceding source; `frozenUpperPacket_norm_le` supplies its explicit native kernel counting envelope.

The current uncolored source has equal alpha profiles on the two sides. The general three-pair algebra allows different n profiles, but the actual post-coloring dictionary and its masks are still an open connection. This delivery does not assert full colored spectral packet coverage.

## Preserved hypotheses and remaining obligations

The actual caller uses the original `MediumAdmissible b sigma kappa c0 atom`, source key k, `small in activeD atom k`, q piece `j : Fin 3`, h sign, Csep and arbitrary original rectangle. The finite source identities hold for arbitrary z,y. Returning to the original inclusive numerical cutoff still uses the predecessor's z>=0 and y=roughY(x) bridge; no untrimmed Lambda=lambdaTrim assertion was added.

The following remain internal work:

- actual coprime-coloring coverage, its fixed coefficient masks and its subpower number of classes;
- total smooth-label/divisor multiplicity payments beyond the exact retained finite fibres;
- the full five-coordinate weight5 finite-variation/FTC estimate and one common `x^(5*kappa+o(1))` debit;
- cancellation in the actual frozen diagonal packets and the D0/D1/D2 regular/exceptional spectral return, with a common completed interval and additive phase;
- general-D/nonclean canonical root/inverse transport and its costs;
- all remaining genuine single-zero, gcd/close-pair, restoration and omitted-lattice payments, and the original weighted S1−2Re(S2)+S3 assembly.

No new external input is used by these local algebraic/counting proofs. The named classical coloring/spectral inputs remain upstream obligations with their original precise scopes. Internal P1/P2, K, PP or the final medium theorem have not been promoted to external premises. No new manuscript contradiction was found.

## Exact sources, installation and static scope

Only `docs/source-only/20261102-resume-30h/medium_poisson` was written. Production and A–G were read-only. No Lean, lake, compiler, build, CI, numerical or finite-certificate replay, functional decision execution, quota check or subagent was used. The static work was mathematical/source inspection and a read-only text/import/hash inventory. A text search found no `sorry`, `admit` or `axiom` token in the three Lean files. This is not elaboration or kernel verification.

Install order, when the user chooses to integrate, is the order below, each under the corresponding `ImbalancedChen/` filename. Exact current imports, source hashes, module names and inherited manifest paths are in REGISTRY. The old source-only import chain is not claimed to be a fully validated recursive build closure.

| Source | Lines | Raw SHA-256 |
|---|---:|---|
| Part3OriginalActualThreePairPolarization.lean | 158 | `2bce5688ccbaa6205ce6cfa2d91a951b2c58a353d4f3f6400b36368414a4d050` |
| Part3OriginalActualPolarizedProductCaller.lean | 350 | `22e955705e408e592e4afaa5b2b5f6b3055182b06fa31361eb798d130591362f` |
| Part3OriginalActualFrozenSmoothPackets.lean | 177 | `7c7e31d3da60489beb877c31848fb572bab5389720a4657757c935b163ae9d2e` |

REGISTRY raw SHA-256: `1b73a68f229c05b1f0c7b9ee9dbbc5927176742c03cdeedc795fdd18e65f27b9`.

All selected F source/import pins matched their F recorded hashes. One older inherited Sol6 `phase3-abel-physical-box-registry.json` contains the stale/malformed OneTimeVariationTransfer digest `a95d23a647f15f6493aceab13fa2f030ec9a62a25288a3da38261bf00e379ee`. The selected current named top-level source hashes to `a95d2382050cef73840e8a9cd212e6fe4e58ade1b984baf49b9a99ea8d71e79e`; the discrepancy is explicit in REGISTRY. No prior metadata was edited and no different-byte mirror was substituted. This is an installation-pin issue, not a mathematical closure claim.
