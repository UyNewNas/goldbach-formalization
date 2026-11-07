# S29 — independent review of actual upper/lower same-rho PP

Status: **frozen independent publication-checkpoint review; full assigned yellow scope HOLD**. This report audits S19/S24 and the S22 spectral dependency. Source acceptance below means only that the displayed bounded mathematical claim survives independent static review. No Lean/Lake/compiler, guard, numerical replay, CI dispatch, Git/remote mutation, author-file edit, child agent, or account-usage inspection was performed. `compiled=false`, `kernel_verified=false`, `formal_credit=0`; finite proof bodies remain `UNEVALUATED`.

The assigned review directory is `docs/source-only/20261102-resume-30s/S/s29_review_actual_pp/`. All writes in this review are confined there. Author delivery hashes were independently re-read for this freeze. An old report, a source-only declaration, a theorem with its own target as a premise, or a CI pass on a narrower leaf does not close a whole yellow parent.

## Exact scope and terminal statements

The authoritative initial tracker is `../1_+_1.748_lean_proofs/main.md`, SHA256 `eda2afd45edaa3d00072bb677dd5eb3c9937c40d63ac23149ebbe3581cbeaca9`. The reviewed original yellow statements are:

- Line 98: `P3.6 把估计实例化到同一rho和实际PP源族`.
- Line 110: `外层positive marked族/Theta、chosen-grid profile、post-loss level与完整同rho PP总装`.
- Line 137: `P4B.4 供应hdensity和hUniformPP，消除上界前提` (PP part here; S27 reviews the density supplier).
- Lines 144/161: `P5.6 供应八组原始causal估计并闭合hLower` / `把八组真实供应闭合到同一原始实例` (the actual h7/h8/h9/h1011 part here; the other four are not silently discharged).
- Lines 90/97 are the genuine original full-range 7/32 spectral dependency; S30 owns its independent full spectral audit.

The actual upper terminal is the `hUniformPP` argument of production `ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean:45–52`, theorem `ImbalancedChen.P4BCurrentSmoothBadUpperSuppliers.current_realBad_upper_of_actual_density_and_uniform_smooth_PP`. For the original physical parameters and the same `epsilon delta`, `retain delta`, and `cap delta`, it is

```lean
∀ delta : ℝ, 0 < delta → ∀ physicalWidth : ℝ,
  0 < physicalWidth →
  2 * physicalWidth ≤ (1 - kappa) * b / (1 + b) - nu * r →
  UniformPrimeProductTarget (ι := Unit) 2 (fun N : ℕ => N)
    (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
    (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
    (fun N _ => P4B.smoothPhysicalPairOuterRamp b N
      (manuscriptHalfProductCutoff kappa N) physicalWidth)
```

`Part3DistributionTargets.lean:187–193` expands the target as `∀ A>0, ∃ C>0, ∃ N0, ∀ N≥N0, Even N → ∀ i, |primeProductSignedError ...| ≤ C*N/(log N)^A`. Thus **delta, a fixed legal width, and A precede C and N0**. The terminal covers every legal fixed width; it does not require one constant/threshold for arbitrarily shrinking widths chosen after N0. R19's zero correction is stronger in this respect and K's `width^(-24)` is compatible with the actual terminal. The same coefficient at a fixed precision must occur in density, pointwise majorization, and distribution. The manuscript expressly allows a different finite coefficient at a different precision.

The physical parameter assumptions stay `1/2<b<1`, `0<kappa<1`, `nu>0`, `r>0`, and `nu*r<(1-kappa)*b/(1+b)`, with `0<epsilon delta≤1`, `(epsilon delta)^2≤r` and eventual physical cap at least `N^(nu*r)`. Neither `currentK=8452171/1250000` nor `currentC=49044063/25000000` changes. An auxiliary factorization level cannot replace the physical level or residual Q/B.

The actual lower consumers are the four arguments of `ImbalancedChen.P5OriginalCoefficientArithmetic.eventual_D12_of_fixed_original_grouped_suppliers` in production `P5OriginalFixedDensitySupplierAssembly.lean` (and identically the corresponding mean assembler). With `k=fixedProductDensityCoefficient` and the **same original E**:

```lean
h7    : ∀ delta>0, ∀ᶠ N, Even N → U7 N ≤ (U7Envelope k + delta)*H N
h8    : ∀ delta>0, ∀ᶠ N, Even N → U8 N ≤ (U8Envelope k + delta)*H N
h9    : ∀ delta>0, ∀ᶠ N, Even N → U9 N ≤ (U9Envelope k + delta)*H N
h1011 : ∀ delta>0, ∀ᶠ N, Even N →
          U10 N + U11 N (E N) ≤ (originalJointRawCost k + 2*delta)*H N
```

Here `Uj` abbreviates the literal `currentChenUpsilonj` and `H` abbreviates `singularNormalization`; these abbreviations in this report are not new Lean declarations. In particular h1011 supplies the original **raw** joint endpoint, before the existing proved reserve/surplus weakening. U7 retains one signed PP3+PP4 sum, U8 its original rank-three source, U9 all three labelled branches, and U10+U11 one original common positive four-prefix partition. Separate overlapping alternatives cannot be added.

## Original manuscript and primary theorem applicability

Independently read the original manuscript body at 127–165, 201–254, 256–357, 538–559, 737–817, and 882–904; its SHA256 is `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Also read the actual PP completion and coefficient completion, rather than deriving scope from source filenames.

The original PP statement is the signed sum `sum_q rho_N(q) [sum_{p1...pk≡N mod q} W_N - X_W^(q)/phi(q)] = O_A,W(N/log^A N)`. The permitted original primes have a fixed positive power floor and complete product O(N); weights are fixed finite smooth geometric families with polylogarithmic mixed Euler bounds and no additional arithmetic filter. The admitted coefficient classes are the actual upper and lower trees, marked queries and ordinary descendants, and positive switched families. The exact smooth trim, order-three HB identity, Fourier norm (not the number of retained modes), rough-slot auxiliary SW, low-rank BV, and one/two-long branches must all apply to the actual source. Complete scale is the full product, never a residual quotient.

`distribution-prime-product-completion-20261010.txt:25–70` states the actual coefficient hypotheses and only an **absolute** PP error. Lines 74–117 give the actual trim, pre-HB rough cutoff and proper-power correction; 119–149 give the exact factorial tensor and collision correction; 153–216 give the actual coupled Fourier norm, exhaustive branches and SW. `distribution-coefficient-completion-20261010.txt:69–110,144–220,225–275` distinguishes physical cap from analytic cover, retains every full/selected square, requires the partition to be fixed on a whole atom box before arithmetic tuples/error signs, preserves marked factorial multiplicity and one beta pair, and fixes moment orders before kappa/thresholds. Its low-rank classes are different: upper `19/48`, lower start `38/125`, marked `1527/3584`, plus independently buffered classical states. J/R18's upper rank-two theorem alone is not all of these.

The manuscript's Theta is exactly `4*li(N)*sum_B sigma(B)*C(BN)/(phi(B)*log(Q/B))` for one common Q and a nonnegative marked family. Positivity alone cannot convert an absolute `N/log^A N` bound to a relative `epsilon*Theta_Q` bound uniformly over positive weights. Zero mass and a fixed positive geometric family must be handled in their actual domains. No artificial universal family-mass lower bound is authorized.

Read the saved exact primary extractions under `../goldbach-research/external-source-audit-20261009/`: Pascadi v3 Theorem A (lines 512–556), Theorem J (2886–2943), and ABL v1 (575–1010, including Lemmas 3.1/3.2 and continuous/holomorphic clause). Theorem A is a true Maass-basis/Fourier-coefficient inequality with arbitrary complex n sequence and cusp density `1/q`; Theorem J averages the actual infinity-cusp coefficients against one common additive phase. The existing common-interval extension does not permit choosing a different maximizing interval at each level. ABL's oldform K depends on dilation in general; the actual coprime-level specialization is what makes K=1. The transformed n coefficient must be independent of spectral height, and the full continuous/holomorphic forms are distinct from the principal subgroup. These exact applicability requirements cannot be replaced by an arbitrary arithmetic coefficient/Bessel packet or generic hEnergy assumption.

## Accepted exact reuse; not missing work and not new credit

R17–R19 author REPORT/REGISTRY and R29 independent review were read, then the relevant original declarations were checked directly. The registry gives precise source/hash/declaration pins.

| Source | Accepted supplied scope | Boundary that remains |
|---|---|---|
| R17 joint labels and upper payment | Full tagged old-pair/mother-occurrence arithmetic source, actual multiplicity order `length(cs)+3`, full upper rejected absolute logarithmic payment with threshold before later labels/weights | Joint lower/order and positive-Theta relative payment, actual selected causal-family identification |
| R17 `P2GammaPairThetaZero` | Exact existing product pushforward of Theta; equal-product weights add; zero Theta forces every nonnegative pair weight zero and annihilates the displayed rejected source | Its `pairSourceTheta` definition is not an equality between `Qphys` and original `rootQ N t`; positive mass is not paid |
| R18 grid | Actual logarithmic hat, ceil cover, head Abel/mother cost and fixed-order derivative budgets | Extra coupled amplitude Fourier/Mellin norm is not that head-only cost |
| R18 support/conductor | Real original 19/96 upper rough-rank≤2 coefficient including beta, complete retained scale below x^(9/20), actual all-mother local conductor call with common N threshold | Other physical classes, enhanced same-integer coefficient cover, full signed chart/mother sum |
| J/K upper source | Original arbitrary-width pair profile; complete ordered HB occurrence/Fourier source identity; complete post-modulus Fourier-tail payment with two-group scalar logarithmic cost 14 | Actual support gate, retained modes and source reserves are separate obligations |
| R19 | Every actual upper source chart's rough-prime reserve is exactly zero; inserted into the exact same attached Q/rho source identity | Original trim, negative proper-power correction and full retained mode bank still appear |
| R24 spectral | Current OriginalData six hard tails paid with actual raw source mass and common fixed-order/threshold; both zero lanes identified with native finite estimates | Full normalized trace/energy, all spectral classes/A/J/regular/gap and normalized zero budgets |

The current raw root Q is explicitly `N^(Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1))` in H's `P2OriginalU5SmallPartnerRootPayment.lean:26–27`. `P2OriginalPairRootActualQuery` already preserves exact per-root physical Q and double-buffer query. Neither statement constructs a finite selected family with one Q. S17 confirmed that its W1/W2 carrier dictionary does not yet supply this full selected-family equality. This is a missing actual construction, not proof that a source file is absent or a manuscript counterexample.

## S19 candidate independently reviewed

Read the complete first candidate `S/s19_actual_upper_pp/P4BActualUpperTrimPayment.lean`, raw SHA256 `28e99c3bc8e1f4e1a71fb2157e9b3126913a7866e3db0c1989b654d53a01bd48`, and its exact physical signed-row and originalLowerCut suppliers. The author confirmed this final checkpoint byte freeze; the independent hash agrees.

`lowPrimeWords_card_le` preserves ordered original prime words, including repeated primes, and bounds each complete-product fibre by the existing ordered-factor divisor count. The proof does not assert injectivity of product. `wordKernel_eq_signedRow` retains target N and product in the original signed count-minus-exact-coprime-mean. The actual ramp/list extension is in [0,1]. `exists_actual_trim_budget` uses `Y<N` before the noncollision signed-row theorem, so product=N and tau(0) never enter this trim. The complete modulus sum, not each isolated q, is bounded.

`eventually_actual_upper_trim_logAccuracy` fixes `eps=kappa0/4`, uses the actual `ceil(2*N^(1-kappa0))`, and pays the whole trim with powers `1-kappa0/2` and `1-3*kappa0/4`, both strictly below one. Its threshold precedes every legal width and later policy/cap. No trim estimate, source-mass estimate, hPP, hUniformPP or target-equivalent structure field is an input. The only coefficient premise is the actual active-support bound `actualActiveUpperCap ... ≤ N^theta`, for a fixed `theta≥0`.

**Static disposition: accept this bounded class-II source deduction subject to remote elaboration/kernel/axiom verification.** It is not yet an unconditional final frozen-policy trim instance. It does not pay proper powers, retained modes, the selected common-Q positive family, or the full final PP target. No final premise is counted removed at this checkpoint.

The second candidate `P4BCommonRefinedUpperTailAndTrim.lean` was then read in full together with E's `P5ActualCommonRefinedRange` and the existing structural `P5OriginalCommonRefinedConstructor.OriginalData`. The record contains coarse parameters and actual finite fourth/fifth rows/licensing, not a PP/density/energy field. `commonRetain` is literally its `policy8` at `nu=1`; E already proves its signed nonzero attached support below `N^(599/1000)` for `epsilon≤1/1000`. The new `common_supported` supplies K's exact natural floor cap, and `common_natural_cap_bounds` supplies the required positive cap and rpow bound. `exists_common_original_upper_fourier_tail_paid` then actually consumes K's full two-group tail theorem, retaining `width^(-24)` and `retainedUpperAtlas`. `eventually_common_original_upper_trim_paid` consumes the new full trim theorem and E's actual active-cap bound. These are accepted bounded source instantiations subject to remote verification, not new range/Fourier proofs.

The two support premises are therefore removed **for this independently specified common-refined policy**. There is still no established identification of that record/policy with the final full87 buffered coefficient required by the density and upper-terminal construction. Neither the `.599` range nor use of the name `OriginalData` supplies that missing equality. This difference is explicit in the candidate and is not treated as a manuscript counterexample.

## S24 actual lower source boundary

Directly read the production U7 source-supplied route and literal physical weights, U8 physical source, U9 ordered physical source, and the existing U1011 same-rho smooth-main approximation. U7's actual source mass is already supplied and must not be reconstructed or reported missing. U8's unit/repeated diagonal arithmetic payment already exists. U9 branch labels and original multiplicities are retained exactly. U1011 already has a fixed-mesh/width-before-N separated approximation of the **native signed divisor main**; that result explicitly does not prove AP/center/full-PP estimates.

The U7 `weight3/weight4`, U8 `physicalWeight`, and U9 `orderedPhysicalWeight` are original source-membership indicators. They retain sharp geometric walls and center-coprimality. Being bounded and modulus-independent does not make them permitted smooth PP weights. A real permitted positive smooth approximation remains required. If using the old consumers' exact hard-source hPP premises, actual boundary/center-filter correction must be paid after the same-rho modulus sum. Alternatively, the original positive physical-divisor majorant can support a direct smooth upper-count route, paying the extra smooth main mass without asserting monotonicity of signed PP. **The manuscript does not require the stronger arbitrary sharp signed-domain theorem merely because an existing consumer exposes it as a premise.** The terminal obligation is the actual Uj envelope. Their positive original prime floors provide a plausible route to paying target-prime factors, but neither this review nor the existing source identities is that proof. S24 confirmed this boundary and is working on the actual conversion.

At this checkpoint h7/h8/h9/h1011 remain unproved. A new consumer retaining `hPP`, density or licensing as an unprovided field would not change that verdict.

The first S24 candidate `P5OriginalU789SmoothLogSources.lean` was read in full. It defines literal affine-log smooth gates for U7's separate three/four-prime sources, U8's separate first/second `N^(1/3)` walls, and U9's exact original inverse branch permutations and `q≥sqrt(N/(p1*p2))` wall. It proves [0,1], smoothness in log coordinates, nonnegative margins on each original nonzero source, and exact one-plateau there. It retains U7/U8 weak repeated-prime walls and all three U9 labels. This is a genuine local source-conversion candidate, with no desired PP/boundary premise.

A material support conversion was identified and supplied during review: the auxiliary factor `smoothGateUpperStep width (1-sum v)` alone, at fixed positive width, permits products up to `N^(1+width)`, outside the original O(N) complete-product class. The final candidate's new `productUpper` instead uses `smoothGateUpperStep width ((1-sum v)*log N)`, so nonzero support has product `<exp(width)*N`. Its `physicalOuter*` multiply this gate by the literal log profiles, and `actual_sources_on_physical_plateau` proves that the new gate is exactly one on all original sources. It does not alter a hard source definition.

Independently read the full appended conversion and proof through `actual_smoothing_prime_support`. For `0<width≤417/40000`, the full smoothed support of every branch has every prime `>N^(417/10000)` and complete product `<exp(417/40000)*N`, including tuples outside the original source. U9's third-prime floor is derived from its own first/second and quotient-square walls. These constants are smoothing reserves; the original `59/250`, `417/5000`, `19/125` source thresholds remain unchanged. **Static disposition: accept the bounded actual smooth-profile/plateau/positive-floor/O(N)-support conversion, subject to remote verification.** Quantitative physical Euler/Fourier budgets, positive main approximation (or genuine hard-filter/boundary correction for the old hard-PP route), retained modes and actual final suppliers remain unproved; smoothness alone is not that estimate.

Also independently read S24's `P5OriginalU789SmoothChartRoughOne.lean` in full. Its dependent-rank `Source` contains exactly the actual two U7 sources, one U8 source and three U9 branch labels, with ranks three/four and no artificial absent ranks. It applies the existing `independent_test_chart_cutoff_eventual` at the newly proved common prime floor, with fixed `K≥4` before N and one N0 before every width, source label, chart and original prime word. Actual nonzero psi gives the chart windows; actual nonzero smoothing gives the prime floor and the original independent-prime cap N. Each active `roughWord` is exactly one. `eventually_actual_full_chart_correction_zero` annihilates the entire displayed finite chart/source correction even with arbitrary further complex factor F. This is valid exact zero, not a bound assumed of F and not a source mass/PP premise. **Static disposition: accept this second bounded class-II conversion subject to remote verification.** It does not identify or estimate the subsequent full actual HB mode bank.

## S22 spectral dependency traced

S22 explicitly reported that no whole actual 7/32 export is available. Independently read its candidate `Part3OriginalUniformTestCutoffBudget.lean`: the exported `exists_original_six_test_and_tail_threshold` prepares the actual finite `C^d` test mass plus one degree-two cutoff debit and reuses R24's original six-tail at one threshold. Its ratio called `rho` is the spectral-kernel ratio `V*M/N`, **not** the physical signed sieve coefficient `rho_N` in PP. It does not produce a normalized Kuznetsov identity, A/J/regular/gap inequality, continuous/holomorphic full class, normalized zero-lane payment, or full outer scalar estimate.

The candidate preserves one test-family charge: order zero has 12eta plus the cutoff's 2eta (14eta); order four has 28eta plus that cutoff (30eta). These are alternative orders of the same source. This review does not add a second 28eta to an already charged estimate or declare 14eta sufficient for a fourth-derivative use. S30 owns the full spectral review. There is currently no actual S22 theorem to instantiate into the physical hUniformPP or the four lower slots; the final premise delta is zero.

## Required remote evidence and full-scope verdict

S02 and root received the exact terminal types and quantifier order early. Before any whole-yellow green claim, evidence must include all of the following in a reviewable artifact:

1. Exact source and transitive import manifest hashes, intended module map, Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native upstream `09b97db5764ade1246bfb77206baa1b124760958`, and matching remote commit/tree. Existing identical-source successful artifacts should be reused.
2. Successful remote elaboration and kernel evidence for the actual supplied declarations and their dependency closure. The new trim leaf is an eligible bounded target; a final PP target is eligible only when the full actual source is supplied.
3. Expanded theorem types and `#print axioms` for each new supplier and the actual upper/lower terminal chain. No new axiom, sorryAx/admit, unsafe theorem, target-equivalent licence field, desired hPP/hUniformPP/hEnergy premise, or estimate defined by subtracting the claimed target may remain. A standard-foundation axiom list is not proof that an arbitrary explicit target premise was discharged, so both the type and axiom evidence are necessary.
4. Explicit application of actual declarations to the fixed policy, source W, modulus carrier, rho, widths, complete scale, cover, residue range, and parameter/threshold order. Retained global squarefreeness, signed multiplicities, exact coprime mean, common interval/phase and actual derivative/scalar costs must remain visible.
5. Independent full-node scope audit: original selected common-Q source and positive-Theta relation; enhanced same-integer factorization; all physical low ranks and medium/one-long/two-long alternatives; trims/proper powers/Fourier norm and retained modes; every displayed upper and lower consumer premise. A narrow leaf's green evidence must not be inherited by the whole parent.

**Whole assigned yellow scope: not source-complete at this checkpoint. No green recommendation.** Formal/API/import/elaboration uncertainty is class I. The new trim and missing actual parameter/source conversions are class II. Full normalized spectral source/energy and remaining actual global estimates are unresolved class II/III obligations. The inspected evidence establishes no substantive counterexample to the manuscript; it also supplies no license to call the original analytical conclusions formally proved.

## Independently frozen source pins

| Actual delivered source | Raw SHA256 | Review disposition |
|---|---|---|
| S19 `P4BActualUpperTrimPayment.lean` | `28e99c3bc8e1f4e1a71fb2157e9b3126913a7866e3db0c1989b654d53a01bd48` | Bounded full trim source accepted; actual active-cap premise explicit |
| S19 `P4BCommonRefinedUpperTailAndTrim.lean` | `557fffde0657b03b9120507d29d38e7fe3d6e451b124f1fe13ea423dfe40ded5` | Actual structural-policy support instantiation accepted; full87 equality remains |
| S24 `P5OriginalU789SmoothLogSources.lean` | `c42a2276c826f5ed8a6050663b4e0d11b25c2c713fb4a0a45640dbebaf83ce67` | Actual plateau, fixed positive floor and O(N) support accepted |
| S24 `P5OriginalU789SmoothChartRoughOne.lean` | `71eb3bbc183e14b302601f4c8d2aee1fafe176f74c32b7dec7f864a52dd179b8` | Six actual smooth-source chart rough insertion/correction-zero accepted |
| S22 `Part3OriginalUniformTestCutoffBudget.lean` | `0db0af01d82e152dad6e153d86ce78eb3deaa46390c9ef1f11957a4623a6a1a0` | Export-type/cost cross-review only; no full actual 7/32 supplier |

S22's final namespace-only correction opens the existing `OriginalMediumPhysicalE3Block` for `Rectangle`; the final header and hash were re-read. It changes no mathematical conclusion. S19's final REPORT/REGISTRY hashes are `53bd3bbbe81708aa01e87f3b82256f8dd1f549a84a512ef87a94180c77ae08d7` / `4428367ebfc2774149344e21f18772e423b1ea91a321868ef8e42ce3322cb0aa`. S22's final REPORT/REGISTRY hashes are `0263d906aae45310ddcc67c39f9c973e7a4623117618476aaf5126511f3147d5` / `cd73d16386c5fe408449b3a8271dcb3f0b41a6ddd13c1aa85f00877a9870e450`. S24's final report and registry are separately hashed in the independent registry. Each author's explicit whole-scope verdict is HOLD with zero final PP/lower-slot premise removals; the reports agree with the inspected declarations.

The final `REGISTRY.json` binds this report, the exact author source bytes independently inspected, relevant primary/production/reuse files, declarations and remaining premises. It does not fabricate compile or axiom evidence. S19's 38 registered new/reused source byte hashes were independently recomputed and all matched; this is byte evidence, not a claim to have re-proved all 38 inherited mathematical bodies. Root ordered the checkpoint freeze and the authors stopped further research for this publication set.
