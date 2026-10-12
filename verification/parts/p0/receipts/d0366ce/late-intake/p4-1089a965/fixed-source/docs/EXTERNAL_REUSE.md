# External Lean reuse audit

Audit date: 8 October 2026 UTC. Scope: external foundations relevant to the imbalanced-Chen transfer manuscript, including semantic fidelity, theorem assumptions, licensing, dependency pins, and actual CI evidence.

## Bottom line

1. **Reuse Mathlib rather than reconstructing arithmetic multiplicity, rational logarithm enclosures, or finite Selberg diagonalization.** These APIs exist both at the compatible Mathlib revision below and in current master.
2. **subfish-zhou/goldbach-lean is the strongest application-level candidate found.** At the inspected commit it has literal unconditional Chen 1+2 and Li–Liu 1+1.9 theorem statements, ordinary natural-number primality and arithmetic, matching finite counts, and exact-commit successful CI with source, theorem-type, axiom and module-replay checks.
3. **That is evidence for the existing .9 exponent and .67 Chen coefficient, not the manuscript's .76407 exponent, 1.8271 Chen coefficient, or 6.786 upper-sieve coefficient.** No formal theorem with those new manuscript constants was established in this audit.
4. **Two traps must be avoided.** The historical UyNewNas Chen endpoint is explicitly conditional, including an old counting premise documented as false. ANT's legacy theorem named `bombieri_vinogradov` is only a pointwise parameter-dependent bound and does not establish classical BV.
5. **External code has not been integrated or independently rebuilt by this audit.** The subfish CI run inspected in detail used a warm exact project-cache hit. A fresh isolated build and downstream literal target/axiom probes should precede adoption. License, source, and CI evidence justify prioritizing that work over reimplementing its analytic foundations.

## Revisions and compatibility

| Source | Inspected revision | Toolchain / dependency | Recommendation |
|---|---|---|---|
| Mathlib compatible baseline | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` | Lean 4.33.0-rc1 consumer pin | Use for an initial compatible reuse branch |
| Mathlib current master | `9e6b3aac99b624d10c84653ab9c5357283b9b3b8` (7 October 2026) | Current source checked; not compiled here | Relevant APIs still present; do not upgrade automatically |
| subfish-zhou/goldbach-lean | `09b97db5764ade1246bfb77206baa1b124760958` | Lean 4.33.0-rc1; Mathlib e4c91783 | Main reuse candidate |
| UyNewNas/analytic-number-theory-lean | `88ee563ba0021702ea370b13bae7c7e7fec59657` | Same Lean and Mathlib pins | Reusable neutral analytics, subject to statement-level selection |
| UyNewNas/chen-theorem-lean | `857f1a060210b0f274a423d55bbf614becb90a0f` | Same Lean/Mathlib; ANT dependency pinned to `e07b9d2c5b91f82dab8138aed7e84788917e97f0` | Arithmetic and corrected finite-counting reference, not an unconditional endpoint |
| lixiang90/chen_theorem | `11dcca8fc3ab340358503278c46d72aef072a6e7` | Lean/Mathlib 4.32.2 | Additional mathematical source; licensing and execution evidence unresolved |

Sources: [subfish Lake file](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/lakefile.toml), [toolchain](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/lean-toolchain), [ANT Lake file](https://github.com/UyNewNas/analytic-number-theory-lean/blob/88ee563ba0021702ea370b13bae7c7e7fec59657/lakefile.toml), [historical Chen Lake file](https://github.com/UyNewNas/chen-theorem-lean/blob/857f1a060210b0f274a423d55bbf614becb90a0f/lakefile.toml), [lixiang Lake file](https://github.com/lixiang90/chen_theorem/blob/11dcca8fc3ab340358503278c46d72aef072a6e7/formal/lakefile.toml). The GitHub default-branch commit and exact source were fetched, rather than treating the website as the authority.

## 1. Mathlib: immediately reusable foundations

### Prime factors counted with multiplicity

Import `Mathlib.NumberTheory.AlmostPrime`, backed by `Mathlib.NumberTheory.ArithmeticFunction.Misc`.

- `ArithmeticFunction.cardFactors`, scoped notation `Ω`, is the length of `Nat.primeFactorsList`.
- `Nat.IsAlmostPrime k n := n ≠ 0 ∧ Ω n = k`.
- `Nat.IsAtMostAlmostPrime k n := n ≠ 0 ∧ Ω n ≤ k`.
- `Nat.IsSemiprime` means exactly two factors, not the prime-or-product-of-two predicate used in Chen's theorem.
- Useful proofs: `ArithmeticFunction.cardFactors_mul` (both factors nonzero), `cardFactors_pow`, `cardFactors_apply_prime_pow`, `cardFactors_eq_one_iff_prime`, `Nat.Prime.mul_isAlmostPrime_two`, and `Nat.Prime.sq_isAlmostPrime_two`.

**Endpoint convention:** Mathlib's at-most-two predicate includes 1, whereas subfish's Chen second summand explicitly has size at least 2. The manuscript itself permits Ω(1)=0 with an at-most-one counting discrepancy. Formalize that finite discrepancy rather than silently identifying the counts. Likewise avoid `primeFactors.card`, which counts distinct primes.

Source: [AlmostPrime](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/AlmostPrime.lean), [multiplicity arithmetic](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean). The AlmostPrime file was byte-identical at current master.

### Exact rational logarithm bounds

Import `Mathlib.Analysis.SpecialFunctions.Log.Deriv`. Relevant existing real theorems:

```lean
Real.abs_log_sub_add_sum_range_le
  (h : |x| < 1) (n : ℕ) :
  |(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + Real.log (1 - x)|
    ≤ |x| ^ (n + 1) / (1 - |x|)

Real.sum_range_le_log_div
  (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
  ∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1)
    ≤ 1 / 2 * Real.log ((1 + x) / (1 - x))

Real.log_div_le_sum_range_add
  (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
  1 / 2 * Real.log ((1 + x) / (1 - x))
    ≤ (∑ i ∈ Finset.range n, x ^ (2 * i + 1) / (2 * i + 1))
      + x ^ (2 * n + 1) / (1 - x ^ 2)
```

For positive rational t ≥ 1, substitute x=(t−1)/(t+1). The resulting finite sum and error are rational; explicit `norm_num`/kernel-checked arithmetic can certify the manuscript's logarithmic inequalities. This bounds actual `Real.log`, rather than trusting an external floating-point computation. The denominator in Mathlib's displayed tail is exactly the one above; do not substitute a sharper unproved tail.

Source: [remainder bound](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L217), [lower and upper odd-series bounds](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L320). All three names remain in current master.

### Finite Selberg infrastructure

Import `Mathlib.NumberTheory.SelbergSieve`.

`BoundingSieve` packages a finite support, nonnegative weights, a squarefree product of sieving primes, total mass, and a multiplicative density with 0<ν(p)<1 at the sieving primes. It defines the actual sifted sum and remainder.

```lean
BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
  (muPlus : ℕ → ℝ) (h : BoundingSieve.IsUpperMoebius muPlus) :
  s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus

BoundingSieve.upperMoebius_lambdaSquared
  (weights : ℕ → ℝ) (hw : weights 1 = 1) :
  BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared weights)
```

`BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq` supplies the full diagonalized quadratic form. `SelbergSieve` adds a level ≥1.

**Scope limit:** these are finite identities and inequalities. They do not themselves prove the manuscript's level-sensitive coefficient 6.786, distribution errors, Rosser stopping rules, or prefix density gains.

Sources: [upper-sieve theorem](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/SelbergSieve.lean#L216), [diagonalization](https://github.com/leanprover-community/mathlib4/blob/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/NumberTheory/SelbergSieve.lean#L375). Subfish also includes [Selberg upper-bound extensions](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/AnalyticNumberTheory/Sieve/SelbergUpperBound.lean), including `selberg_upper_bound_optimal`; this particular optimum ranges over all divisors of the sieving-prime product. Its name alone does not supply a truncated-level analytic bound.

## 2. subfish: semantic and trust audit

### Literal endpoint audit

[Goldbach.Statement](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/Goldbach/Statement.lean#L16) imports only Mathlib primality definitions and parity and defines:

```lean
∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
  ∃ p q : ℕ, p.Prime ∧
    (q.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ q = r * s) ∧ N = p + q
```

[Goldbach.chen_theorem](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/Goldbach/Theorem.lean#L15) has that type without a mathematical hypothesis. CI's elaborated output explicitly printed `Nat.Prime`. The threshold is a natural number chosen before all subsequent N; no bounded-only enumeration, vacuous real threshold, or hypothesis carrying the conclusion appears.

The [1+1.9 entry](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/Goldbach/OnePlusOneNine.lean#L15) has:

```lean
∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
  p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
    N = p + r * q ∧ r ^ 10 ≤ q ^ 9
```

The equality and powers are over genuine naturals. Its real-power companion explicitly casts r and q to ℝ and uses `((19 / 10 : ℝ) - 1)`; it is not natural-number division accidentally producing a different exponent. The proof passes through an existing power-equivalence theorem. The exact natural-power statement already avoids real-power convention ambiguity.

The [finite representation module](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/LiLiuGoldbachOnePlusOneNineFinite.lean#L30) defines the count as the cardinality of `(Finset.range (N + 1)).filter` of eligible prime p. Witness pairs are existential, so different factorizations do not inflate the count. The independent [count probe](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/Goldbach/OnePlusOneNineChecks.lean) proves extensional equality with a literal filter and checks the 0.0004 inequality. As q is prime and r≥1, N=p+rq implies p<N even though the carrier includes p≤N.

### Normalization and available coefficients

The public Chen count coefficient is **0.67**. Li–Liu's public count gives **1/2500** and a family for each fixed κ<515093/800000000, with κ chosen before the threshold.

`liuSingularSeries_source_formula` expands to the manuscript's odd-prime universal product times the odd prime-divisor correction. Its positivity is proved. Do not substitute the legacy `singularSeries`: the code separately proves that its finite sieve normalization differs by a factor of two and a tail correction.

Source: [normalization definitions and identities](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/Arithmetic/LiuSingularSeries.lean).

### Inspected proof route

For Chen:
- `Goldbach.chen_theorem`
- `MathlibNt.ChensTheorem.chens_theorem_unconditional`
- `ChenVerifiedPrerequisites.chens_theorem_of_liu_coprime`, with the premise supplied by `LiuWeight.liuPanCanonicalCoprimeTheorem_proved`
- the internally supplied Jurkat–Richert weighted lower certificate and genuine switched-source Selberg/triple estimate
- corrected finite counting, followed by the semiprime equivalence.

For the quantitative Chen endpoint, `chen_good_representations_lower_bound_of_triple_penalty` explicitly consumes the lower bound, the triple bound, the negligible remainder, and `corrected_counting_bridge_public_of_nine_le`. It does not consume the known-false historical bridge.

Sources: [unconditional wrappers](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/ChensTheoremUnconditional.lean), [counting/sieve assembly](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/Chen/ChenVerifiedPrerequisites.lean), [proved Liu–Pan producer](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanUnweightedUnconditional.lean).

For Li–Liu existence:
- `Goldbach.one_plus_one_nine`
- `goldbach_onePlusOneNine_nat_unconditional`
- `eventually_onePlusOneNine_of_sharp_margin_pos`
- `goldbachSharpElementaryMargin_pos`
- certified G67 lower, G9 upper, and G12 upper integral estimates.

The strictly positive exact retained margin is 126891/200000000. The separate 0.0004 count follows the author-G11 quantitative ledger, not merely this earlier existence margin.

Sources: [existence assembly](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/LiLiuGoldbachOneNineUnconditional.lean), [stronger count assembly](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/LiLiuGoldbachG11AuthorQuantitative.lean).

### Genuine PNT and BV versus names only

The [PNT facade](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/AnalyticNumberTheory/PrimeDistribution/PrimeNumberTheorem.lean) imports the adapted PNTAnd proof and proves a genuine `Nat.primeCounting` asymptotic with a little-o relative error. It also exposes a Chebyshev-psi error of order x·exp(−c(log x)^(1/10)). This is not a count redefined to equal x/log x.

Subfish's [StandardBombieriVinogradov definition](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/Distribution/BombieriVinogradov.lean#L130) has correct uniform quantifier order:
- for every A>0,
- choose B≥0 and C>0,
- then for all sufficiently large natural N,
- sum errors over actual moduli 1≤q≤floor(√N/(log N)^B),
- with a maximum over all y≤N and canonical coprime residues,
- bounded by C N/(log N)^A.

The prime count is a literal finite filter with `Nat.Prime` and congruence. Its center is the genuine logarithmic integral with fixed additive normalization 2/log 2. A separate [unconditional producer](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean) supplies `AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov`. Its exact immediate chain is `standardBombieriVinogradov_of_nonprincipalPrimitivePsi` applied to `nonprincipalPrimitivePsiSiegelWalfiszSource`; that producer consumes `rawLandauSiegelLowerBound`, proved from `Bombieri1965Theorem4.exists_uniform_quadratic_LFunction_one_lower_bound`, and explicitly constructed canonical smoothing data.

For varying bounded coefficient–prime convolutions, [liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/MathlibNt/SieveTheory/LiLiuPanBoundedAggregate.lean#L91) chooses C, B and N₀ before N, interval endpoints, and coefficients vary. It assumes |f(a)|≤1, A₂≤N^(2/3), and (log N)^(2B)≤A₁; the convolution remains inside the discrepancy's absolute value.

**Still required for this manuscript:** prove an exact adapter from a found distribution theorem to the manuscript's curved semiprime or finite prime-product region, preserving all uniformity, auxiliary coprimality, ranges, and error budgets. Ordinary BV is not automatically the stated generalized convolution theorem; bounded coefficients are not automatically arbitrary divisor-bounded sequences. No exact ready-made formal Polymath Claim 12 / Theorem 14 adapter was established by this audit.

### Actual CI and trust evidence

Exact-commit [run 34950755779](https://github.com/subfish-zhou/goldbach-lean/actions/runs/34950755779) completed successfully. Job 104320886172's actual logs were read:

- checked out the exact audited commit;
- used Lean 4.33.0-rc1;
- **project-cache-exact-hit=true**;
- `lake --wfail build` completed successfully (11,222 build jobs, with cached replay);
- source scanner reported 2,514 source modules and 2,514 default-build modules, with `issues: []`;
- printed literal public types and transitive axiom sets;
- all six public Chen/Li–Liu endpoints reported only `propext`, `Classical.choice`, `Quot.sound`;
- successfully replayed Goldbach.Theorem, Checks, OnePlusOneNine, OnePlusOneNineChecks, and All using leanchecker over cached imports;
- verification-script tests passed (116 tests, one skipped).

A second [same-commit run](https://github.com/subfish-zhou/goldbach-lean/actions/runs/34949895502) also has successful build, source/axiom, and replay steps.

The [actual scanner](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/scripts/check.py) masks comments/strings and rejects executable sorry, admit, axiom, native_decide, unsafe, and debug.skipKernelTC in its shipped proof-source scope; it checks build coverage/imports and requires exact named axiom reports. This is materially stronger than a green build alone.

**Limits:** this audit inspected the public semantic targets and selected proof dependencies, not every line of 2,514 modules. It did not independently reconstruct all project proof objects from a clean source checkout. Module replay over cached imports is not a separate full rebuild of every imported dependency. Do not describe this as an independently reproduced full formalization.

### Research tree warning

[research/wu2008/README.md](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/research/wu2008/README.md) explicitly says the final Wu08 1.8938 theorem is not completed. It lists genuine delivered fragments alongside unresolved analytic/function inequalities, original nine-row systems, and final numerical aggregation. History contains failed/old variants and is excluded from default build. The public release's green CI does not certify this whole research directory.

## 3. UyNewNas repositories

### Historical Chen

The [actual chens_theorem signature](https://github.com/UyNewNas/chen-theorem-lean/blob/857f1a060210b0f274a423d55bbf614becb90a0f/MathlibNt/ChensTheorem.lean#L153) takes both `ChenAnalyticBounds` and `ChenCountingBridge`. Its [README](https://github.com/UyNewNas/chen-theorem-lean/blob/857f1a060210b0f274a423d55bbf614becb90a0f/README.md) explicitly warns that the historical counting bridge is refuted by finite evaluation for the existing objects. A theorem conditional on such a premise cannot be treated as an unconditional Chen proof even when it has no sorry or custom axiom.

The corrected route exposes `corrected_chens_theorem` under `CorrectedChenAnalyticPositivity`, with corrected finite-counting pieces. Semiprime/multiplicity API and the corrected finite combinatorics may be useful. The older `chens_theorem_weak` proves only infinitely many suitable even integers, by the elementary p+3 construction.

Exact-commit [CI run 31926899504](https://github.com/UyNewNas/chen-theorem-lean/actions/runs/31926899504) passed the public build, conditional-chain audit, and placeholder guard. Those checks correctly certify the conditional statement, not the missing unconditional premise.

### ANT

Current [ANT README](https://github.com/UyNewNas/analytic-number-theory-lean/blob/88ee563ba0021702ea370b13bae7c7e7fec59657/README.md) positions this as a reusable foundation and points to subfish for the completed application. Exact-commit [run 35758715197](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/35758715197) passed build and trust audit. Actual logs report **551** public API axiom reports, all standard, rather than the README's older 463 count.

Good reusable source includes the [Mertens product facade](https://github.com/UyNewNas/analytic-number-theory-lean/blob/88ee563ba0021702ea370b13bae7c7e7fec59657/AnalyticNumberTheory/Mertens/Theorems.lean):
`primeProduct_mertens_isBigO` and `primeProduct_mertens_nat`, with the exact exp(−Euler–Mascheroni) constant and O(log⁻² n) error, uniform constant before all n≥2.

**Reject the misleading legacy BV name as a distribution input.** In [AnalyticNumberTheory/Sieve/BombieriVinogradov.lean](https://github.com/UyNewNas/analytic-number-theory-lean/blob/88ee563ba0021702ea370b13bae7c7e7fec59657/AnalyticNumberTheory/Sieve/BombieriVinogradov.lean):
- `logarithmicIntegral x` is the legacy proxy x/log x;
- `bombieri_vinogradov` chooses C after fixed x,q,y,l;
- the proof sets C to the error divided by the positive comparison scale;
- there is no average over moduli in that theorem;
- the file explicitly records these limitations.

That theorem is valid elementary bookkeeping but insufficient for classical uniform BV. Select the subfish `StandardBombieriVinogradov` contract and its real producer instead, or an independently validated neutral extraction of it.

**Namespace collision:** ANT and subfish both export AnalyticNumberTheory and PrimeNumberTheoremAnd; adding both wholesale is not a safe dependency design. Choose a single owner for each library root or use a small provenance-preserving extraction after a dependency audit.

## 4. Additional candidate: lixiang90/chen_theorem

This separate project has literal Chen/twin-Chen endpoints in [formal/ChenTheorem/Main.lean](https://github.com/lixiang90/chen_theorem/blob/11dcca8fc3ab340358503278c46d72aef072a6e7/formal/ChenTheorem/Main.lean), genuine [prime-or-two-prime and finite-count definitions](https://github.com/lixiang90/chen_theorem/blob/11dcca8fc3ab340358503278c46d72aef072a6e7/formal/ChenTheorem/Defs.lean), and a named-axiom [completion gate](https://github.com/lixiang90/chen_theorem/blob/11dcca8fc3ab340358503278c46d72aef072a6e7/formal/Audit.lean). It also contains [exact logarithmic and integral numerical bounds](https://github.com/lixiang90/chen_theorem/blob/11dcca8fc3ab340358503278c46d72aef072a6e7/formal/ChenTheorem/Main/NumericalBounds.lean) relevant as mathematical reference.

However:
- GitHub Actions reported **zero runs** for this repository during this audit. Its claimed local build success has not been independently reproduced here.
- No root project license was found in the full tree, and GitHub's repository license metadata was null.
- Apache licenses/notices are present for specified vendored PNT and linear-sieve subdirectories; those do not establish a license for all original project files.

Therefore **do not copy its original source until licensing is clarified**, and do not report its source claims as independently verified compilation. Its differing 4.32.2 toolchain also needs a port/rebuild before use in a 4.33.0-rc1 project.

## 5. Recommended adoption order and acceptance conditions

1. Start with direct Mathlib imports for multiplicity, natural/real power comparisons, exact log-series certificates, and finite Selberg algebra.
2. Prefer the exact compatible Mathlib/Lean pins above if importing subfish. Keep the new manuscript layer separate and preserve the distinction between proved external results and unproved manuscript obligations.
3. Before using an external analytic endpoint, independently rebuild its required source closure with inherited LEAN_PATH/LEAN_SRC_PATH cleared. Run literal endpoint examples, `#check @...`, `#print axioms ...`, and a whitelist excluding sorryAx/custom axioms. Retain source coverage and no-bypass checks.
4. Import or extract only the API actually needed: PNT/Mertens, singular-series normalization, actual BV/Pan contracts, level-aware sieve weights, finite count maps, and numerical enclosure lemmas. Avoid another independent PNT/BV implementation.
5. Prove adapters for:
   - singular-series normalization;
   - Ω≤2 count versus prime-or-two-prime count, including 1;
   - real-power or rational natural-power imbalance;
   - generalized distribution on the manuscript's actual curved prime-product region;
   - finite prefix stopping/support rules and exact remainder costs;
   - each interval certificate's link to the mathematical integral it bounds.
6. Audit the final manuscript theorem against a standalone literal specification. A rational arithmetic identity, a positive symbolic margin, or a theorem with the target analytic estimate as a premise is a useful intermediate result, but it is not the final unconditional theorem.
7. Preserve Apache-2.0 license text, applicable notices and attribution for Mathlib, the two UyNewNas projects, and subfish; record exact source revisions and modified files. Subfish's [provenance ledger](https://github.com/subfish-zhou/goldbach-lean/blob/09b97db5764ade1246bfb77206baa1b124760958/docs/PROVENANCE.md) also records its adapted PNTAnd closure. Do not silently copy from an unlicensed candidate.

### Completion boundary

This external-first audit found substantial reusable formal infrastructure and a CI-backed, semantically faithful existing weaker Goldbach application. It does not establish the new manuscript, its claimed novelty, the generalized-distribution adapter, or the improved numerical coefficients. Those remain distinct proof obligations.


## Independent ordinary BV verification completed (8 October 2026)

[Run 37778759271](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37778759271), audit branch head `ff248610d4b945116f448e9085628ee267363760`, rebuilt the 279-module source closure of `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. The literal ordinary BV consumer compiled, and both named supplier and consumer axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`. All 280 expected modules including the probe passed bundled Lean kernel replay, with no missing or unexpected module.

[Evidence artifact 11554018342](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37778759271/artifacts/11554018342), archive SHA-256 `8940ef374ec6d87434cb94df8759f006c3d963aa344ba97c24b10fa589551f26`. The replay uses the same Lean kernel; official Lean and cached Mathlib dependencies remain trusted. This verifies ordinary BV, not yet the separate prime-convolution supplier or the manuscript. Mertens modules were included in replay, but specific Mertens named-axiom audits were not part of the probe.
