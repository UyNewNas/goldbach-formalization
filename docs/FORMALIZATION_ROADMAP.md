# Lean formalization scope and dependency roadmap

Review date: 2026-10-08. Source: `imbalanced-chen-transfer.tex`, especially lines 106–164, 361–424, 3236–3276, 10234–10355, 10497–10988, and 11581–11682. This is an architecture review, not compiled Lean code or verification of the analytic manuscript. No repository changes, Lean implementation, or software installation were performed in this architecture review. Implementation must be checked by a real Lean build; the user has subsequently authorized GitHub CI for compilation. At the initial review only the TeX was available. A companion certificate archive was subsequently supplied; the inventory below is the replay checklist, not a current claim that all assets remain missing.

## Main conclusion

A useful initial Lean milestone is achievable without pretending to formalize Chen's theorem: exact representation definitions, finite count subtraction, rational-power equivalence, elementary asymptotic transfer from explicit hypotheses, and the final rational/logarithmic arithmetic. The full `0.76407` conclusion additionally needs the manuscript's distribution, sieve, weight, and integral-certificate chain. The `0.74774` conclusion also requires the separate published `1.9728` Chen input whose interfaces the manuscript explicitly leaves unaudited. The basic transfer theorem does not, by itself, justify replacing its constant `8` by `6.786`. Smaller imbalance exponents are stronger: the separate `0.76407` result does not improve on the project's conditional published-method baseline `0.749`. The external-input `0.74774` is numerically smaller, but retains the published-input dependency. Neither comparison establishes global priority (see manuscript lines 10469–10496).

## 1. Minimal meaningful kernel-checkable core

Suggested modules are a roadmap, not files claimed to exist.

1. **Representations.** Define `omega m := m.primeFactorsList.length`, Chen primes as a `Finset` filtered from `Finset.range N`, and good/bad counts by filtering that same set of primes `p`. The condition `p < N` makes `N-p > 0`, so the library's `omega 0 = 0` convention cannot create fake representations. Prove, for positive `m`, that `omega m ≤ 2` means `m=1`, prime, or a product of two primes. Keep the exceptional `m=1` case explicitly. Count each `p` once, not factorizations or labelled tuples. For `b<1`, a good composite necessarily has smaller factor first; squares belong to the bad set.
2. **Count subtraction.** Prove the set inclusion “Chen ⊆ good ∪ bad ∪ {p : N-p=1}” and the exceptional cardinality bound `≤1`. First derive `D12 N ≤ Db N + Bb N + 1` over naturals. Cast to reals before writing `Db N ≥ D12 N - Bb N - 1`; this avoids truncated-natural-subtraction mistakes. This theorem needs no sieve theory.
3. **Rational exponents.** For positive natural bases and `d>0`, prove `(r:ℝ) ≤ (q:ℝ)^((a:ℝ)/d) ↔ r^d ≤ q^a`. Use monotonicity of positive real powers, `Real.rpow_mul`, and `Real.rpow_natCast`. Thus the target exponents can use decidable integer inequalities `r^100000 ≤ q^76407` and `r^100000 ≤ q^74774`, with a proved bridge back to the exact manuscript statement. Annotate rational constants with `ℝ` or `ℚ` so `/` is never accidental natural division. Do not evaluate huge powers merely to prove the general bridge.
4. **Abstract asymptotic transfer.** With explicit hypotheses `H>0` eventually, `H→∞`, `D12 ≥ (c-ε)H` eventually, and `Bb ≤ (K log(1/b)+ε)H` eventually for every positive `ε`, prove eventual `Db ≥ δH` whenever `δ < c-K log(1/b)`. The vanishing `1/H` is needed for the exceptional point. An epsilon/eventually formulation is easier to audit than beginning with `liminf`. Parameterize the sequence by `N=2n`, or carefully establish a nontrivial even-number filter. This is a conditional theorem whose hypotheses must remain visible.
5. **Arithmetic and logarithms.** Check the displayed exact rational comparisons with proof-producing arithmetic (`norm_num`, `ring`, `field_simp`, etc.). Prove the logarithm bounds using existing mathlib results, not a floating approximation. Then instantiate the abstract transfer theorem under the explicitly stated count bounds.

The actual normalization still needs its own bridge: define the odd-prime infinite product, prove convergence and strict positivity, define the finite divisor factor, and establish `C(N)` bounded below by a positive constant and `H(N)=C(N)N/log(N)^2→∞`. A bare infinite-product expression is not a proof of those properties. An initial theorem may instead take `H` and these properties as explicit hypotheses; it must not be advertised as the normalized number-theoretic result.

## 2. Concrete numerical work already independently rechecked

Python exact `Fraction` arithmetic reproduced the final displayed equality and strict comparisons. These checks are arithmetic evidence, not Lean kernel verification and not validation of the integral endpoints.

- The quoted old extended endpoint minus the quoted fourth, fourth-tail, and fifth gains is below `3393/500` by exactly `5263022677418334584228327/11295900627024191351160832000` (about `0.000465923245`).
- With `K5=3393/500`, the displayed table recombination equals `4609497840932309/2522777813550000`; its surplus above `18271/10000` is exactly `8156112194/157673613346875`.
- For the manuscript's upper bound `L=2(u+u^3/3+u^5/(5(1-u^2)))`, the surplus `18271/10000-K5 L-1/1000` at `b=76407/100000` is exactly `35699308829233414603473/2410634362470953811500000000`.
- The corresponding surplus `1233/625-K5 L-1/50000` at `b=74774/100000` is exactly `185165622096800747399617/2079121467717203946750000000`.

A useful Lean simplification: `Real.log_div_le_sum_range_add` already proves an atanh partial-sum estimate, with a coarser remainder. Set `u=(1-b)/(1+b)` and use **three terms**:

`log(1/b) ≤ 2(u+u^3/3+u^5/5+u^7/(1-u^2))`.

This existing bound is sufficient for both stated outcomes. Exact arithmetic leaves positive surpluses of approximately `0.000006347662` and `0.000074589240`, respectively. Consequently an initial formalization need not first develop the manuscript's sharper denominator-5 remainder. The exact weaker-bound surplus at `76407/100000` is `95237238332197230887802000370977/15003513290475362588580531432700000000`.

## 3. Analytic proof obligations behind the count bounds

### Original constant 8

Theorem `thm:transfer` requires a proved quantitative Chen input and the bad-count upper bound. The latter depends on:

- prime number theorem and partial summation for the semiprime mass;
- Siegel–Walfisz uniformity for interval-restricted prime sequences;
- the stated generalized Bombieri–Vinogradov convolution theorem, strictly below level `1/2`;
- curved-region rectangle bracketing and uniform boundary/discrepancy estimates;
- Mertens/sieve-product asymptotics and the one-sided dimension bound;
- the specific linear upper sieve with controlled well-factorable errors.

Only after these steps may the fixed `θ<1/2` estimates be taken to their supremum. Do not insert an endpoint distribution theorem at `θ=1/2` or interchange construction and asymptotic limits silently.

### Improved constant 6.786 and separate Chen coefficient 1.8271

The final theorem depends on much more than arithmetic:

- the complete eleven-term Chen weight and all its multiplicities;
- the fixed-prime-prefix and shifted finite-prime-product distribution interfaces;
- admissible factorization/level gates, including the manuscript's two-factor and selected-subproduct repairs;
- extended first stop, variable third-prefix decisions, legal fourth/fifth descendant decisions and odd first exits;
- restricted lower sieve followed by Buchstab subtraction;
- original fourth boxes, fully disjoint fourth-tail supplement, and a fifth-prefix comparison valid over the actual partially refined tree;
- a proved kernel lower bound for each retained box, an integral interpretation of its rational volume, and correct order of compact trimming/buffering limits;
- the first narrow correction plus the distinct second correction block, including the repaired second-seed functional, its Buchstab envelope, unit-quotient masses, and fixed-positive-cutoff extension.

The correction intervals `(31/200,4/25)` and `(29/200,3/20)` are disjoint. The new second contribution `112/837495` **replaces** `56/465275`; the old and new versions cannot be added. The seed proof intentionally retains the old positive cap `6.81`; stronger new-cap extensions must not be presumed.

These interfaces should become separate propositions with all ranges and uniformity quantified, and proofs or explicit unresolved status. A structure field that simply assumes the desired bound is a useful contract, but is not an instance or a proof of the manuscript.

## 4. Missing computational evidence

The TeX states final fractions but does not include the certificate implementations, full box streams or interval traces. At minimum recover:

- `certify_extended_prefix.py` plus its exact enclosure and sieve-function table data; the cited calculation uses two million subdivisions and the full small-third-prime tail;
- `certify_fourth_prefix_K_refinement.py` and companion data: 483,089 retained boxes out of 9,381,251;
- corrected fourth-tail certificate/replay data: 295,979 new boxes, excluding **all** 483,089 old selected cells;
- `certify_fifth_prefix_K_refinement.py` and companion data: 149,251 retained boxes out of 12,103,014;
- original outward eleven-term table, lower-prefix Buchstab certificates and logarithm/sieve-function enclosures;
- first one-step correction certificate, repaired second-seed implementation/replay, and `certify_second_seed_omega_envelope.py` with its 80-bit interval primitives and 8,192-cell Darboux data.

For a kernel-level checker, external programs may generate candidates, but Lean must validate every selected branch's admissibility, rational inequality, rounding direction, disjointness and sum, with proved real-analysis interpretation. A digest proves neither geometric validity nor an integral bound. Full enumeration of rejected cells is unnecessary for a lower bound if all selected cells are supplied, valid, disjoint, and their sum is verified. Chunking the selected stream will be more manageable than replaying millions of candidate boxes inside one reduction. Do not use `native_decide` as if it were ordinary kernel reduction; disclose its trust implications or use proof-producing checking/reduction appropriate to the project's standard.

## 5. Verified library footholds and honest gap statement

Primary documentation checked on 2026-10-08:

- [Natural prime factor lists](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Factors.html): prime factors, product recovery and uniqueness support the finite decomposition.
- [Finite-set cardinalities](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html): the finite combinatorial layer.
- [Real powers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html): rational-power bridge ingredients named above.
- [Exact logarithm upper-bound lemma](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Deriv.html#Real.log_div_le_sum_range_add): `Real.log_div_le_sum_range_add` and related series estimates.
- [Selberg sieve](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/SelbergSieve.html): basic upper-sieve setup, Λ² weights and diagonalization. This does **not** itself supply the manuscript's explicit linear/double-sieve estimates.
- [Prime Number Theorem+ project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd): relevant external formalization project to inspect at a pinned revision before reuse. A project title/blueprint is not evidence that each required quantitative theorem is proved without unresolved dependencies.

This bounded search did not locate verified drop-in proofs of the exact generalized distribution, Lichtman interfaces, or quantitative Chen statements required here. It does not establish that no such formalization exists. Pin Lean/mathlib/dependency revisions and inspect exact theorem types and transitive axioms before assigning “available” status.

## 6. Acceptance criteria

First milestone: a pinned, reproducible build of the finite core, logarithmic/numerical lemmas and honestly conditional transfer theorems; no `sorry`, `admit`, hidden research axioms, or renamed copies of the target in the completed modules. Check theorem statements against the manuscript, run the build, and inspect `#print axioms` on exported results, including dependencies. Standard Lean foundations such as choice/propext/quotient soundness are distinct from unproved analytic assertions.

Full completion: supply and verify all analytic inputs and certificate interpretations, instantiate the actual normalization and count bounds, and derive the eventual representation statements. The theorem remains about sufficiently large even integers and gives no effective cutoff. Nothing here proves all-even strong Goldbach, certifies novelty, or validates the manuscript's excluded floating diagnostics.
