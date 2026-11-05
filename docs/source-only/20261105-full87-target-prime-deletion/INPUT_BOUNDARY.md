# External-input boundary — fixed-rank target-prime deletion

The six candidate declarations in the new Lean file are elementary finite statements. Inputs already present in pinned mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1:
- `Nat.prod_primeFactors_dvd`: `(∏ p ∈ n.primeFactors, p) ∣ n`, `Mathlib/Data/Nat/Factorization/Basic.lean`.
- `Nat.prime_of_mem_primeFactors` and `Nat.mem_primeFactors`, same module/dependencies.
- `Finset.prod_le_prod_of_subset_of_one_le` and `Finset.prod_le_prod`, `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean`; `Finset.prod_nonneg`, `Finset.prod_le_one`, GroupWithZero Finset.
These specific actual source declarations were inspected against the mathlib *pinned source file* for product/density operations; no compiler/typecheck claim.

Manuscript source: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, lines 393–407, `g_N(p)=1_(p>2,p∤N)/(p-1)`, `g_0(p)=1_(p>2)/(p-1)`, excluded multiplier `prod_(p_last<=p<y,p|N)(1-g_0(p))`. The interval is implemented on literal `N.primeFactors`; lo>=3 ensures p>2.

EXTERNAL, REGISTERED ONLY, NOT IMPLEMENTED OR ASSUMED:
1. PNT/Mertens: normalization of V_N(y) to target-dependent singular factor; require target-uniform statement and actual y=N^u. Version/formal theorem not yet accepted. Proposed caller ordinary density-to-residual limit.
2. Ordinary linear-sieve parity Rosser positive exit-series and tail convergence: exact parity, fixed rank and s-range plus target uniformity; original manuscript §4 and Appendix upper; no complete formal source currently certified for this project. Proposed caller same ordinary continuation.
3. Moving-residue AP distribution for full-q primitive remainder: exact rho, modulus range, epsilon/eventual uniformity and Chen corrections not yet certified; not supplied by this finite target factor proof.

MANUSCRIPT INTERNAL, STILL OPEN: supply the actual square-test compact rank-j lo and prove uniform integer rounding/power-gap and N-threshold; integrate target deletion with the SAME signed original87 ordinary-source integral, real residual kernel and β; pay primitive/centre corrections, sixth filtering, saved87, the separate density/compiler reserves and final same-rho transfer.

No axiom, placeholder statement, imported external distribution proof, or conditional target asymptotic has been introduced.
