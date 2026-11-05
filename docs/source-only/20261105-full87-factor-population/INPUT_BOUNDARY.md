# External-input boundary — P1.4 factor population

No analytic external theorem is introduced, assumed or implemented in this packet. Finite calculations use the existing exact prime prefix / coprime correction in `ImbalancedChen/ChenInitialPrimeSource.lean`, the preceding same-rho source modules, and the pinned Mathlib prime-factor interface.

**Existing formal library API (not a new analytic postulate):** Mathlib `Mathlib/Data/Nat/PrimeFin.lean`, `Nat.mem_primeFactors`, at mathlib commit `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` (Apache-2.0): `p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0`. Also `Nat.le_of_mem_primeFactors`. Used only to identify a finite prime-prefix filter with the actual distinct full-modulus prime factors, not to deliver a distribution bound. Exact module source examined; this new consumer has NOT been elaborated.

**Future external analytic inputs:** Ordinary linear-sieve limit / prime arithmetic progression distribution, PNT/Mertens etc. None consumed. Previously recorded only in `docs/source-only/20261105-full87-eighth-arithmetic/INPUT_BOUNDARY.md` and subsequent packets. Accurate versions/quantifiers/normalization still need matching before invocation. No replacement analytic axiom is permitted.

**Still internal:** common N and epsilon schedule, actual owner/trim and complete factor source, error normalization and o(1), same ordinary-continuation mean to residual-integral bridge, sixth-filter signed cost, saved numerical certificate mapping and two independent reserves.
