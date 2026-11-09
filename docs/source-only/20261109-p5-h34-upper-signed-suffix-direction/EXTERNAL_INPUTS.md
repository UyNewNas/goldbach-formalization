# External inputs — P5.6 h34 upper physical signed suffix direction

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Toolchain Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**New external analytic inputs: NONE.** No PNT, Mertens, BV, or other classical analytic theorem is implemented or assumed.

Existing *finite*, manuscript-local interfaces reused in the new Lean module:
- `firstExitRetainedPolynomial_ordinaryParityRosser`: an exact equivalence of full and parity-safe retained polynomials on the same decreasing prime carrier, given `1<Q`, carrier primality, and (trivial for `lower=false`) lower-carrier bound. Applied in `physical_upper_suffix_eq_parity_safe_correction`.
- `firstExitRetainedPolynomial_eq_product_add_correction`: exact signed first-exit identity, used once for each actual upper policy to compare corrections.
- `firstExitCorrection_nonneg_of_even_retained`: generic finite positivity under every-even-step retained and `h(p)∈[0,1]`. Applied ONLY to `ordinaryParityRosserPolicy false Q` using `ordinaryParityRosserPolicy_upper_even`, never directly to unrestricted full-prefix policy.
- `mem_roughPrimeUniverse_prime`: primes on the actual finite carrier, used to derive the bounds of the genuine reciprocal-totient weight.
- Prior source-only `physicalFirstExcludedSuffix`, `physicalEulerBase`, `physical_upper_density_eq_euler_add_first_excluded` and `originalPhysicalQ` from the pinned h34 packet chain, consumed without treating it as compiled.

Still manuscript-internal and NOT outsourced: actual signed q/tag rejected-lane-to-first-exit correspondence, owner/selected filters, quantified payment, root multiplicity and U4 collisions, all-action CLOSED-CELL, feedback and seed, PP same-rho compatibility, native-history, common 430+11. The sign of the upper finite Euler correction does not establish the sign of the complete arithmetic/history mismatch. No new axioms or sorry/admit/unsafe/native proof escape.

Status: SOURCE_ONLY; declarations UNCOMPILED; kernel and transitive axioms UNAUDITED; finite guards UNEVALUATED; no green credit.
