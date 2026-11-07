# P5.6 → h34 — selected root p versus quotient first obstruction in the complete N-P prime prefix

Date: 2026-11-06 UTC. Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-request-admission-20261105`. Actual handoff HEAD: `41a9aa72597fc72fd6b5f85e0df37a918b2b8704`.
Source commits: `da3f850b028b4a7c0364e223d99428d41b95388f` followed by source-only local variable binding correction `a05ba407bf85b226dad8adbe94c71bb11d4980ea`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (UNCHANGED).
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT**.

## The new manuscript-internal proof candidates

One new Lean file, `Part5OriginalH430JointPrimePrefix.lean` (238 lines, 13 theorem declarations, 1 noncomputable definition). It imports the predecessor `Part5OriginalH430FirstObstructionPrefix`, retaining the original tagged U3/U4 arithmetic data and exact frozen and original cutoffs. The previous packet identified the least prime of the *quotient* q. This packet restores the chosen original prime p to the complete integer N-P = p*q.

- `raw_tagged_band`, `raw_tagged_root_prime`: raw, including rejected, U3/U4-labelled receipts retain the original chosen prime p and its genuine primality from the original selector. This is **not** a feedback-history prime certificate invented by assumption.
- `raw_tagged_product`: the original quotient equation is exactly `p*q=N-P`; it is recovered using the existing raw source divisibility and integer division identity. No primality of the quotient q is asserted.
- `min_root_and_quotient_first_prime`: given a genuine prime p and an actual rejected q with least prime factor ell, `min(p,ell)` is prime, divides `p*q`, and is <= **every** prime divisor of `p*q`. The proof explicitly distinguishes a prime dividing p from one dividing q; it does not use the value of a feedback root mark.
- `jointFirstPrime`, `joint_first_prime_spec`: instantiate that minimum on the *same* tagged additive prime P, thus obtain the exact least prime divisor of the actual `N-P` when the quotient is rejected.
- `no_prime_before_joint_on_difference`, `root_precedes_quotient_obstruction`, `quotient_obstruction_precedes_root`, `joint_owner_order_split`: rule out all earlier prime divisors and distinguish when p is earlier versus when ell is earlier, assigning the equality case only once.
- `frozen_only_joint_prime_spec`, `rejected_frozen_joint_prime_spec`, and both `...joint_prefix_clear` declarations: specialize to BOTH actual arithmetic rejection channels, keeping the original or frozen physical cutoff respectively. Both preserve the U3/U4 tag, p, integer q, additive P and the distinct lane identities.

**Mathematical distinction:** `ell=minPrime(q)` alone is NOT in general the first prime divisor of N-P. The complete arithmetic first divisor is `min(p,ell)`. It is still NOT the manuscript's historical first-*excluded* prefix owner: manuscript first-exit depends on retained-prefix history, cap/cube tests, parity and signs. The present packet proves no identification of that causal owner, no full/selected/inherited filter matching, and no count or feedback equivalence.

The pinned manuscript's ordinary upper odd first-exit and lower even first-exit identities appear in `paper/source/manuscript-body.tex` around lines 377–391 and 694–716, and the finite positive-feedback and common refinement around lines 790–877. Nothing is reclassified as external because the manuscript itself must supply these causal compatibilities.

## Exact outstanding internal obligations

1. From the pinned real historical policy, compare its *first excluded* prefix with `min(p,ell)`; explicitly handle the case p precedes ell, ties, the actual retained cap, first-exit rank/parity/sign, all full/selected/inherited gates, and unique owner **per tagged occurrence**. Do NOT equate the global least divisor with a sieve exit without proof.
2. Identify true raw U3/U4 selected-count root weights and multiplicities, and pay signed `frozenOnly` and `rejectedFrozen` rejection masses. A root mark one does not count all q.
3. Prove complete all-action request-level CLOSED-CELL arithmetic induction, all ordinary/fixed/switched/seed/floor payments, request Buchstab/retention, and actual row/base compatibility.
4. Complete manuscript-local PP/same-rho, feedback weights to integrals, native-history quality, outer integral—Theta—count correspondence and one joint causal 430+11 refinement at unchanged c/K, root norm 7/2, row norm 12, true alpha and frozen same-Q.
5. Install under the original pinned Lean toolchain, elaborate, compile, kernel replay, audit transitive axioms and independently replay finite guards and numerical430. Neither this nor inherited source-only candidates receive formal credit before these gates.

## Validation / ownership / next action

Repository push permission verified and h34 branch not protected; remote branch head was `41a9aa72597fc72fd6b5f85e0df37a918b2b8704` immediately before creation. Only this new h34 source was created and then locally corrected. No P1.4/P3.6, existing production modules, other task paths, CI files, dependency versions or manuscript files were modified. No force push, merge or CI dispatch.

Text-level forbidden-placeholder and delimiter checks were performed before the source commit; the subsequent correction prevents shadowing a prime hypothesis with raw-membership evidence. This does **not** certify Lean parsing, elaboration, kernel checking or mathematical truth. The repaired source blob is `3a116b52c23ab3f9db13d0477eb77d88c4e122dc`. Lean/Lake executables were unavailable; finite guards remain `UNEVALUATED`.

**Next concrete action:** read the original retained-prefix selector and its first-excluded edge enumeration in the fixed manuscript/Lean mapping. Match actual `jointFirstPrime z cut = min(p,ell)` against the FIRST HISTORICALLY EXCLUDED prefix, or explicitly show the mismatch, retaining the physical tag, rank, parity, signed mass, q multiplicities and owner. Do not promote this arithmetic minimum as a causal exit theorem without those proofs.

**Complete manuscript-internal h34 remains OPEN.**
