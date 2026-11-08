# P5.6 / h34 — original U3/U4 q-fibre weighted true H430 lookup

Date: 2026-11-08 UTC. Dedicated branch: `chatgpt/p5-h34-request-admission-20261105`.
Actual incoming remote HEAD: `7aa34641e9473f5d10274ba4eb67d5917c9a852f`; mathematics commit: `0a65a12a3330dd20c80bfb828bebe8ac003dc553`.
Lean source blob: `f84b7ea8cfff4815d99b443254292d367351365b`.
**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED.**

Pinned manuscript (UNCHANGED): `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Its “Finite defects and actual descendants” defines averaged positive-family Theta and its “selected eleven occurrences” uses a negative 1/4 for each true U3/U4 upper label. Toolchain unchanged: Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

## Mathematical change (189 lines, two definitions, four public candidate theorems, one private helper)

`Part5OriginalH430QFibreWeightedTrueLookup.lean` adds the genuine original quotient-fibre sum
`originalQFibreWeight N w p = ∑ q ∈ originalReceiver N p, w ⟨p,q⟩`.
Here **w can depend on q AND on the U3/U4 tag**, and can be signed. A coefficient lookup at p is not declared to be the true integer receiver count or Theta weight.

- `original_signed_q_source_by_prime_fibres`: disintegrates the actual original U3-exclusive and U4-overlap tagged receipts, retaining distinct q positions and different w3/w4 values.
- `original_weighted_true_H430_by_q_fibres`: reindexes their genuine H430 source lookup by the original prime p, multiplying the actual q-fibre weight. Uses the true U4 main-envelope equality `U3_eq_main_on_U4` on the original [a,59/250) band. The result is
  `∑_{p∈U3-only} C3(t_p) W3(p) + ∑_{p∈U4} C4(t_p)(W3(p)+W4(p))`.
  This does NOT identify the two tags with separate historical Fin positions.
- `original_weighted_true_H430_signed_quarter`: retains the literal -1/4 for EACH original upper label without assuming weight positivity.
- `original_U34_real_count_by_q_fibres`: the ACTUAL original integer U3+U4 count has q-fibre multiplicities `#q`: exclusive plus TWO copies in U4. This cardinal identity is a distinct object from the H430 lookup.

This is not a repeat of the previous `OriginalU34AnalyticLookup` sum of one coefficient for every tagged q. The new statement permits arbitrary **q-dependent** arithmetic/analytic mark weights, necessary to state an eventual positive-family Theta comparison without replacing `σ(B) C(BN)/(φ(B)log(Q/B))` by a cardinality. The exact Theta weight and physical owner remain to be instantiated.

## Critical unclosed obligations

1. Identify the fixed manuscript's actual upper H430 selected-count consumer, physical z0 and real full/selected/inherited owner/depth. A p-fibre lookup is neither an owner nor a count inequality.
2. Establish the legitimate **averaged positive marked family** source-to-Theta estimate with the real q-dependent normalization, thresholds, polarity and frozen common Q; only then transfer the true H430 coefficient into the original selected arithmetic count. No finite H430 lookup sum is asserted equal to its continuous integral.
3. Retain the double U4 source and cross-q collisions; pay root weights and complete one-sided signed Euler first-excluded differences, six rejection lanes, and all historical occurrence multiplicities.
4. Finish the request-level all-action CLOSED-CELL predecessor induction, base/switched/seed/floor, Buchstab/retention consumption, feedback rounding-to-integral, manuscript-local PP/same-rho, native-history proper/equality/inherited mass and common nested 430+11 causal refinement with original c/K, 7/2 and 12.
5. Stage/install and compile the held source chain, kernel-replay, audit transitive axioms and evaluate numerical430 finite guards. No green claim.

## Verification and ownership

The math source commit was created from the **actual** `7aa34641` branch head with a non-forced, expected-SHA guarded fast-forward. Its blob was remotely read back and compare verified exactly one new h34 Lean source file, 189 additions, zero deletions. Simple forbidden-proof-token/source-content checks were performed; **no Lean parser, elaborator, compiler, kernel, axiom audit, independent review, numerical430 replay or CI dispatch was performed**. Numerical430 and inherited finite guard status remains **UNEVALUATED**.

No production/P1.4/P3.6 source, other owner directory, manuscript, workflow, dependency or toolchain was changed. The latest remote HEAD must be read back after metadata commit. Next: use the actual q-fibre weighted expression to identify the genuine source-to-Theta **inequality** and count owner, not a fabricated equality or another unweighted q-sum.

**完整h34稿内证明仍未闭合。**
