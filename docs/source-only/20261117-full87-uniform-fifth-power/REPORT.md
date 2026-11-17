# P1.4 — actual fifth-parent uniform power cutoff (source-only)

Baseline: `0d61e92a2d722ae7584be8d810d921bc762a02e3`, branch `chatgpt/p1-full87-large-tail-invoice-20261117-1907`.
Task branch: `chatgpt/p1-full87-uniform-fifth-power-20261117-2014`.
Lean source: `P4AOriginalFull87UniformFifthPower.lean`; source commits `81f9c3ae8e26cf4354ed2b918eac8d8398ebd567`, then side-goal clarification `91e2f08c68a88de3e8806c853c7bddae0ed3483f`.

## Mathematical delta

The inherited fifth-power filter is indexed by the original PLUS-beta a: only `X^5 < a^5*b5^6` can survive for an actual fifthExclusive event. The actual nonzero `actualSmallRosserPlus` support proves the *strict* bound `(a : ℝ) < L`. We combine that real bound with the prior **actual** ordered-history rough modulus inequality `(b5*p6)^5 ≤ b5^6`, already supplied by `actual_highq_needs_large_fifth_weight` for original event membership, to obtain the stronger per-parent exclusion:

```
L^5 * (b5 : ℝ)^6 ≤ (X : ℝ)^5
  ⇒ for each genuine p6 in fifth.remainingAfter,
     attachedLeafTest PLUS (p6 :: fifth.selectedAfter) = 0
  ⇒ sixthPositiveContinuation ORIGINAL_POLICY fifth = 0.
```

The signed continuation can therefore be nonzero only if

```
(X : ℝ)^5 < L^5 * (b5 : ℝ)^6.
```

This no longer depends on any individual a or sixth prime; all original a and p occurrences and their coefficients remain untouched in the proof, and the claim is for the genuine `fifthExclusive` constructor from `actualFifthSixthWithoutBoth` within `sharedRankFour`. No mask is transferred to `sixthFromBoth`.

At frozen `X≥N^(3/5)`, `L=N^epsilon` and `epsilon≤1/500` (with `N>1`), this necessary region heuristically corresponds to `b5>N^(299/600)` at the maximum allowed epsilon, versus the existing fifth-admission upper `b5<N^(299/500)`. The exponent arithmetic is a **paper calculation only**, not a new formal Lean lemma or a numerical reserve. The resulting interval is nonempty; **this is not** a same-rho quantitative tail mass estimate or a new `H_N` saving.

## Proof bodies and boundaries

1. `actual_fifth_uniform_power_attached_zero`: unfolds the genuine Rosser finite sum; handles beta=0 separately; uses beta≠0 ⇒ a<L, the inherited *original-source* high-q fifth-power necessity, and strict high-q endpoint to discharge each summand.
2. `actual_fifth_uniform_power_continuation_zero`: zeroes the entire actual ordered post-fifth sixth carrier, for the unchanged signed mass and arbitrary admission R, by pointwise zero summands. No cardinality or cancellation assumption.
3. `actual_fifth_nonzero_continuation_forces_large_parent`: contraposes the uniform support lemma; nonzero implies strict large-parent inequality. No target-equivalent "tail smallness" assumption.

This packet does not re-prove PP/BV/Mertens/PNT, does not create a new event producer, and does not claim large-tail estimate, direct sixthFromBoth payment, general physical-rho level, actual 87 archive or two-reserve compatibility.

## Checks

- Read complete preceding REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and source, relevant fifth-rank power source and actual Rosser support in sixth-positive-carrier source, and frozen manuscript blob.
- Prior branch `0d61e92...` compared identical to previous branch ref before branching; independent task branch created from that exact SHA.
- Local `lean --version`, `lake --version`, `elan --version`: each exit code 127 (command not found). No local pinned mathlib/native dependency checkout; no compile attempted and no CI dispatched.
- Verification: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. Candidate tactics have NOT been elaborated or kernel checked, and may contain Lean errors. No transitive axiom inspection, independent review, or original numerical archive replay.
- No `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`, new external theorem or resource/toolchain upgrades in this packet.

Frozen: manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=`49044063/25000000`; K=`8452171/1250000`.

## Precise next action

Actual quantitative control of the *remaining* fifth-exclusive same-rho signed physical tail with `X^5<L^5 b5^6`, and independent direct `sixthFromBoth` terminal, within fixed N^theta level. Do **not** repackage the present support lemma as a saving or deduce signed monotonicity. The existing full-physical outside/producer/licensed-outside payments must stay once each. Before new work, test this source using matching pinned Lean/Lake if available, repair actual elaboration issues, and keep the task branch isolated. Parent P1.4 YELLOW.
