# P1.4 — active Rosser level localization of genuine high-q stopped terminals

## Baseline and owned scope
Actual previous handoff HEAD: `29291cdf03dd8dd5909668e8ecc331213ae3a9bb`, branch `chatgpt/p1-full87-first-disagreement-terminal-l1-20261109`, with REPORT, REGISTRY, INPUT_BOUNDARY, full 285-line source and HANDOFF read back. Its original source `d467ce507bef3b0f150cac7ceab67583ebcaf880` is preserved. This packet is an independent continuation: `chatgpt/p1-full87-active-rosser-level-20261109`, new Lean candidate `P4AOriginalFull87ActiveLevelHighProduct.lean`, source commit `1bde3d88b871cb7df5de0f749d80b1766ecd5374`, blob `926adf4fd572c0940d68e44f99146ca2f7462595`, 208 LF-terminated lines.

## NEW substantive internal mathematical fact
The existing actual source `ImbalancedChen/ActualSmallRosser.lean` contains `actualSmallRosserMinus_active` and `actualSmallRosserPlus_active`: if the ACTUAL sign-selected beta(a) is nonzero, its original level condition is STRICTLY `(a : ℝ) < L`, not just membership in the displayed divisor support. The actual physical test is STRICTLY `X < a * t.selected.prod`; since this product is a natural, the two inequalities force `(X : ℝ) < L * (t.selected.prod : ℝ)`. Consequently if `L * (t.selected.prod : ℝ) ≤ X`, each full-q beta*F summand vanishes, and so do both the true signed terminal and its original L1 charge.

The candidate Lean file constructs `highProductStoppedTerminals` by FILTERING the complete original `stoppedTerminals 8` list *after the original policy and post-candidate suffix have already been evaluated*. It provides an exact SIGNED equality of `stoppedTest 8` with the physical sum over only high-product occurrences, and an exact equality of the old `stoppedTerminalL1` invoice with the corresponding filtered invoice. This is not a new mask on retained eighth-level continuations. It does not alter beta, sign, multiplicity, original parent, or the first-disagreement cancellation. A separate candidate theorem shows any nonzero original stopped sum has an actual high-product stopped occurrence.

This removes provably zero contributions even when the displayed small-divisor support is large. It is a mathematically stronger cutoff than requiring explicit checks for every a in the displayed support. It does NOT establish a numerical bound on the remaining high-product occurrence population, an o(H_N) payment, or the archived saved87 gain. The full five frontier classes remain separate and unpaid.

## Exact verification
- GitHub original HEAD `29291cdf03dd8dd5909668e8ecc331213ae3a9bb` and all previous packet records were read before writing; pinned manuscript `9731290e8f53cffda44129906cde6a965eaa869b` and body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` reconfirmed.
- New branch created from `29291cdf03dd8dd5909668e8ecc331213ae3a9bb`. New source written on this branch, commit `1bde3d88b871cb7df5de0f749d80b1766ecd5374`. Remote source readback blob `926adf4fd572c0940d68e44f99146ca2f7462595` and line count 208 matched local `git hash-object`.
- Source check: five non-private candidate theorems, no sorry/admit/axiom/native_decide/unsafe. The source is not elaborated or kernel-checked.
- 2,500 deterministic exact-Fraction arithmetic cases for signed high-q and sign-selective beta supported below real L; 1,657 inactive selected-product cases, 697 nonzero signed cases, 0 counterexamples. NOT saved87 or Lean replay.
- Real execution environment: `bash -lc 'lean --version'`, `lake --version`, `elan --version`: each exit code 127, command not found. No installed Lean/Lake, no matching mathlib workspace. No build attempted; no installation, CI, Codex, resource changes, master modifications or merge.
- Validation: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Kernel replay, transitive axiom audit, original numerical archive authentication, independent review all ABSENT.

## Remaining obligations and concrete next step
1. Get a pre-equipped exact pinned Lean/Lake environment and stage the source-only import chain with the correct ImbalancedChen paths; actually compile this candidate and all prerequisites before any COMPILED claim. Compiler failure requires correction, not heuristic promotion.
2. Bound the REAL high-product stopped occurrence mass `X < L * selected.prod` for the original raw/licensed first-exclusive fifth/sixth/seventh histories, and pay it against the SAME physical rho_N/H_N and legal integer PP cutoff fixed before large N.
3. Discharge all 87 archived affine witnesses/dynamic parent/common history and real signed gain; five separate frontier invoices and raw/finite/filtered losses; primitive/centre/modulus/endpoint, ordinary residual integral, rank9, changed/tagged and separate compiler/density reserves.
4. External manuscript estimate remains REGISTERED_NOT_PROVED and unused. No claim of full P1.4 closure.

Pins unchanged: Lean leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958; c=49044063/25000000; K=8452171/1250000.
