# P1.4 — Actual changed-rough five-prime-factor power obstruction

**Parent P1.4: YELLOW. Proof status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED.**

## Frozen recovery and source
- Resumed verified previous HEAD `f8188e3ed66416ae4d2e3a259653d289d1e2c661` from branch `chatgpt/p1-full87-changed-rough-five-factors-20261120-1410`. Read previous REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and the complete 167-line Lean candidate, predecessor causal witness and symmetric-difference physical density source.
- Checked existing `FixedRoughCoefficients`, `RoughPrimeUniverse`, `SmallRoughAttachment`, `P1SignedExitPartition`, `P1SignedExitPolicyComparison`, `P1SignedExitCoefficientDifference`, and real `ChenInitialPrimeSource`. These do **not** already prove the five-factor real scale obstruction below.
- New source `P1Full87ChangedRoughLevelObstruction.lean` (131 lines), blob `0cad8eda1941942821b75aa91545adf637d9a54e`, source commit `a44f6fe9a632074dc0a6ed54d390ed55d88ed237`, independent branch `chatgpt/p1-full87-changed-rough-level-obstruction-20261120-1510`. This imports the previous candidate by its staged Lean module name; the source-only import closure remains unstaged.

## New candidate finite arithmetic inference
Let `R` be the unchanged `P4AOriginalFull87CompleteSixthDispatch.policy` and `S` the unchanged `P4AOriginalFull87LicensedSixthPolicy.policy`. For each **actual** rough modulus `b` in the symmetric difference of their fixed supports, the predecessor gives five distinct prime factors of `b`. Both original supports are squarefree, and each of those factors lies in the **same** literal `roughPrimeUniverse N cap w z`, hence satisfies the original inclusive threshold `w ≤ p`.

The new private proof uses `Nat.prod_primeFactors_of_squarefree` and the product comparison directly (no independent enumeration of occurrences). Conditional only on the numeric base condition `1 ≤ w`, it derives:

```text
w^5 ≤ w^(b.primeFactors.card)
    = ∏_{p ∈ b.primeFactors} w
   ≤ ∏_{p ∈ b.primeFactors} p
    = b.
```

Two public consequences specialize this to the genuine RAW/LICENSED changed supports and prove (i) `w^5 ≤ b`, (ii) for every integer level `B` with `B < w^5`, no changed rough modulus satisfies `b ≤ B`; the corresponding low-level filtered symmetric difference is empty. The cutoff comparison is strict, so equality at `B = w^5` is not excluded.

This is **not** a proof that the full physical small/rough product `q=a b` has cutoff `B`, nor that the manuscript's actual `w` and the code parameter are correctly identified. The manuscript's `rho_0=19/96` and `theta_*=599/1000` invite a separate parameter audit: **if** the code uses `w=N^rho_0` and the *same rough-difference* support is claimed to sit below `N^theta_*`, the scale inequality `5 rho_0=95/96 > 599/1000` would exclude every such changed modulus at sufficiently large `N`. No such parameter identification has been proved or assumed here. Treat this as a potential model/interface mismatch, not as a result about the published gain.

## Actual environment validation
- `lean --version`: exit 127 (`command not found`).
- `lake --version`: exit 127; `elan --version`: exit 127.
- `git --version`: 2.47.3. Memory cgroup `/sys/fs/cgroup/memory.max` = 4294967296 bytes.
- Source fetched back via GitHub with Blob `0cad8eda1941942821b75aa91545adf637d9a54e`. Forbidden escapes scan for `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`: PASS. **Not** a Lean type-check or computation.
- No fixed Lean elaboration, kernel replay, transitive-axiom audit, independent review, or numerical archive authentication. No CI, Codex, force push, main/master write, dependency upgrade or resource increase.

## Concrete next action
1. In a *permitted existing* pinned Lean environment, stage the exact source-only import closure (previous five-factors, causal witness, symmetric-density sources) under `ImbalancedChen/` and type-check; repair errors without changing pins.
2. Check the actual meaning of `w` against the frozen manuscript's small-prime presieve cutoff and physical `theta_*` level **before** using the fifth-power obstruction to remove any density or signed-gain term. A mismatch invalidates that reduction.
3. Continue classification of the actual odd first disagreement at ranks 5/7/9/greater and real ancestor/current parent; match the literal changed/tagged/BOTH/inherited 87 occurrence ledger without erasing multiplicities.
4. Then connect the same ordinary residual integral and quantitative `H_N` losses, with outside net, stopped states, producer invoice, both separate reserves and the LICENSED same-`rho_N` smooth PP permission still open.
