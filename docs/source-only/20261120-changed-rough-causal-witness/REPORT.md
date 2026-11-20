# P1.4 — actual changed rough support has a causal post-four witness

Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. P1.4 parent is **YELLOW**.

## Verified recovery / exact identity

- Read the previous independently branched HEAD `8247476fbdd914977ca641af51c84b04183a4537`, its full `P1Full87TrueDRoughSymmDiffDensity.lean`, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF; checked the relevant `FixedRoughCoefficients`, `RetainedModuli`, `FirstExitTree`, `FirstExitGenericModuli`, `P1SignedExitCoefficientDifference`, `P1HistoricalBoundaryPolicyDifferenceSupport` and both actual full87 policies.
- New branch created from precisely the verified HEAD: `chatgpt/p1-full87-changed-rough-first-divergence-20261120-1310`; no changes to predecessor or main/master.
- New source: `docs/source-only/20261120-changed-rough-causal-witness/P1Full87ChangedRoughCausalWitness.lean`, 128 lines, blob `c5928515405cb2eb5bd5c30e8ae511bc69b191fe`; candidate source commit `b083985c5a096dff36b2a09fba18675050ffc7cf`.

## New candidate proof, not duplicated from existing P1 lemmas

For a changed rough modulus `b` in the symmetric difference of the actual ORIGINAL RAW and LICENSED retained rough supports, form the **same** decreasing `roughPrimeUniverse N cap w z` used by the physical density of both policies.

Existing `p1_policyCoefficientDifference_ne_zero_iff_mem_symmDifference` transfers that changed support to a nonzero coefficient difference; the pre-existing P1 common-admission first-disagreement theorem then supplies a real `p1SignedExitStates` state `s`, preserving its literal selected history and factor support. The new specialization of these two existing theorems proves:

- `s.positive = false`: the two odd-first-exit policies cannot disagree at an even positive branch.
- `4 < s.selectedPrefix.length`: both **actual** policies agree at every selected history of length at most four by `LicensedSixthPolicy.through_four_eq_raw`.
- `RAW false s.selectedPrefix ≠ LICENSED false s.selectedPrefix`: this is a **real** policy test disagreement, not a label, a free witness, or a target-equivalent structure field.
- `s.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z`, and **every** selected prime of `s` belongs to `b.primeFactors`.

This is one exact arithmetic/factor-history localization of the changed-carrier density discovered in the predecessor. It rules out assigning a changed rough modulus to an unrelated source, and localizes further 87-cell work to the first truly different odd test at rank >= 5. It does **not** show every such witness is rank 8 or owned by one of the 87 original cells; fifth/sixth, inherited, BOTH, rank9, and unchanged branches remain distinct obligations. No occurrence multiplicity is quotient-ed; the reused first-disagreement traversal consumes the existing actual history.

## Checks and limitations

- Read back the new GitHub source, blob `c5928515405cb2eb5bd5c30e8ae511bc69b191fe`; confirmed its import list, two candidate proof bodies, and absence of `axiom`, `sorry`, `admit`, `native_decide`, or `unsafe` proof escapes in source.
- Actual commands `lean --version`, `lake --version`, `elan --version`: all exit **127** (`command not found`). No installed elan toolchain, no mounted local repo/dependency cache, and `/sys/fs/cgroup/memory.max = 4294967296` bytes. No version-matched elaboration or compilation was possible. The import closure (including source-only `ImbalancedChen.P1Full87TrueDRoughSymmDiffDensity`) remains **UNSTAGED**.
- **UNEVALUATED** proof; static scan and Git blob readback are not kernel certification. No kernel replay, transitive-axiom audit, independent review or model evaluation of the full87 mathematical proof. No CI, Codex, resource increase, new analytic input, main write, merge or force push.
- Manuscript freeze unchanged: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Toolchain unchanged: Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000`.

## Remaining precise in-paper obligations / next step

1. In a fixed-pinned Lean environment install this source-only import closure in the matching `ImbalancedChen/` module paths and run `lake env lean`; repair actual elaboration failures before any COMPILED label.
2. Case split the actual first odd disagreement by its true selected rank 5, 7, 9, ... and its `rosserAncestor 4/5/6/8`, **then** connect every real rank-8 owned state to the literal 87-cell changed/tagged/BOTH/inherited actions. Do not infer owner membership just from the factor-history witness.
3. Connect the signed changed-rough density from the predecessor to its ordinary residual integral; keep raw/licensed outside net, producer invoice, fifth/sixth ordered stops and compiler versus density reserve separately, with one quantitative `H_N` charge for each real loss.
4. Authenticate the LICENSED physical `rho_N` as a causal coefficient for the *same* smooth PP `W_N`; the RAW and delta coefficients remain unlicensed and must not be substituted for the manuscript's admitted family.
5. Audit lower-half three corrections, saved original full87 numeric archive, kernel replay, transitive axioms and independent review.
