# P1.4 — actual nonzero upper-prime coefficient has original power-filtered witness

## Verified recovery and unchanged pins
- Task's previous remote HEAD and handoff read at `4b1deb6de2cb8d21b043f13801924ec25fd3d6f4` on `chatgpt/p1-full87-stopped-global-prime-ledger-20261118-2110`. Read full 313-line source, REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF, earlier PLUS-power filter source, previous Rosser prime-fibre, prime-source declarations, relevant earlier invoice reports and pinned manuscript. Root, docs and docs/source-only AGENTS.md absent; this packet is new with no AGENTS.
- Independent branch `chatgpt/p1-full87-upper-prime-actual-support-20261118-2206` created from exactly that verified SHA. No edits to older packet or main/master.
- Frozen manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, verified Git blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. PP retains the same signed rho on prime-product residue term and exact density, no extra arithmetic filter.
- Frozen Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`, c=`49044063/25000000`, K=`8452171/1250000`. GitHub `lean-toolchain` and `lake-manifest.json` were checked.

## Actual in-manuscript finite proof candidate
New `P4AOriginalFull87UpperPrimeActualSupport.lean`, 154 lines, source commit `29fd32e53cb9c30be4813588eaa51a0c943b87cc`, re-read Git blob `7ec0f1d7d4f2dbefc7d2c1ae87c19e4d2495f5dd`.

The predecessor defined a global original upper-half prime coefficient `C_N(P)` by summing the unchanged signed `sharedRankFour` state List and the unchanged receiver-generated actual fifth/sixth stopped event Lists. Previous work did not extract a **single genuine occurrence witness** from the nonzero global coefficient, including its original fifth-power Rosser filter.

The new theorem `actual_upper_prime_nonzero_has_power_filtered_witness` proves the following necessary-condition candidate, without adding a structure assumption:
`C_N(P) != 0` implies an original `sharedRankFour` state, an admitted actual `fifthExclusive` event with kind RAW-only or LICENSED-only, and a literal `p in fifth.remainingAfter`. With `b=(p::fifth.selectedAfter).prod` and `a=(N-P)/b`, it has:
- `2P < N` and `X < N-P` (strict).
- `a in actualSmallRosserSupport N cap w` and `a in largeFifthRosserIndices N cap w X fifth.selectedAfter`.
- `a*b=N-P` exactly (not a quotient rounding surrogate).
- `X^5 < a^5 * fifth.selectedAfter.prod^6` exactly (the original fifth-power retention).
- All state, event and sixth memberships are in the ORIGINAL ordered producers; no duplicated occurrence is removed.

The constructive argument only uses finite nonzero-sum occurrence extraction at three nested List levels and unpacks the original if-gate and `Finset.mem_filter`. Both/sixthFromBoth branches are excluded only for this precise stopped coefficient, as in its existing valuation. This theorem is necessary, not sufficient: cancellation may make a coefficient zero despite admitted occurrences. It does **not** show that the surviving P-support is sparse enough, that Rosser membership is smooth, or that PP can be applied. No new H_N bound or reserve payment follows. This narrows the EXACT next smoothing or independent arithmetic payment to a witnessed subset of the original physical event family.

## Actual checks and evidence
- Read back new source on remote branch: blob `7ec0f1d7d4f2dbefc7d2c1ae87c19e4d2495f5dd`, 154 lines, 7 text occurrences of `:= by`, forbidden escape tokens 0. Hash/static scans are not elaboration.
- This run: `lean --version` exit 127, `lake --version` exit 127, `elan --version` exit 127 (all `command not found`). No exact pinned local Lake closure. `/sys/fs/cgroup/memory.max` reads 4294967296 bytes, existing container setting, neither imposed nor changed. No compile was attempted after dependency failure.
- Validation: SOURCE_ONLY / UNEVALUATED / UNCOMPILED. KERNEL_REPLAYED=no; transitive axiom audit=no; independent review=no; real saved87 source/certificate replay=no.
- No new CI, Codex, toolchain upgrade, resource change, main/master mutation, merge or force push.

## Precise remaining yellow work
1. Prove that the original witnessed quotient/Rosser arithmetic filter is admitted by the frozen smooth PP **or** bound the exact global signed C_N(P) independently with SAME physical rho and H_N. A support implication alone does neither.
2. Pay unchanged lower-half primitive, modulus-prime and centre terms exactly once; source-map lower w vs upper z without equating rho0 to w.
3. Prove ordinary residual mean, original saved87 geometric/certificate authentication, actualParent coverage, RAW eighth / unfiltered sixth BOTH / rank9 / changed/tagged and two independent compiler/density reserves.
4. Stage the full source-only import closure at the fixed toolchain and repair any elaboration errors; separately replay kernel and audit axioms.

P1.4 parent YELLOW. No certified H_N improvement.
