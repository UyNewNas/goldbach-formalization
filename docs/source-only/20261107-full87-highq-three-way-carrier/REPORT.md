# P1.4 actual full87 high-q three-way carrier triage

## Exact provenance
- Prior read-back HEAD: `2790edc6fd8d6a6dad85b105003f600123c3b0e0` on `chatgpt/p1-full87-highq-frontier-dominance-20261107`.
- This task branch: `chatgpt/p1-full87-highq-three-way-carrier-20261107`.
- New source commit: `61340eabfc37810ec38c6c5a607037d1f7d3b789`.
- New source: `P4AOriginalFull87HighQCarrierTriage.lean`, 293 lines; Git blob `9808de09e2a138364b9725366211bd8e6ac42597`.
- Frozen paper `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- Frozen Lean v4.33.0-rc1, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.

## New genuinely internal arithmetic obligation addressed (SOURCE CANDIDATE)
The previous packet proved the **forced-full** gate `X < s.selectedPrefix.prod` for a genuine owned eighth occurrence. It did not prove any local zero condition on the complementary population.

This packet proves a distinct **zero gate** from the actual full rough carrier, without changing the old/new policies. Define

```
carrierEnvelope(N, cap, X, w, s) :=
    ∀ a ∈ actualSmallRosserSupport(N,cap,w),
      a * (s.selectedPrefix.prod * s.remaining.prod) ≤ X
```

All `s.remaining` primes are recovered from the ACTUAL sixth-policy rank-eight frontier and are positive. For every possible terminal leaf, either a remaining prime is skipped or included; induction proves its full modulus remains ≤ the right-hand envelope. The original sign-sensitive small beta and all leaf signs are untouched. Thus, for **both** ordinary continuations at this very same state,

```
  signedTest(old, highQTest X F) = 0
  signedTest(new, highQTest X F) = 0
  ordinarySaving(old,new,highQTest X F,s) = 0.
```

The actual owned87 sixth-minus-eighth high-q difference is therefore exactly the sum of two NONOVERLAPPING populations in original list order:
1. **Forced-full**: `X < P8(s)`, whose high-q ordinary saving is its original unmasked signed saving.
2. **Unresolved mixed**: `¬(X < P8(s))` AND `¬carrierEnvelope(...,s)`, whose original high-q ordinary saving remains in full.

The third population `¬(X < P8(s)) ∧ carrierEnvelope(...,s)` has been removed by a **proof of exact arithmetic zero**, not by geometric measure zero. The predicates are applied only to existing `states` occurrences; no `toFinset`, no branch reassignment, no change of parent, mark, physical q, sign or small beta. At strict equality the first gate is false. These are finite identities, not estimates of the archive's numerical gain.

Caution: the all-unprocessed-prime product `s.remaining.prod` may be enormous, so this is a *safe but coarse* zero certificate. No claim that saved87 contains any zero-gate occurrences, no PP admission, no nonempty population, and no H_N tail smallness follow. The mixed high-q term remains completely unpaid.

## Verification conducted and not conducted
- Read the actual previous HEAD, REPORT/REGISTRY/INPUT_BOUNDARY/HANDOFF and entire 266-line predecessor source; read underlying original owned eighth source, full leaf invoice, rough/first-exit invariants, signed helper and Chen source; verified no AGENTS.md in the previous repository tree.
- Source was created as an actual Git blob and independently read back at its source commit, SHA `9808de09e2a138364b9725366211bd8e6ac42597`.
- Static forbidden-escape scan negative; simple parentheses count balanced. These are **not typechecking**.
- Independent deterministic *synthetic* Fraction arithmetic: 4,500 signed recursion samples (1,500 carrier-zero, 378 large-prefix) and 2,200 occurrence-list partition samples (590 forced-full, 4,730 proved-zero, 5,613 mixed occurrences), all zero contradictions. No original saved87 replay.
- **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No Lean/Lake, no kernel replay, no transitive axiom closure, no independent mathematical review, no CI dispatch, no Codex, no local machine, no extra compute and no reserve payment.

## Next exact obligation
The necessary next step is **not** more formal partition wrappers. Establish an actually useful *policy-dependent* upper envelope (which would need to replace the raw product of all remaining primes by a genuine bound on retained ordinary terminals), classify the original saved87 occurrences at the frozen physical PP threshold, and obtain H_N-relative quantitative control on both forced-full and unresolved mixed populations. Alternatively return to the original ordinary-continuation residual-integral identification and primitive signed PP adapter. Neither is proved in this source.
