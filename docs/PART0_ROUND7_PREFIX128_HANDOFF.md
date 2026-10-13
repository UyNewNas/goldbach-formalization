# Part 0 Round 7: adopted E0 Prefix128 integration (evidence-bound, root pending)

- P0 parent: `a1f5c160bf61e4177b22be44ffd31c76c26821d4`, branch `chatgpt/chen-p0-integration`.
- Fixed P2 production commit: `817d0da055d9ccd15b6461278f0201446bd28ee7`, branch `chatgpt/chen-p2-certificates`.
- Freeze: manuscript `ba6ec11d800eccc54406490631895e174de85766`; proof common baseline `1a80c1bcce67886f699d097fc37fd245cd3620bf`. The existing Lean, mathlib, goldbach and other dependency pins are unchanged.
- P2 source verification: [Part 2 certificates CI run 38338317790](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38338317790), job `115103375505`: **SUCCESS** on exactly `817d0da055d9ccd15b6461278f0201446bd28ee7`. Its archived logs contain the strict elaboration, original bundled leanchecker replay, and complete compiler declaration/transitive-axiom audit, with all 15 producer modules named. Artifact `part2-certificates-38338317790-1` (ID `11785933455`). The source and compiled-module identity must be checked anew in any new environment.
- Producer census: all 15 modules = 1,190 defining-module declarations, including generated/private. Newly imported P2 batch: Data **76**, Batch **219**, Prefix128 **186**, total **481**. P2's audited axiom whitelist remains `propext`, `Classical.choice`, `Quot.sound`. No claim that these producer records constitute a *P0 root* type export.
- P2's other 12 certificate modules match P0's parent tree byte-for-byte: all 12 Git blob SHA values were compared before reception.

## Immutable source identity and actual result

| Module | Original Git blob |
| --- | --- |
| `ImbalancedChen.Certificates.PairedV2Batch64To128Data` | `65aa7d4b5418e02f0e0db326efcd30ffe9cfcd1e` |
| `ImbalancedChen.Certificates.PairedV2Batch64To128` | `2fac5be361f4f580a0887c704f61aa04e8b313d5` |
| `ImbalancedChen.Certificates.PairedV2Prefix128` | `7828dcb47d62de548c011c2b0e30f13ff0699a75` |

These three original Git blobs are reused unchanged in the P0 tree and imported explicitly in `ImbalancedChen.lean`. Actual adopted E0 source ordinals `[64,128)` are appended to the already accepted `[0,64)`, preserving the first 128 rows, the source ordering, and the same physical `K/80` fourfold integral kernel. P2 proves real grid-key injectivity, disjoint source ordinal ranges, and `Prefix128.integral_eq_parts`; it does **not** assume geometric union-integral identities or a full arithmetic parent permit.

The exact real integral bound supplied by `ImbalancedChen.Certificates.PairedV2.Prefix128.integral_bounds` is
[
\frac{406911671777567}{10^{20}} \le \operatorname{Prefix128.integral} \le
\frac{406911907846016}{10^{20}} .
]
These are lower and upper bounds on the *128-row finite integral sum only*, not on the entire 17,572-row mask or on `hLower`.

## Remaining verification gates (DO NOT PREMARK AS SUCCESS)

1. This new **P0 integration SHA** requires full root `lake build`, original bundled `leanchecker` replay, global `ImbalancedChen` transitive axiom audit and existing Round3/Round4 compiler-type export, plus exact source/tool/object provenance. The earlier success on `a1f5c160bf61e4177b22be44ffd31c76c26821d4` cannot cover the new import.
2. P0 Round6 fifth-history compiler-type export (`verification/parts/p0/check_round6_types.py`, four modules, 70 declarations) is not yet wired into the required core workflow and has no P0 run receipt; a proposed workflow update was blocked by platform safety checks. Do not claim this gate passed.
3. The 481 new P2 declarations have producer-full compiler types, but a new-root-specific complete type export/receipt is still pending; root build, replay and axiom audit are distinct from that inventory. Retain all actual CI logs and exact SHA.
4. Still missing: the other adopted certificate rows `[128,17572)`, E1, saved-floor semantics, full historical arithmetic parent licensing, union coverage, actual distribution/error payments, shared rho density, full K/c ledger and both `hLower` / `hUpper`.

The conditional theorem `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds` has not had its hypotheses discharged. No manuscript change, proof-baseline change, axiom addition, or default-branch merge occurred. This handoff records an integration submission, not an unconditional theorem acceptance.
