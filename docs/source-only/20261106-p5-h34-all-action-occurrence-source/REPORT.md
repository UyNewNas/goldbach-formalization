# P5.6 → h34 — actual generated all-action occurrence source

**PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**

- Branch: `chatgpt/p5-h34-request-admission-20261105`.
- Verified preceding remote HEAD: `33e12cfc4b664df7883793b3d6fa4d5158d70e0b`.
- New source commits: `9be01b07e5106299f5e24098442232018fb76d32`
  (initial addition), `3699a6404aae21a5e5927bd902ec3b2b1075736a` (final source).
- New module: `Part5OriginalH430AllActionOccurrenceSource.lean`,
  214 lines, 8 uncompiled theorem bodies, 2 definitions; blob
  `690ea1b71cd1ca5c2bcb99440ec2905a9e9b6099`.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
  `paper/source/manuscript-body.tex` blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
- New source-only directory only. No production/P1.4/P3.6, dependencies,
  tooling, CI, default-branch, or manuscript modification.

## What changed mathematically

Previous `RequestedLevelBankSupply.sum_selectedLevel` partitions only
positions reading a chosen bank action. This packet advances the
**manuscript-internal actual request-level all-action source**, rather
than extending the conditional U3/U4 rank-one owner/presieve API.

`retainedLevel` and `buchstabLevel` are filters of the original
`LevelIndex` FIN positions at precisely remaining generation `g+1`.
`selected_choice_unique` and `choice_three_indicator` exploit the
literal `resolve (g+1)` and the previous table `iterate g`: each
resolved request chooses exactly one of retained, Buchstab or a specific
original 106-bank slot. The proof uses the *actual* `Request.mode`;
it does not replace specified-cell lookup by scalar closed-min selection.

`selected_retained_children` and `selected_retained_value` identify
the real unchanged-parent, specified-cell retention child and its
predecessor-table contribution. `selected_buchstab_children` identifies
the original strict prime-child carrier for the real upper/lower
polarity; it neither replaces that carrier by an approximate integral
nor silently asserts its analytic bound.

`level_action_partition` combines these with the existing
`sum_selectedLevel` to partition any signed function on ALL positions
of the actual generated level:

```
 sum_{l:LevelIndex} [resolved(l)] F(l)
    = sum_{retained positions} F(l)
    + sum_{Buchstab positions} F(l)
    + sum_{a:106 actions} sum_{selected-bank-a positions} F(l).
```

`exterior_level_value_zero` then uses the existing
`resolve_none_value` on the actual closed scalar read to remove only
unresolved zero-valued positions. The resulting
`full_level_action_source` is the same exact partition for
`F(l)=levelMark(l) * requestValue(iterate(g+1), current(l))`.
All repeated path positions and positive original path marks are
preserved; no root count weight is invented or divided out.

## Accuracy boundary

This is an EXACT request-level source identity candidate. It is
**not** an all-action CLOSED-CELL count inequality. In particular there
is not yet a quantitative retained/Buchstab supplier at the generated
request level; no base, fixed, switched, seed, floor or PP/same-rho
component is paid; the original U3/U4 selected-count source/root
weights/full/selected/inherited owner and rejection fibres remain open.
The source split is not the original arithmetic count identity.

This packet does not change the presieve-stage finding in the preceding
`PresieveExponentSeparation` packet: `omega<=a` was a conditional
obstruction to choosing original arithmetic p as an initial presieve
root, not an identified fixed manuscript parameter. Ordinary lower
trees starting at w=a,h are distinct from that projection.

Original c/K, root norm 7/2, row norm 12, true alpha, same Q,
physical closed-cell semantics and 430+11 budget are unchanged.

## Validation and next action

- Authenticated GitHub owner write permission and the actual h34
  dedicated branch were confirmed before the first file write.
- Remote SHA and blob were re-read; source diff from preceding HEAD
  contains only this new module at that checkpoint. A final remote
  HEAD and four-file diff must also be checked after the documents.
- Basic delimiter/forbidden-token and declaration-presence scan only.
  These are NOT parser/elaboration/kernel verification.
- Lean/Lake unavailable locally; no heavy compile, CI dispatch,
  kernel replay, transitive-axiom audit or finite numerical replay.
  All finite certifications remain **UNEVALUATED**.

**Next manuscript-internal action:** Starting with the exact all-action
source split, prove actual request-level retained and Buchstab
coefficient/Theta bounds under the same generated geometry, then
combine all three action families into the CLOSED-CELL predecessor
inequality. Do not claim that algebraic splitting itself pays any
Buchstab mass; do not swap specified-cell and scalar reads.
Separately resume true U3/U4 stage/owner matching (not the invalid
conditional initial-p presieve root), original root weights, complete
filters and rejection fibre multiplicities.

**Full manuscript-internal h34 remains OPEN.**
