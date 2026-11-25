# P2.9: actual selected-history radial aggregation

**Status: SOURCE_ONLY_UNCOMPILED. New formal credit: 0. New kernel credit: 0.**

This package supplies a finite, positive, occurrence-preserving aggregation of the existing Gamma5 radial payment over the original U4 root-prime and selected-history indices. It also pays the sum over the fixed 431 remaining-depth slots. The width and the large-N threshold are chosen before any moving root prime, position subfamily, or depth selection.

The new source is `ImbalancedChen/P2FiniteMarkedGamma5ActualRadialAggregate.lean`. Its exact blob is `93062adda7fdc87780a9c684c046652c567558d9`; UTF-8 SHA256 is `7683ad34324d753af07709b5b1b0f12a77b836c3e07aabb5ec58e808e446c713` (27,200 bytes, 638 lines). It imports the existing actual root-cell dictionary, natural radial mass, and original emitted-history multiplicity source.

## Exact conclusion and its scope

For fixed root precision `n` and every positive epsilon, the source proves that one fixed `0 < h <= 1/8`, with `width = log(1+h)`, eventually pays

```text
(log N / N) *
  (allDepthSelectedProfileMass N n t h B
   - allDepthSelectedInnerMass N n t h B)
<= epsilon
```

uniformly in `t` and in the original dependent families

```lean
B : (dep : Fin 431) -> (p : Nat) ->
  Finset (LevelIndex N n .U4 t p dep.val)
```

The final public theorem is `absolute_all_depth_selected_profile_excess_payment`. The intermediate single-depth theorem quantifies over all `dep : Nat` with one common threshold. The final theorem additionally sums all `dep : Fin 431`, charging the fixed factor 431 before N.

The three `selected*` quantities are a raw marked profile extension and its exact radial partition. They use the literal original `originalBand N .U4`, `B p`, `LevelIndex`, `levelMark`, old word, and root Q. The inner term is the same profile restricted by the complete-product condition `M <= N`; the outer term is its `M > N` part. The boundary `M = N` belongs to the inner term.

They are not definitions of the old `ordinaryBad`, `markedConverted`, `markedTheta`, or J. No theta-conversion coefficient is silently discarded: the theorem is explicitly about raw ordinary `levelMark` weights. Identifying the inner smooth restrictions with the original sharp Gamma5 count and preserving the original conversion/normalization is a separate task.

The all-depth sum is a finite error budget over the original depth slots. It does not assert that every generation is simultaneously the original counting source.

## Why the moving history does not multiply epsilon

1. `level_shape_sum_le` expands an arbitrary positive level subfamily into the original filtered list of occurrences, then into the original `rootHistory`. It uses `mark_pos`, not cancellation or an absolute value of a signed sum.
2. The existing `actual_shape_word_mark` gives the fixed-shape, fixed-old-word positive coefficient bound. Its original proof uses `history_itinerary_nodup` and the positive itinerary mass bound. This package does not reprove those theorems.
3. The existing `occurrence_old` identifies the full old word as `p :: letters path`. Thus a fixed old word fixes p, and the entire root-prime/position coefficient for one shape is at most one. The empty old word has coefficient zero.
4. The original history has fuel 430. Its theorem `rootHistory_computed_data` gives `remaining + path.length = 430`; `levelOccurrence_source` identifies the remaining value with the level index. Hence the finite shape set contains all paths, and `Fin 431` contains every nonempty original level.
5. Original root primes are grouped by `originalRootCellBand`. On each cell, `originalRootCellBand_Q` gives `rootQ = cellQ`, using the already existing `codeLevel_rootCode` dictionary. There is no new differentiation of root Q and no exchange of a varying-p family with a single global smooth family.
6. The full tuple keeps all k old slots first, followed by the two fresh slots and all r tail slots. Its prefix is required to equal the literal original old word. No coordinate is sorted, identified, or discarded.
7. The finite coefficient bound is paid once with
   `C(n) = #shapeWords * #RootCode n * #Split`,
   where `Split = Fin(K+1) x Fin(K+1)` and K is the original `frozenSourceRankBound`. Only `k + 2 + r <= K` splits contribute. These factors are fixed before N. The existing `absolute_natural_outer_payment` receives epsilon divided by `C(n)+1`; the all-depth corollary first divides epsilon by 431.

The source does not ask callers for a fibre bound, a positive coefficient bound, a target payment, a global smoothing theorem, or a J estimate.

## Exact dictionaries retained

- `outerSlice_eq_bounded_outer` transports the old-word restriction through the existing injective natural-coordinate image. It removes only zero profile values.
- `boundedProfileSlice_split` is the exact `M <= N` / `M > N` partition on the same `Part3.labelledPrimeTuples rank (2*N)` enumerator.
- `selectedProfileMass_split` keeps the original p and dependent position sums on both sides.
- `selectedOuterMass_eq_cells` changes Q only after membership in the original root cell.
- `selectedOuterMass_eq_prefix_sum` is the exact finite coefficient dictionary, retaining every list occurrence and its positive mark.
- `allDepthSelectedProfileMass_split` sums the preceding identity over the fixed original depth range.

The existing radial natural-mass theorem covers the whole nonzero natural prime outer support at large N by the bounded enumerator. This package reuses that support dictionary; it does not give a new equality with an unbounded original-history or J sum.

The original K is reused under its original FQN. Sharp-source rank inclusion is already supplied by `P2FiniteMarkedGamma5ActualRank.enhanced_position_source_rank`; it is not reproved here. This file's new mass definitions explicitly use bounded splits and do not claim the missing sharp-source/smooth-inner equality. Zero old rank remains in the ambient enumeration and contributes no actual U4 prefix; an empty tail, repeated factors, empty B, and zero mass are retained. No cardinal sum involving the very large K is evaluated.

## Reused source inputs

Full paths, Git blobs, SHA256 values, imports and selection rules are in `REGISTRY.json`.

| Source | Exact existing input used |
| --- | --- |
| `P2FiniteMarkedGamma5ActualRootCells` | Blob `88dcd460198c101d181267599b8666247f738e5f`; original cell band and its Q equality |
| `P2FiniteMarkedGamma5RadialNaturalMass` | Blob `6d51477d988bd87c2d9ca90995b09bc65742fdfd`; natural image, injectivity, uniform outer payment |
| `Part5OriginalH430EmittedWordBox` | Blob `f14948c46180277d22c4f466de18772e06535aef`; original old-word reconstruction and positive shape/word bound |
| `Part5OriginalH430EmittedPathMultiplicity` | Blob `a80bc00166667c4873121a22464541e123898147`; original no-duplicate itinerary proof, unchanged |
| `Part5OriginalH430RequestedHistory` | Blob `9103005991a106805aea773e1039af040c0e9c4a`; original lists, marks, dependent positions and depth range |
| `P2FiniteMarkedGamma5PhysicalExtension` | Blob `2f776e2b4f9d5125b1df887d0e5da01e2c52dd1b`; original profile bounds |
| `P2FiniteMarkedGamma5FrozenConstants` | Blob `2bd068f48afb9d7f083491bcb0f056692283d8f2`; unchanged original floor/rank FQNs |

The T23 emitted-word supplier also imports its existing absolute-word-box and owned-word modules. Their exact source bytes are registered, although those analytic normalization results are not used as a Gamma5 distribution theorem. In particular, `uniform_emitted_box` and `uniform_wordBox_normalization` concern their stated theta arithmetic normalization, not a general positive-prime-product or J licence.

## Source selection and qualification boundary

Use the inherited source selection in
`docs/source-only/20261125-p2-actual-small-payment/SOURCE_INSTALL_MANIFEST.json`
(blob `b7c93742331aad2d433b3fd02f836726d0ff5a33`), supplemented by the exact T23 sources and the existing radial/root-cell sources registered here.

The old history closure and the thin constant modules retain the same original FQNs. Select the already recorded `FrozenRootRefinement` postimage instead of its preimage. If `ActualRank` or `ClassicalFixedClampGeometry` is present in the combined closure, use the corresponding existing radial postimage as well. Preserve the prior history owner postimages for `HistoryQuotientCounts`, `TaggedArithmeticReceivers`, and `SeedHistoryMass`. This increment edits none of those owners.

The old 764-node selection does not by itself include the additional T23 chain. Its `OwnedMemberMass` imports `Part5OriginalH430RealizedBuchstabSupply`, which is not selected by that old manifest; the complete combined selection has not been reconstructed or qualified by this task. Existing unresolved import selections inherited from the root-cell package also remain recorded. This is a source-selection boundary, not a new mathematical premise in the aggregate theorem.

The already accepted three thin radial modules remain unchanged. Their existing acceptance does not qualify this new aggregate or permit unchecked combination with old history object files. A later controlled build must check a coherent full-history import variant and its complete outputs. No build, kernel replay, owned-declaration audit, or stock/runtime gate was run for this file.

## Manuscript provenance and duplicate check

The manuscript reference is `UyNewNas/chen-imbalanced-semiprimes` at
`a988cba584d803ae2856a0de50efb582f4f3dd6a`, under `paper/release-20261106/en/`.

- `argument.tex:359-374` states the fixed finite nonnegative labelled-prime-product setting, bounded rank/weights, positive floor, and ordinary unsifted mass.
- `argument.tex:400-407` allows positive outer approximation and places the large-N limit before the approximation-error limit.
- `sieve-appendix.tex:494-552` preserves the original common Q and selected old slots in the finite positive family.
- `sieve-appendix.tex:634-660` and `763-776` specify the original Gamma5 source and inclusive bad wall.
- `sieve-appendix.tex:1033-1066` and `1090-1101` retain original histories and fixed finite queries, positive lower bounds, and absolute errors.

This increment formalizes a finite positive aggregation omitted from those approximation statements. It supplies the radial portion only. It is not a new manuscript hypothesis and does not assert that the whole smooth-family/J argument is complete.

The search inspected the exact `a929011e...ac95824be770e85000bee243d65ec9c195c1d60b` branch delta and relevant T07/T21/T23 source-only consumers. T07's existing classical smooth accounting concerns Gamma9--21 with its own fixed constants; T21 gives exact smooth partitions; T23 already proves the itinerary coefficient bound. No existing consumer combining those actual history coefficients with the new `naturalOuterMass` was found. Those earlier results were reused, not reproved. Default-branch search alone was not treated as exhaustive evidence.

## Validation and remaining work

The original 554-line candidate was read independently by the root and review agents. The only subsequent source change appended the fixed-depth sum definitions and three theorems; the review agent separately checked those 84 added lines. The final Git blob was read back byte-for-byte and its SHA256 verified. A token scan found no `sorry`, `admit`, new axiom, `native_decide`, or `unsafe`. These are static source checks, with no new formal or kernel credit.

The substantive manuscript work still includes the inner smooth-to-sharp comparison with the original nonradial selections, uniform payment of any genuine nonradial walls, a single admissible smooth realization of the retained selection data, and the exact original ordinary/converted/J and prime-product interfaces. The existing sharp Gamma5 cost theorem and seed converted-mass identities must be reused when doing that work.

The 29 H247/native-Wu endpoints belong to an existing native Binder sufficient-condition/compatibility branch. Their semantic identification with the manuscript's actual enhanced finite-family conclusion has not been established. They are not entered as 29 necessary manuscript mainline obligations.
