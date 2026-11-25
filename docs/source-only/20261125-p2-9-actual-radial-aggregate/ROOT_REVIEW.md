# Independent root review: actual U4 radial aggregate

Reviewed source blob: `93062adda7fdc87780a9c684c046652c567558d9`.
SHA256: `7683ad34324d753af07709b5b1b0f12a77b836c3e07aabb5ec58e808e446c713`.
Scope: static source and manuscript-boundary review only. The candidate has not been compiled; formal/kernel/endpoint credit remains zero.

## Source and reuse checks

The entire 638-line candidate was read. Its original 554-line proof body is unchanged by the 84-line all-depth extension. No sorry, admit, axiom, native_decide or unsafe token occurs in executable source.

The two existing finite-history suppliers were independently read at their original repository blobs:
- `Part5OriginalH430EmittedPathMultiplicity`, blob `a80bc00166667c4873121a22464541e123898147`.
- `Part5OriginalH430EmittedWordBox`, blob `f14948c46180277d22c4f466de18772e06535aef`.

Their coefficient bound is a bound on positive marks. The old subsum proof first proves nonnegativity from mark_pos, then uses the no-repeated-itinerary result and rootHistory_itinerary_mass_le_one. It does not obtain the bound through cancellation of signed coefficients. The old word equals the root prime followed by the existing letters of the path, so fixing the whole word fixes that prime. The empty-word case contributes zero.

The pinned Mathlib APIs Fin.sum_ofFn, List.ofFn_get and List.ofFn_getElem_eq_map were checked in mathlib4@e4c91783ca8e6a7c693ae624ade32fd22d4e43c1. This is a static API check, not evidence that every elaboration step succeeds.

## Quantifier and counting checks

- The original originalBand, p-dependent LevelIndex subfamily B, levelMark and complete old word remain literal.
- The tuple prefix preserves the first k old coordinates; the two fresh coordinates and all r tail coordinates are retained.
- RootQ is replaced by the old cellQ only under actual membership in the original root cell.
- Reordering finite sums preserves positive multiplicities. No injectivity of the product map is assumed.
- The coefficient bound is proved before applying the radial bound. It is not an extra hypothesis.
- Shapes, RootCode n and the original bounded rank splits are finite and fixed before N. The proof uses epsilon/(aggregateCard n + 1); it does not pay epsilon separately for each moving prime or history position.
- The final all-depth result uses epsilon/431 before choosing h. The same h and the same large-N threshold then apply to every t and every dependent B dep p. The finite depth factor comes from the original 430-fuel history.
- No enormous finite rank or shape enumeration is evaluated.

## Exact equality and remaining boundary

selectedProfileMass_split is an exact identity over the same bounded prime-tuple carrier and the same raw marks: the full selected profile sum equals its M <= N part plus its natural outer sum. Equality M = N belongs to the inner term. The all-depth identity sums this same equality over Fin 431.

The selected profile sums retain discrete history-selection coefficients. The candidate does not prove those coefficients form a globally smooth admitted finite family. It does not identify the inner smooth term with original ordinaryBad, remove thetaConversion, establish converted/J bounds, or apply the prime-product distribution theorem. Summing all depth budgets does not assert a new simultaneous sharp counting interpretation for all generations.

The source uses already existing history theorems rather than re-proving their mathematical content. Their full selected import closure, the selected original owner postimages, and any receiving producer/import bindings still require qualification before compilation. The three accepted radial thin modules are unchanged.

A separate agent independently reviewed both the main candidate and the all-depth increment, with the same source-only conclusion and no critical or important mathematical defect identified.
