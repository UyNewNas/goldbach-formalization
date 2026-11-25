# Four Full87 interior expression candidates

**Status: SOURCE_ONLY.** Actual normal compilation, kernel checking, and
full-owned acceptance have not run for any of these four targets. The candidates
remain pending review of the actual Ascending retry. No successful Ascending
retry is used as evidence in this packet.

## Evidence and bounded changes

The actual 19-error diagnostic record belongs to
`P4AOriginalFull87AscendingAllInteriors`, in
`../batch13-repairs/LITERAL_FAILURES.json`. Its rational `decide` reduction,
untyped coefficient index, and local-let cast problems provide indirect evidence
for the same expression patterns in these four files. No target-specific error
log or diagnostic is attributed to them.

The candidates make only three enumerated changes:

1. Use the existing `decide +kernel` method in ten finite proof bodies.
2. Explicitly type nine coefficient indices as `j : Fin 8`, so `j.succ` indexes
   the original nine affine coefficients.
3. Use `Rat.cast_le` and bounded simplification at ten rational-to-real bridges.
   The simplification unfolds the existing local `a` and the required rational
   division, numeral, or absolute-value casts.

`P4AOriginalRemainingEighthSources` already uses the same kernel decision method
for finite rational coefficient equalities. It is part of the accepted
SourceDictionary source closure. The existing cast donors are
`P5U7OriginalRationalCellBounds` and `P2OriginalSixthSimplexBinding`.
`REPAIRS.json` records the exact donor hashes and ancestor-receipt reference;
ancestor acceptance does not accept these four owners.

The search of accessible source-selection, packet provenance, Git history, and
local acceptance JSONs found no repaired replacement or accepted target receipt
to reuse. The canonical preimages match the recorded original packet hashes and
source commit `220c14630ffd266f824bdbf0977147ecb740c0dd`. The old packet commit
`be2efd01c561080672e6c0ad0ba21638837afe4c` is unavailable locally; it was not
fetched or represented as independently reread.

## Candidate hashes and finite obligations

Every module name below has prefix `ImbalancedChen.P4AOriginalFull87`.

| Suffix | Margin predicates | Coefficient predicates | Candidate SHA256 |
| --- | ---: | ---: | --- |
| `H3Interiors` | 1,188 | 9,504 | `da04113fec3b8b80633b241a730abea2361ebd4dbbf6d6e2fff72f5fda29bdac` |
| `SeedNineFiftyInteriors` | 1,548 | 12,384 | `f43e6e4f2d5658fa078e50bedf73d97a5721c69a07bc03064964addb6d00eda2` |
| `H5H7Interiors` | 1,710 | 13,680 | `af29c737fdbd2e3cd7cad650af50dbf2e7a2db8dfb29e9dbe23a81438fb98252` |
| `DescAscPairInteriors` | 2,701 | 21,608 | `e0bc4dc4bb7ca0a2b1721b23224a2000def97e668006ff72acbbfc5a194f22a4` |

These are counts of the existing finite propositions, not completed validation
counts or measured runtime estimates. The 7,147 margin predicates and 57,176
coefficient predicates still require actual Lean elaboration and kernel
evaluation.

## Preserved mathematical contract

All point tables, row definitions, public theorem statements, family constants,
imports, and existing local options remain unchanged. The private
`affine_perturbation` header in each file only gains the explicit `Fin 8` type
already required by the original point domain and finite sum.

| Family | Centre margin | Box radius | Slope bound | Perturbation bound | Final row slack |
| --- | --- | --- | ---: | --- | --- |
| H3 | `9/1000000` | `1/100000000` | 6 | `3/6250000` | `1/125000` |
| Seed/Nine/Fifty | `7/10000` | `1/100000` | 6 | `3/6250` | `11/50000` |
| H5/H7 | `9/100000` | `1/1000000` | 5 | `1/25000` | `1/20000` |
| Descending/ascending-pair | `9/1000000` | `1/100000000` | 6 | `3/6250000` | `1/125000` |

Exact rational arithmetic confirms each perturbation is eight times the slope
bound times the radius, and the stated positive slack is no larger than the
centre margin minus that perturbation. This arithmetic check does not establish
the finite row predicates themselves.

The original family split remains `14 + 16`, `15`, `13`, and `12 + 17`, matching
the manuscript's `30 + 15 + 13 + 29 = 87` domains. The manuscript anchors at
commit `a988cba584d803ae2856a0de50efb582f4f3dd6a` are `argument.tex` 213–218,
`sieve-appendix.tex` 202–218, and `numerical-appendix.tex` 280–284. Original full
and selected-complement squares, ancestor tests, and source definitions remain
intact. The conclusions remain continuous-source interior statements; prime
realization, saved87 witness identity, numerical integrals, and P1 completion
are outside these theorems.

## Static verification and review

Fresh comparison against the fixed source commit confirmed exactly the
enumerated byte changes, with all 17 definition blocks and 15 public theorem
headers unchanged. All remaining declaration headers are unchanged except the
four private index annotations. Import and option lists match exactly, including
the existing local `maxRecDepth` and `maxHeartbeats` settings. No new assumption,
axiom, `sorry`, `admit`, or native decision method was introduced.

The compilation-review agent independently reviewed all four candidate hashes
and found no material issue with the finite goals, index types, rational cast
transport, or preserved constants. That is a static review, not a compilation
or acceptance result. No cloud job, Lean invocation, or Git publication was
performed while preparing these candidates.
