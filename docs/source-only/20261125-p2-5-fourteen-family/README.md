# P2.5: one negative-inner sum and its fourteen selected families

Status: **SOURCE ONLY; NOT COMPILED in the current P2 checkout; no current
kernel or owned-declaration acceptance.** The files below are source
candidates. Static hashes and historical P1 receipts do not establish
acceptance of the current 362-module graph.

## Production candidates and retained preimages

The repository-level production candidates are:

- `ImbalancedChen/P2Saving16NegativeFiniteCore.lean`, SHA256
  `6e30268863c917cc5746f1d980c73914d36ebff22d24cf4b61f335631f821e47`.
- `ImbalancedChen/P2Saving16FourteenNegativeFibrePartition.lean`, SHA256
  `0ab2abd52408a4963426c6efff7531d48aad592b5dc7a487eb21751172e5f68d`.

The **package-local**
`ImbalancedChen/P2Saving16FourteenNegativeFibrePartition.lean` is retained
as the exact old preimage, SHA256
`10f1a89be7f794eab2651c2181fdc51e91c9e622d44ac9e3490b5f49a5e4c0f2`.
The production copy changes only its first import from
`P2Saving16NegativeOriginalFibreSum` to `P2Saving16NegativeFiniteCore`.
Its two definitions and fourteen theorem bodies are byte identical.

`owners/` contains seven complete **after-extraction owner sources** for
later integration; `owners/preimages/` retains their exact old source
bytes. Those seven heavy modules are not installed in production. Their
remaining scheduled and analytic theorems retain their names, types and
proof text, apart from the documented equal-name identifier quoting.
Future integration must use the after-extraction owners with the new
core, because the old owners would define the moved names a second time.

## Exact finite identity

At one common positive trim width, the selected original `(s,d)` pair
carriers are pairwise disjoint. Their union and its complement in the
original small/rough pair carrier give the exact identity

\[
\operatorname{negativeInnerSum}
=\sum_{i:\mathrm{Fin}\,14}\operatorname{selectedSum}_i
+\sum_{x\in\operatorname{complement14}}\operatorname{negativeTerm}(x).
\]

The complement keeps the original negative test, coefficient, sign and
weight `G (s*d)`. Full rough words and every original pair occurrence are
retained. Before changing a pair sum into a sum over full moduli, the
proof applies the original small/rough product-uniqueness theorem.

Strict disjointness follows from positive-trim containment, the original
full87 source-ownership theorem and injectivity of the two source-cell
constructors. Earlier independent static review checked the pinned
Mathlib signatures of `Finset.disjoint_left`, `Finset.sum_biUnion`,
`Finset.sum_union` and `Finset.sum_image`. That review was source analysis,
not Lean elaboration.

## The 31 moved declarations

Every listed namespace is prefixed by `ImbalancedChen.`. These are 31
explicit declaration commands: 30 public declarations and one private
helper. Generated inductive, deriving and private kernel names are not
counted as independent source commands.

| Original namespace | Declarations moved to the finite core |
| --- | --- |
| `P2CanonicalWallFullResidualPayment` | `Prefix`, `canonicalPrefix` |
| `P2Saving16FirstRowCompilerFibre` | `firstEightCoordinates` |
| `P4AOriginalFull87StrictActionTrim` | `source_iff_rows`, `Margin`, `actionSlack`, `trim`, `mem_trim`, `trim_subset_source` |
| `P4AFull87TaggedAtomValue` | `CellKey`, `fibre`, `admit`, `occupied`, `literal_value` |
| `P2Saving16ActualCompilerDifference` | private `attach_indicator`, `actual_product_correction`, `actual_weighted_product_correction` |
| `P2Saving16SignedCorrectionFamilies` | `negativeInnerSum` |
| `P2Saving16NegativeOriginalFibreSum` | `negativeTest`, `selected`, `tuples`, `negativeTerm`, `selectedSum`, `complementSum`, `fibreSum`, `negativeInner_exact_split`, `selectedSum_eq_ordered_eight_fibres`, `selected_full_modulus_injective`, `selected_term_is_actual_compiler_difference`, `selected_moduli_subset_Q`, `selectedSum_eq_full_Q_correction` |

All thirteen finite declarations from `NegativeOriginalFibreSum` move
together. Its two scheduled theorems stay in its old owner. The old
`StrictActionTrim` owner also removes `rowCount`, `rowValue` and
`sourceSet`, which were already extracted to
`P4AOriginalFull87SourceDefinitions` on November 24; those three are not
counted in the new 31.

The finite core directly imports only:

```lean
import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P4AOriginalFull87HistoryCore
import ImbalancedChen.P4AOriginalFull87Ownership
import ImbalancedChen.P2OriginalSaving16Full87SourceBinding
```

### Identity and compatibility accounting

`FINITE_CORE_DECLARATION_IDENTITY.json` records zero-based UTF-8 byte
ranges and SHA256 values for each preimage and postimage block, command,
header and body. Original line endings, including the two CRLF blocks
from `CanonicalWallFullResidualPayment`, are retained.

- Eighteen of the 31 entire declaration commands are byte identical;
  29 headers and 19 bodies are byte identical.
- Fourteen actual term references to the reserved word `universe` are
  escaped as `«universe»` in the core. Each occurrence has its original
  byte offset, line and context in the ledger. This preserves the
  identifier; those declarations are not labelled byte identical.
- `StrictActionTrim.mem_trim` uses `mem_ofPred_eq` in place of the
  deprecated alias `mem_setOf_eq`. The same single-token change is made
  independently in the installed `HistoryCore.mem_core` support source.
  No warning is disabled.
- The private `attach_indicator` has the same source namespace, short
  name, type and body. Its generated kernel fullname changes with the
  defining module. Its new generated counter and elaborated proof terms
  are not asserted before compilation. The public theorem names remain
  unchanged.
- The seven owner postimages apply any required `universe` term escaping
  to their retained declarations. Their per-declaration hashes and
  occurrence counts distinguish those lexical changes from exact bytes.
  The FirstRow owner also corrects its already-recorded erroneous import
  `P2Saving16Full87SourceBinding` to the existing
  `P2OriginalSaving16Full87SourceBinding`; no alias module is created.

The existing `P4AFull87TaggedAtomValue.admit` is a definition naming the
admission predicate. It is not an `admit` proof placeholder.

## Five existing support sources

`SUPPORT_SOURCE_SELECTION.json` records the exact donor commits, source
hashes, installed hashes and receipt provenance. P14 and P15 supplied
identical repaired bytes for all five files. Four are installed byte for
byte; `HistoryCore` receives only the alias update described above.

| Support source | Historical evidence for the exact donor bytes |
| --- | --- |
| `P4AOriginalFull87HistoryCore` | No own acceptance receipt found; its alias-adjusted current postimage is uncompiled |
| `P4AOriginalFull87Ownership` | No own acceptance receipt found |
| `P4AOriginalH5H7SourceDispatch` | P1 member-repair batch83: own normal, kernel and owned-declaration PASS |
| `P4AUpperTaggedParityCompiler` | P1 member-repair batch83: own normal, kernel and owned-declaration PASS |
| `P4AUpperTaggedBetaAttachment` | P1 batch5: own acceptance with source and five output hashes |

Exact receipt copies are under `support-receipts/`; their source hashes
bind the donor files, not the current P2 graph. Donor source preimages
are retained under `support-preimages/`. The existing production
`P2LowerFiniteCellRounding` differs from the P14 donor and is preserved
verbatim, along with every other preexisting production source.

## Dependency and preservation checkpoint

The actual baseline is `840f7e7f9d1639b7a6678c9fe34a6fcc01916321`.
That commit adds documentation to `c79b9ab98635f7137679cfbeb9513b7a2174f3d8`
and leaves its 13 production compatibility repairs unchanged.

`CLOSURE_SELECTION.json` now records the graph read from the actual
production files: **362 project modules**, consisting of 360 existing
modules and the two new candidates, with no missing project import or
cycle. Five of the 360 existing modules were missing locally and are
installed from the sources above. All 3,778 preexisting production Lean
files remain byte identical, including the protected 371-source set.

The preceding 1688-module source selection is retained verbatim in
`PREIMAGE_CLOSURE_SELECTION_1688.json`, SHA256
`adea7eb4ed5de99ddbe91f8fd1ec61385f1dd641b09289dac4049969ce739b6e`.
That large graph was never installed or compiled here. Its recorded,
unapplied FirstRow import spelling problem remains part of that historical
record. The finite extraction removes the path through
`SignedCorrectionFamilies` → `WeightedCompilerLedger` → `R17PaidIntegral`
from this root; it does not replace any scheduled or analytic theorem.

The complete snapshot check below is scoped to source checkpoint
`a5d960eed7a4fff90d7a572d383bb6b497173f18`, whose parent production baseline
is `840f7e7f`. Run it from a checkout of that exact snapshot. Later
compatibility repairs to dependencies deliberately change the historical
baseline comparison; they have separate source maps and actual compile
receipts and must not be represented by this earlier static result.

Run the source-only consistency check from that repository root:

```sh
python docs/source-only/20261125-p2-5-fourteen-family/verify_source_identity.py
```

The script checks the retained bytes, allowed transformations, owner
removals, support provenance, whole14 import-only difference, actual
closure and unchanged production baseline. It does not invoke Lean,
Lake, a cloud compiler, or Git mutation. `STATIC_SOURCE_CHECKS.json`
records its output separately from compilation acceptance.

`INDEPENDENT_STATIC_REVIEW.json` records the separate scope review, bound
to the two candidate source hashes and all three selection/identity
ledgers. It found no blocking issue within this finite scope. Complete
current acceptance must still include the private helper and all
generated `Margin` declarations, including constructors, recursors and
deriving instances.

## Remaining obligations

This finite identity supplies no PP bound, common corner schedule,
complement payment, Q96 evaluation, or same-coefficient distribution
estimate. It retains all those obligations' original terms and does not
assume their conclusions. In particular, it does not sum fourteen copies
of the entire distribution error and introduces no second saving.

Any later corner-schedule candidate in this package has its own source
map and review status. Its presence does not change the finite core's
NOT_COMPILED status or discharge these remaining analytic obligations.
