# Batch12: nine existing candidate owners

Status: **source and receipt review only; fresh runtime gates required**.
No target acceptance or build readiness is asserted. Source review is bound to
published commit `220c14630ffd266f824bdbf0977147ecb740c0dd`.

`CANDIDATES.json` records all nine exact source hashes and imports, direct project
import hashes, accepted-parent receipt pointers, complete parent-closure source
fingerprints, and the static proof-body review. It reuses the existing 53-candidate
inventory; it does not duplicate the 2,740-module graph or provide another runner.

## Preserve exact accepted parents

The three parent owners have the recorded status
`PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS` in the existing audit12
receipt. Their current complete source closures also match that receipt and the
published commit, with no missing entries or mismatches:

| Parent (prefix `ImbalancedChen.`) | Matching source closure | Candidate consumers |
|---|---:|---|
| `P4AOriginalFull87SourceDictionary` | 215/215 | Seven Full87 owners below |
| `Part3ActualWThreeCapacityRun` | 130/130 | `Part3ActualWResidualCompletion` |
| `P1OriginalFifthPositiveStratumMass` | 212/212 | `P1OriginalFifthMovingHarmonicEnvelope` |

The receipt is member
`batch9-completed-normal-supplement-acceptance/lane-1/VALIDATION_RESULTS.json`
of `docs/p1/20261124/batch9-normal-accepted-evidence/verification.tar.xz`.
Receipt SHA256:
`3e986f38b3962a08fc09e31826f18c06df9a6f5b2eff93eb888118cca9da6db5`.
Every direct project import of the nine candidates is in its corresponding
accepted parent closure. Reuse the parent results after fresh source/artifact
gates; a new consumer does not by itself require repeating accepted parent work.

## Candidate rank retained from the prior inventory review

All names have prefix `ImbalancedChen.`. They are pairwise import-incomparable and
all appear in the observed census's missing-object frontier. Source size did not
establish runtime cost, so the build grouping below refines this earlier ranking.

| Rank | Owner | Proof work |
|---:|---|---|
| 1 | `P4AOriginalFull87PrefixBinding` | Four transfer proofs; only three constant `3 <= 8` decisions |
| 2 | `P4AOriginalFull87H3Interiors` | 1,188 affine-margin and 9,504 coefficient predicates |
| 3 | `P4AOriginalFull87HistoryCore` | 17 continuity, compactness and exhaustion theorems; Fin 4/7 cases |
| 4 | `P4AOriginalFull87AscendingAllInteriors` | 1,344 margins; 832 shared-pool coefficient predicates |
| 5 | `P4AOriginalFull87H5H7Interiors` | 1,710 margins; 13,680 coefficient predicates |
| 6 | `P4AOriginalFull87SeedNineFiftyInteriors` | 1,548 margins; 12,384 coefficient predicates |
| 7 | `P4AOriginalFull87DescAscPairInteriors` | 2,701 margins; 21,608 coefficient predicates |
| 8 | `Part3ActualWResidualCompletion` | Structural list/trace induction and symbolic overflow arithmetic |
| 9 | `P1OriginalFifthMovingHarmonicEnvelope` | 525 lines, 11 named theorems; symbolic nested sums and log/rpow bounds |

## Natural build groups

1. **PrefixBinding and HistoryCore:** the natural first symbolic pair.
2. **AscendingAllInteriors:** the first literal owner to measure. It checks the
   shared 104-row coefficient pool once, instead of repeating it for each cell.
3. **ResidualCompletion:** its own independent symbolic group, using list/trace
   induction and symbolic overflow arithmetic.
4. **MovingHarmonicEnvelope:** a separate independent symbolic group, with its own
   normal result and resource evidence for the larger sum/log/rpow proof.
5. **H3, then SeedNineFifty, then H5H7:** held until actual Ascending pilot elapsed
   time and peak-memory evidence is available. No cheap-build or overlap assumption.
6. **DescAscPair:** also held for that pilot evidence; it has the largest finite
   workload here, across four `decide` proofs.

These are scheduling groups only. Existing local Lean resource options remain
unchanged, and the root retains all lane/resource scheduling decisions.

None of these nine uses `native_decide`. The five literal owners use plain
`decide`, usually after `fin_cases`, and collectively state 8,491 margin and
58,008 coefficient inequalities over 87 original cells. H3, H5H7, SeedNineFifty,
and DescAscPair locally set `maxHeartbeats 0` and `maxRecDepth 8192` for these
checks. Ascending has no corresponding local override. The finite computations
can be costly even though the source files are short. These are exact domain
counts from the existing statements, not successful computation receipts or
runtime predictions. The moving harmonic sums remain symbolic; they are not
enumerated over a concrete prime carrier in these proof bodies.

## Repaired four do not invalidate the 71 passed-owner source closures

The observed 71 normal-passed owners are exactly the existing Batch10 source-set
keys minus the four failed owners. Their source hashes still match the Batch10
postimages. In the current graph, none of Saving19SimplexMoments,
UpperTaggedContinuationAccounting, PrimeEulerOperatorWords or
CommonRefinedPreservation is an ancestor of any of those 71 owners. Their union
closure has 585 modules. Both census source-mismatch modules are absent from that
union and from the nine candidate closures. The JSON records the exact input
census hash and reproducible source-map fingerprints.

This establishes source-graph separation, not acceptance of the 71 or the nine.
The root owns the P1 queue. Reuse the existing inventory's invocation guidance and
runners; fresh source/artifact gates and actual normal/kernel/full-owned evidence
remain necessary. No Lean, Lake or cloud call was made for this review, and no
Lean source or existing file was modified.

## Bounded execution caller

`run_candidates.py` adds two explicit execution groups after the source review
above. It reuses the exact published `retry_four.py` normal/context/receipt and
completed-audit validation functions from commit
`9246927b8faebca3c06e4a5a47e733b5f13536db`, with unchanged Batch5/Batch6/e9 tools.
The source snapshot remains `220c14630ffd266f824bdbf0977147ecb740c0dd`.

| CLI group | Selected owners | Receipt root |
|---|---|---|
| `symbolic` | PrefixBinding, HistoryCore, Part3ActualWResidualCompletion, P1OriginalFifthMovingHarmonicEnvelope | `/workspace/p1-complete-proof/20261125-batch12-symbolic-v1` |
| `literal-pilot` | Full87AscendingAllInteriors only | `/workspace/p1-complete-proof/20261125-batch12-literal-pilot-v1` |

The Full87 names have their existing `ImbalancedChen.P4AOriginalFull87` prefix.
H3, H5H7, SeedNineFifty and DescAscPair interiors are not selectable through
this caller. The two groups remain separate jobs with separate logs and results.

```sh
python3 -B run_candidates.py --group symbolic --check
python3 -B run_candidates.py --group symbolic --run
python3 -B run_candidates.py --group literal-pilot --check
python3 -B run_candidates.py --group literal-pilot --run
```

`--check` accepts explicit `--source-repo` and `--project` paths for local
verification. Execution is restricted to the existing cloud project. There is
no source-installation path: every selected owner and its complete project
source closure must already match the exact Git snapshot. The loader does not
call the four-repair installer's preflight, so unrelated later repairs of those
four owners do not change this caller's source gate.

One original lane-0 serializer covers each group's sequential per-owner normal
attempts and explicit populated e9 audit lane. The reused normal primitives
require direct-dependency readiness, exactly one genuine target `Built` header,
and durable source/object/configuration/runtime/command bindings. Independent
failures preserve logs and allow the remaining selected owners to proceed.
Completed normal and full-owned audit receipts are validated before reuse;
partial audits are held for inspection without overwriting them. Accepted
parent normal work is not scheduled again.

Local preparation checks passed: Python `py_compile`, the symbolic source gate
(four owners, 304-module union closure), and the literal-pilot source gate
(one owner, 216-module closure). These read-only checks invoked no Lean, Lake or
compiler service and establish no normal, kernel or full-owned acceptance.
Every result keeps `whole_P1_complete: false`.
