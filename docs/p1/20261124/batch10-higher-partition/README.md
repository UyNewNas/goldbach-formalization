# Existing Higher proofs, separated into compilation units

**Status: source-only, uncompiled.** This package does not claim that the new modules, their public facade, or P1 have passed Lean. It contains no cloud driver and executes no Lean command.

## Actual reason for this change

The frozen `a9a4e532991af5ba3b397b7381fd4a1fdf3302ee25ef27a16ebba04e68a68334` monolithic source failed in Batch9. The complete normal command exited 1 after 813.0146605129994 seconds; Lean itself exited 134 after reporting an interpreter `lean::memory_exception`. No proof-level goal, failing declaration location, or successful object was emitted. The failed source has no accepted `.olean` to reuse. The complete normal log and original source/five-artifact records are retained under `evidence/`.

This establishes a concrete memory failure in the monolithic run. It does not identify the particular guard that was active, prove a mathematical gap, or justify repeating the same run with a larger budget. The partition preserves the existing mathematical source and permits separate compilation receipts and cache reuse.

## Exact partition

| Compilation unit | Existing declarations retained |
| --- | --- |
| `P2OriginalSixthHigherMomentsCore` | Five existing definitions; `completeH_cons_succ`; nine existing small helpers |
| `…GuardLowBoundary` | The successful Low group: `(k,i) = (0,0), (0,1), (1,0), (1,1), (2,0)` |
| `…GuardMiddle` | The successful Middle group: `(4,0), (5,1)` |
| 42 other `…GuardKkIi` files | One remaining integrated-power guard each, including the existing degree-six `(6,6)` proof |
| Seven `…AuthorKk` files | One existing rational author/Newton guard for each degree 0 through 6 |
| Original `P2OriginalSixthHigherMoments` | Five remaining definitions and fourteen remaining public theorems; its original aggregation proofs refer to the imported guards |

There are **53 files: 52 new providers and the existing root filename**. All 90 original source declarations occur exactly once. No theorem statement, polynomial recurrence, factorial coefficient, finite range, proof body, or definition body is synthesized or mathematically rewritten.

Low and Middle remain in their actual successful group sizes and original order. Their five and two proof bodies are byte-identical to the frozen production source. The known degree-six proof differs from its successful probe only by the already existing helper spelling `real_smul` versus `rational_smul_real`. The earlier probe receipts retain their original owners; the new modules require their own normal and kernel acceptance. None of the old probes is scheduled again.

## Public contracts and ownership

All **15 original public theorem statements, 10 original definitions, and their fully qualified public names** are preserved. Their original mathematical declaration texts and bodies pass exact static comparison.

Five definitions—`duplicateH`, `baryCoefficient`, `bumped`, `integratedPower`, and `completeH`—and `completeH_cons_succ` move to the Core source module. Their namespace remains `ImbalancedChen.P2OriginalSixthHigherMoments`. The other public declarations stay in the original source module. This source-module owner change is intentional and must be reflected in audit scope; it is not represented as preservation of the old owner.

To cross import boundaries, 56 existing private guards and seven existing private helpers become accessible under `ImbalancedChen.P2OriginalSixthHigherMoments.ProofPieces`. Two Core-only helper theorems remain private. `MANIFEST.json` maps every original source declaration to its new owner and visibility. It does not guess generated private kernel names. Generated declarations must be enumerated from the actual new serialized environments.

The sole current direct source consumer found is `P2OriginalSixthMomentRow`. It still imports the original root and explicitly opens `rationalMoment`, `rationalMoment_cast`, `realMoment`, and `integral_interpolate_mul_power`; all four keep their original names and source owner.

## Verification order and resource evidence

Use the existing guard/outer serializer and unchanged 4,000,000-heartbeat / 100,000-recursion-depth settings. Compile Core first, then the 51 proof units one at a time or in separately frozen chunks, then the root after all providers have valid receipts. A cold `lake build` of the root must not fan out into simultaneous builds of all the new guards. Each proof unit imports Core only, so a later unit failure does not invalidate successful independent units.

Record source and the existing five artifact fingerprints, complete raw output, and actual owner declarations for each new module. Final independent kernel and full-owned audits must cover **the union of Core, all proof units, and the root**. Checking only the root's newly owned declarations would omit most of the proof. Original `.olean` files must not be renamed, and probe receipts must not be reclassified as new-module acceptance.

The existing successful Low and Middle commands took 29.350428488003672 and 62.81613987099263 seconds. The degree-six command took 109.12172996500158 seconds, with 109.03445014600584 seconds inside its serialized lane. **No per-probe peak-memory field is present in the available command, lane, or raw-log records.** `PROBE_RESOURCES.json` records those peaks as unknown. The reported Batch9 peak of 21,231,366,144 bytes belongs to the whole two-lane job and cannot be assigned to one probe or guard. Elapsed time is insufficient evidence for pairing two heavy workers.

Fresh compiler processes remove accumulation across guard elaborations, but this is not a guarantee that every previously unobserved single guard or the final import/audit will fit. Those remain actual verification risks. No budget, guard, checker, numerical producer, or finite certificate is changed by this package.

## Manuscript boundary and reproducibility

The source remains an instance of the pinned 1106 `num:simplex-moment` formula in `numerical-appendix.tex`, lines 181–188, at manuscript commit `a988cba584d803ae2856a0de50efb582f4f3dd6a`: dimension six, seven barycentric coordinates, an eighth duplicated node, degrees at most six, and normalization `7! * choose(7+k,k)`. All node values remain arbitrary. The existing author/Newton and integer-divisibility interfaces are unchanged.

`partition_existing_source.py` is a deterministic source extraction and static-check script. It checks the frozen preimage, exact declaration/body preservation, successful probe group contents, the original raw failure/probe hashes, the eight unchanged project dependency sources, and the four protected original P1 roots. It writes only this isolated package. `COMPILE_PLAN.json` supplies exact paths, hashes, imports, and ordering for the parent's existing compiler coordinator; it is not a new compiler or evaluator.
