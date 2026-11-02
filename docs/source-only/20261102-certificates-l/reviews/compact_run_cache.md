# Independent L compact run/cache source review

**SOURCE_REVIEW_PASS**, limited to the concrete original computation, complete ledger and symbolic cache refinement in the exact frozen packets below. Reviewer: `/root/k_review_history`; task IDs: `compact_run_certificate` and `compact_table_cache`.

All eight Lean files remain uncompiled: `compiled=false`, `kernel_verified=false`, `formal_credit=0`. Every decisive finite computation is **UNEVALUATED**. Original compact endpoint, complete analytic/source soundness and global manuscript target remain **OPEN**. Resource feasibility is **UNKNOWN**.

| Packet | REGISTRY SHA256 | REPORT SHA256 |
| --- | --- | --- |
| compact_run_certificate | `522a78845882b0c70673846a65b97191bb8604d996ea140a715bdd30a7e558d7` | `38d8c0dee31a1ce24701ba7b193e42556f03fc550573a3e2350b3dd15b50ac37` |
| compact_table_cache | `a16113428424dbe2be531dff2930c61528351943db43e0cff40eb4f27b164349` | `d969bcd84a40a9fd63a42680a59baf1294fe71dbd3e05ca033b8c2cf7e149b3d` |

| Reviewed source | Raw SHA256 |
| --- | --- |
| P2OriginalCompactCachedEndpointCandidate.lean | `3f84c653e57cf48266a4160477c94112acbad086028c75652892fb9ab04aecb6` |
| P2OriginalCompactCachedRun.lean | `6740638c96f47050e8dc3290d347460e9a0ac162d71fdcc91d6745c1181070a7` |
| P2OriginalCompactConcreteLoop.lean | `5d1dd5be9ccefb5babc3d29c20ab5e68b0ceecf8a1d7fadb564b32f3986b3827` |
| P2OriginalCompactConcreteRun.lean | `6c393a83ba3d468b159ee2877e02e231cc7738117edec3da7415b6a8693132f5` |
| P2OriginalCompactHistoricalEndpointCandidate.lean | `0e47deab9847099d4d3f2e478d0d40cf787476fc814fe098d96521a752f0849a` |
| P2OriginalEfficientPriorityHeap.lean | `74b98c697348d7e5e959cf1f407eb2935f5c83e8d344313451f1c5c75af81e23` |
| P2OriginalCompactQ80ArrayTable.lean | `c788578fbe8aac7a0ef601a0f483ae4972dde0ebce303022264ed6c08859f147` |
| P2OriginalCompactQ80CacheEncloser.lean | `5821aa5af803817feda439763f413810d8234ece305dcfefea5b6140a0b7d80e` |

The first four run sources retain their initial frozen hashes. The cache registry references the two downstream cached Lean consumers without referencing their REGISTRY/REPORT, avoiding a metadata hash cycle.

## Findings

1. **Actual incremental original table.** `appendNode` computes exactly `nodeUpdate g nodes.size (lookup nodes)` from the preceding Array, then pushes it at that index. `buildFrom` starts with index zero's original initial node. The `Represents` invariant proves both size `n+1` and total equality to `sourceState g n`, including the initial-node default beyond the stored prefix. Structural induction gives the closed grid16384/max12 table and exact historical-table refinement. The executable builder does not call the slow functional recurrence or map that recurrence over indices.

2. **Actual Array APIs match.** The inspected v4.33.0-rc1 sources give precisely the push/singleton optional-lookup formulas and Option defaults used in the proofs. The possible positive-branch `simp only` concern is resolved: actual `Lean/Elab/Tactic/Simp.lean` defines `simpOnlyBuiltins` with `eq_self` and `iff_self` and inserts them for `simp only`. Thus the supplied equality hypothesis, reflexivity simplification, `if_true` and `getD_some` support the written proof. No correction or refreeze was needed.

3. **Whole cached interpreter.** CacheEncloser preserves interpolation, point/tail lookup, integer defects/decay, chord/Jensen, lower and upper differences, early returns, integer rounding and minima. Every table-dependent helper, fixed upper calculation and diagnostic has an explicit Array parameter and a componentwise equality proof. Original `jensenAssertions` is table independent. The exact-lookup premise is discharged by the closed cache theorem; it contains no desired analytic estimate. Transporting the existing point enclosure does not prove full leaf enclosure soundness.

4. **Real priority queue semantics.** The manifest-pinned Batteries implementation was independently read and hashed. Its merge ignores root siblings; `rootBag` and `bag_merge_roots` account for that exact behavior. Combine/insertion/deletion preserve multiplicities, and the local NodeWF induction plus transitivity proves global minimum priority. The key is descending integer error, then ascending issued serial. Seed/path addresses do not enter the key. The separate `SerialNodup` invariant handles repeated multiplicities as well as distinct-job uniqueness, so later Python tuple fields cannot break a serial tie.

5. **Original seeds, splits and actual state.** The driver binds the concrete Q80 encloser and normalized original21 inventory in x-outer/y-inner order. Axis selection is the strict relative-width scan 0,1,2, retaining the earlier axis on ties; midpoint is integer floor. Side0 is evaluated/issued before side1, and serials advance only for positive-error insertions. Address navigation computes literal source children, checks the cached parent's coordinates/bounds/serial and derives source refinement from the returned computation. Explicit failure cases do not manufacture a successful run. The loop uses the source-computed fixed upper, target6809/1000, budget2000000 and original while inequality.

6. **Complete ledger and source integral.** Initial totals include every seed. Each split subtracts the parent and adds both children, including exact/empty leaves that do not enter the heap. The complete source forest gives both ordered charge lists, their cached-total identities and length `21 + actual splits`. Its integral decomposition is for the unchanged original compact source kernel/domain. Positional attachment uses the full seed/depth-first side traversal, preserving every terminal charge.

7. **One explicit cache throughout the concrete path.** `cachedRun` binds `tableArray` and `fixedUpperWith nodes` once and threads them through the loop. All seed/job/bounds/serial operations and table-dependent source-check sites use that Array. `cachedRunAndEntries` shares the same Array through the run and complete final charge traversal; `cachedChargeTree` attaches those data. Helper equalities and fuel induction prove exact equality to the original logical run, its entries, charges, attached tree and finite check without normalizing the slow run. This is a source construction/equivalence finding, not a claim about kernel sharing or resource bounds.

8. **Finite candidates remain isolated and unaccepted.** The preferred cached candidate imports CachedRun without importing the legacy slow endpoint candidate. Both contain closed `by rfl` attempts. The historical check requires actual budget stop, splits2000000, upper144590669409566793572719, active heap1852040 and recorded diagnostics true. Those literals are comparison targets only. Neither the saved JSON nor a caller-supplied Run/endpoint creates the state. Conditional field-extraction lemmas and consequences of the unevaluated candidates do not establish those fields.

No static blocker was found within that scope. No added axiom, sorry/admit, unsafe/native proof mechanism, IO oracle, source-estimate assumption or assumed successful endpoint was found in the eight new Lean files. Ordinary `decide` defines source guards; `of_decide_eq_true` reflects already-present Boolean hypotheses and was not used to accept an externally computed result.

## Evidence and limits

The original producer and full-driver source were read as text, together with the relevant conservative interval primitives, manuscript body360–509 and1310–1435, numerical completion61–63, J source-split/forest and K queue/ledger suppliers. Original c=49044063/25000000 and K=8452171/1250000 are unchanged.

All **78** registered local pin occurrences matched hashes and byte counts across **56** distinct paths. The JSON review records that exact inventory. Both manifest-pinned upstream Batteries files matched their recorded hashes. The actual local WSL Array/Option/Mathlib definitions/toolchain files matched the five recorded snapshots. API sources were read, never executed or installed.

The pinned [Batteries PairingHeap source](https://raw.githubusercontent.com/leanprover-community/batteries/41bd267b3f6b7252f6676af46d4ffc6783b64de9/Batteries/Data/PairingHeap.lean) supplies the reviewed operations and WF definitions; the local proof supplies the additional content/minimum facts. The inspected [Lean v4.33.0-rc1 Array lemmas](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0-rc1/src/Init/Data/Array/Lemmas.lean) supply the exact optional-lookup formulas.

Remaining work is explicit: install and kernel-check all source candidates; evaluate the isolated cached historical guard; finish original all-branch analytic enclosure and complete Python primitive/assertion refinement; establish practical kernel resource feasibility. The selected `sourceAssertions` are not an exhaustive Python assertion theorem. No table guard, run outcome, historical sum/count or successful endpoint was evaluated or accepted by this review. Full Python execution equivalence does not follow solely from the reviewed queue/cache refinement.

No Lean/compiler/lake/build/CI/meta elaborator, finite decision, numerical replay/checker, cache generator, Git operation, quota call or subagent was used. Only `L/reviews/compact_run_cache.json` and `.md` were written. There is no newly established manuscript contradiction.
