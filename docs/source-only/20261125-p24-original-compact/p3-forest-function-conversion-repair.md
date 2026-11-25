# P3 forest: move the reflexive equality to function type

Status: proof-only source candidate; no Lean execution or new acceptance
credit from this repair. Root owns independent review and the targeted retry.

## Actual failure

Task `19c87c6f786e4f4db568203af5a2386f`, at source
`d6a9d76c56621992a8445c9628d4a2058db72eb6`, checked the 39-module forest
closure with 27 existing unqualified diagnostic inputs and 11 fresh
`DIAGNOSTIC_PASS_NOT_ACCEPTANCE` results. The forest was the sole failure:

```text
P2OriginalAdaptiveForestSourceIdentity.lean:142:16:
error: (kernel) excessive memory consumption detected
```

The error points to the private pointwise
`originalAdaptiveTree_eq_graftSubtrees ... := rfl`, not the later public
consumer. The returned task metadata reports `-M11264`, 294.808 seconds and
whole-job peak memory 12,010,500,096 bytes. The log reports stable inputs.
`p3-forest-conversion-01.log` is 5167 bytes, SHA-256
`27cb66a301a29dd1582be1cbc514d4e45adf70789986a31e84b3eeed5f42654e`.

## Minimal change and type analysis

The pointwise reflexivity still compares concrete tree-valued expressions
containing the recursive Subtype value projection. The earlier tree-level
boundary therefore did not remove the observed resource failure. The error
does not identify the kernel's internal allocation hotspot.

`originalAdaptiveTree` has dependent function type
`(trees : List ClosedCutTree) -> trees.length = 21 -> ClosedCutTree`.
The private lemma now equates that entire function with the lambda copied
verbatim from its definition, using `rfl`. The intended comparison is at
the lambda boundary, before applying the concrete value projection; no
function-extensionality proof or new computation is introduced.

The consumer applies `congrFun` first to `trees`, obtaining equality of the
two functions on proofs of `trees.length = 21`, and then to the same `hsize`.
This gives the tree equality required by the existing `congrArg closedLeaves`
and `congrFun ... compactRegion`. The subsequent generic graft property,
initial-seed identity, and ordered forest-domain identity are unchanged.
Specialisation and the final consumer remain subject to the actual kernel
retry; memory improvement is not inferred from the source edit.

## Preserved manuscript correspondence and checks

The frozen source remains manuscript commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. A narrow rereading of
`certify_extended_prefix.py`'s `initial_cells()` and the numerical appendix's
compact-partition paragraph agrees with the previously audited 21-seed
inventory: six z strips, x-outer/y-inner enumeration, and original ordered
closed leaves. Their mathematical proofs, data, and numerical producer were
not rerun or changed. Frozen script SHA-256 is
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`;
appendix SHA-256 is
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.

Against the exact diagnostic source, a comment-masked comparison using
original source offsets confirms all seven public theorem headers, the
other four private theorem headers, all four complete computational
definitions, and imports are unchanged. Only this private lemma's statement
and its one call site changed. `git diff --check` passed. No assumption,
axiom, native computation, linter override, or resource override was added.

Source SHA-256 before:
`2f1429d2e08b51a2df175e541a15b4be62772c9bd49cea77aafa9c67d5cab568`.
Source SHA-256 after:
`6a08b33581f5ff540aa2b61be54783967090bbbcc79dd66fd6f6e3227541bc6f`.

The existing 38 successful dependency inputs can be considered by the
unchanged diagnostic reuse gates for a targeted forest retry. They retain
their diagnostic classification; this note grants no compilation, replay,
owned-inventory, or numerical endpoint acceptance.

Independent static review by `p24_project_cache_reuse`, followed by root's
diff review, found no visible type or logical defect in the two dependent
`congrFun` specialisations. The public headers, complete definitions, and
imports were independently compared. This is approval to run the focused
diagnostic, not evidence that its memory issue has been resolved.
