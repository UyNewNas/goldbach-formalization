# Family-scale verification orchestration

The Python checks below ran in scratch on 2026-11-27. They establish source binding and build/cache behavior. No Lean elaboration, kernel replay, declaration inventory, transitive-axiom check, or fixed-source acceptance was produced by these tests.

| Check | Observed result |
| --- | --- |
| Direct source intake | The 87-module closure passed source-only intake with 2 selected modules and 85 unchanged providers. The source-intake SHA256 at this run was `f94488b78df5c01b2d5f727c06579bf5a11e5e918ac2734a8c7ec2779e705c45`. |
| Source mutations in an isolated copy | The gate rejected seven changes individually. They affected the two selected sources, one historical provider source, the accepted closure, the current closure, the whole-node completion flag, and source provenance. After restoring the inputs the 87-module check passed. |
| Existing source/object gate | All 15 existing regression tests passed. |
| External import parser | Parsed the observed LeanArchitect public and public-meta imports and section header. Three malformed or unsupported forms were rejected. Project sources continue to use the unchanged shared parser. |
| Synthetic build | The read-only pass wrote no receipts. The first build compiled three dependency-ordered sources, and the next reused three. Deleting a receipt, altering an owned output, or altering a direct external dependency forced the corresponding fresh compilation. Removing the external Mathlib object stopped the run. |
| Implementation examined | `verification/build_part3_pinned_closure.py` SHA256 `2fbe024ae3758df0a834762452776f8c8c4fc79b46418785698dfd2d7833d7a5`. |

The checked-in reproducer packages the temporary mutation and lifecycle probes as three unittest methods. It constructs a temporary project and temporary git repositories, with a mock compiler for the lifecycle test. To exercise the cases from the repository root, run:

```sh
python -B verification/test_p31_family_scale_build.py
python -B verification/test_part3_source_object_gate.py
python -B verification/verify_part3_continuation.py --group family-scale-budget --source-only
```

## Scope review

Only the family-scale group selects the direct builder. A read-only pass checks all reachable project and pinned package sources and every directly referenced external object before writing outputs. The build follows actual imports into the pinned goldbach and LeanArchitect repositories. Selected package files are checked against their git blobs at the pinned revision. Mathlib and toolchain imports require existing objects.

The direct compiler runs with the owning package as its working directory and with absolute Lake search paths. Reuse compares the source digest, the pinned compiler executable digest, the builder digest, compilation flags, the resolved direct dependency paths and their object-part digests, and the module's own output digests. A successful compiler exit and a second input check precede atomic publication of each cache record. Historical provider objects rebuilt to supply imports receive build records only.

Formal verification retains the common clean-tree and dependency checks, strict recompilation of both targets, per-target kernel replay, complete selected-environment declaration inventory and transitive-axiom checks, and the before/after object-binding checks across the whole project closure. Formal verification has its own report and status.

## Fixed-package duplicate import

The first P2 preflight, task `af46e132d65c472f8f76ea1ab26a1c0b`, exited before any compilation. In the pinned goldbach source `MathlibNt/SieveTheory/Selberg/SelbergUpperBound.lean` (blob `9d3045b9f4d16efc455adcdccd1ff316d78728d1`), lines 5 and 16 both import `Mathlib.Algebra.Order.BigOperators.Ring.Finset`. The initial external-header adapter incorrectly treated this legal duplicate edge as an error.

The revised graph reader retains the first occurrence of each external import. The dependency checkout and its verified bytes go directly to Lean. The shared project parser still rejects the same duplicate import. The reproducer tests both behaviors and the isolated direct-build lifecycle. The repeated in-process calls also exposed an unclosed lock file, which is now closed on every exit by its context manager.

The revised builder SHA256 is `6bbdf4c7e79634bd95b472e3536e39276abe8910d71fcdcc9ff2a4bce80322b2`. Running `python -B -W error verification/test_p31_family_scale_build.py` passed all three test methods. The 15 pre-existing gate tests also passed. The external source parser change leaves the strict compiler options, selected module list, declaration inventory, axiom allowlist and kernel replay unchanged.

## Dependency ownership and preload review

The second P2 preflight identified 531 reachable source modules and 211 external objects. The ensuing provider build was stopped to correct an ownership issue in the verifier. This stop produced no mathematical conclusion about either new theorem.

The earlier builder accepted some external module objects from any registered output root. A missing tracked source file could also switch a dependency from compilation into external-object lookup. The replacement inventories the checked-in Lean files directly from each package's pinned git tree. It reserves Init, Lean, Std and Lake for the pinned sysroot, binds Mathlib to its package, and requires a unique source owner for other imported package modules. Each visible external object must occupy the expected module path for its owner. Each existing object part is checked against its canonical path to reject redirection of a module's parent directory. Before any object writes, a temporary import-only file loads every external boundary module through the actual pinned Lean environment, exercising the boundary objects' transitive imports. The command has no output-object option.

The isolated fixture additionally exercised missing tracked sources in both goldbach and LeanArchitect despite foreign objects, a sysroot module shadow, a foreign object for an ordinary package, ambiguous source ownership, a parent-directory symlink, and a simulated loader failure for a missing transitive prebuilt import. All three targeted Python test methods passed with warnings as errors. All 15 shared source/object regressions and the 87-module source-only inventory passed. The synthetic loader tests the control flow around a failed Lean invocation. A real environment must still pass the import-only probe and the separate strict/replay/inventory gate.
