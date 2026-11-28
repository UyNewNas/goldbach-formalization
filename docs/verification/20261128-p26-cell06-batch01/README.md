# Cell06: first accepted two-owner batch

Two unchanged original-source modules have completed normal compilation, the official stock kernel checker and a full-owned declaration audit:

| Owner suffix | Normal seconds | Stock checker seconds | Full-owned seconds | Canonical declarations |
|---|---:|---:|---:|---:|
| `Moment06Input` | 4.2264 | 2.9440 | 15.1475 | 9 |
| `Geometry06ScalableActive8EnumerationBlock000` | 11.9819 | 6.1433 | 16.5975 | 31 |

Both full-owned inventories have zero shared occurrences, no unsafe/partial/axiom owners and only permitted transitive axioms. Exact timings and inventories are in the archived receipts. All six processes exited zero. No previously successful normal, kernel replay or full-owned audit was rerun.

The accepted project context advances from 1,502 to **1,504 modules**. This adds the moment packed-input/list interfaces and the first geometry active-enumeration parsing block. The remaining Cell06 parser, decoder, finite arithmetic and integral chain are open. The Cell06 integral and global P2.6 are not complete. The older archival `original_full_snapshot_verified:false` qualification remains unchanged.

## Verification contract

This uses the explicitly new `batch_global_boundary_v1` contract: a complete global byte PRE and POST around the two sequential owners, plus actual per-mode local D checks. It does not claim the older per-command full-global verification window. The controller and its 28 passing synthetic host tests were independently reviewed before this real execution.

Each complete G scan read **110,275 files / 13,130,890,292 bytes**. PRE took 24.3544 seconds and POST 49.0609 seconds; both matched the same byte-map SHA256, with no mismatches. Every mode binds its exact command, allowlisted environment, local inputs, durable process return, log and normal output to the same attempt. The final batch seal requires all six successes and the completed POST. Successful normals are permanent artifacts and are excluded from recompilation.

The real run used the pinned Lean `leanprover/lean4:v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, trust zero, warnings as errors and one Lean thread. The original 113 rows, 33 vertices, 97 gates, degree six / exp degree three, Q80/Q96 and saved max(old,new) semantics are unchanged; this prefix does not yet prove all their downstream obligations.

| External root | SHA256 |
|---|---|
| Controller delivery | `484a28bb2a39836d86120e04b699bda12b8e9c5af33fef0c84699ab6bd7e9a24` |
| Batch extension | `94ef902b323ff2b041045c08d315b4b89e86ee769c5797ea8b7f2a01aeb4b376` |
| Batch contract | `32536b97ddaa017be6872d73efbdc8fb837a33763f55f98e50be7c27b1c67209` |
| Accepted batch seal | `b3859d41dbfd10ea78ab4452d8e779989d4a00bd40748a1100c2c0e241e0c7e1` |
| Accepted 1504 context | `c19494c887e8768213dfb8c15b43fc36f2f52c72d527a86f8095f4a66f25dcb8` |

Cold preparation took 89.5184 seconds, including 65.8659 seconds of ancestor validation; its copy upper bound was 1,048,342,543 bytes. The real six-mode batch took 155.3678 seconds, with 57.0406 seconds in proof processes and a sampled aggregate peak of 7,248,977,920 bytes. These are separate measurements, not a throughput promise for later modules.

## Evidence and provenance

`CAPSULE.json` records the roots, mode metrics and exact scope. `MANIFEST.json` pins every archive member. `evidence.tar.xz` is 4,886,672 bytes, SHA256 `6bb52855f6a2efe1573e388fd4495663f23a6faa9f971e1e3209c0108fca96ea`; all 84 members, including its internal manifest, were read back byte for byte.

The archive includes both source/object pairs, permanent normal artifacts, all six attempt directories, full G selector and boundary reports, both prefix contexts, the batch seal, exact helpers/controllers, original JSON copies, MCP job records and the packager. Parent objects and the fixed external runtime remain pinned references rather than duplicated dependencies. The ancestor evidence is published in commit `ed57da0020d437d4eaacaaff3deed73944c41113`; the full source-only candidate backup is artifact commit `9779a018863ddfc674f34228beffbf7c34f4867c`.

Actual MCP jobs were prepare `04ed8aff389843468a4b6746cffc46af`, run `bd88d0f2d8d64120b4b1b5d32cac9ef4` and evidence packaging `c23844dd65f7436780e03214aa2f02d2`. The packager only checks existing evidence and bytes; it never executes a proof mode. Its archived source and receipts describe the exact operations. The accepted private stage is `/workspace/p26-cell06-batch-boundary-20261128/stages/batch01`.

No larger batch, parallel execution or repaired-source transport was performed. Future continuation requires a separately anchored parent and whitelist; editing the frozen controller or recompiling successful owners is not a continuation mechanism.
