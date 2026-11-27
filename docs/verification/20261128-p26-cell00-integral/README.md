# Original Cell00 integral bound: verified

The original 56 Cell00 rows now give the closed theorem

```text
1055527309463438251 / 2^96 ≤ integral(cell 0, conservativeDensity).
```

`P2OriginalSaving19Cell00SourceAttachment.concrete_cell_integral_bound`
has no premises. The original row ordinals, nine rational vertices per row,
moments through degree six, Q80/Q96 scales and saved `max(old,new)` floors
are retained.

## Verification

| Scope | Result |
|---|---:|
| Recovered incoming project modules checked against the current context | 468 |
| Canonical declarations replayed by the unmodified Lean kernel | 28,059 |
| Additional serialized equation-theorem occurrences checked separately | 229 |
| Complete serialized declaration occurrences accounted for | 28,288 |
| New Cell00 target modules, normal / stock-kernel checks | 19 / 19 / 19 |
| Complete owned declarations in the new targets | 154 |
| New complete-owned audit invocations | 4 |
| Original simplex pairs separated | 1,540 |
| Original source gates / original vertices checked | 97 / 28 |

All inventoried targets are safe, total and nonaxiomatic. Their transitive
axioms are contained in `propext`, `Classical.choice` and `Quot.sound`.
The fixed Lean version is `v4.33.0-rc1`; Mathlib remains at
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` with its locked dependencies.

The current supplier context has 907 selected project objects. It combines
the accepted 439-module context with the recovered original finite owners
and floor bridge. Only the unavailable row-arithmetic aggregate was normally
rebuilt. Its original 56 numerical suppliers were reused and then checked in
the current dependency context.

Lean stores some imported equation theorems in multiple serialized modules.
The audit accounts for every canonical and shared entry. It checks identical
names, types, universe parameters and mutual-block metadata, and sends each
of the 229 serialized shared proof bodies to `Kernel.Environment.addDeclCore`
at trust level zero under a fresh audit-only name. There are 228 identical
proof bodies and one different proof body of the same type; all 229 passed.
The failed earlier inventory comparison and its log remain bound in the
capsule. The successful 1,530.055-second canonical replay was reused only
after rechecking the complete source/object, runtime, replay-code and log pins.
The completed owned audit took 338.303 seconds.

## Integral attachment

The accepted rational affine construction gives the actual physical
simplex and original moments for every row. The saved Q96 floor bounds its
actual density integral. Exact proper affine separators put every pairwise
intersection on a null wall, allowing the 56 integrals to be summed over
their union. All 97 original gates hold on all 28 original vertices.
Removing the proper source walls gives almost-everywhere inclusion in the
actual strict source cell. Integral monotonicity yields the displayed bound.

The context union contains 926 project objects. `project-objects.tar.xz`
contains only the 19 new target objects and the rebuilt aggregate. Its exact
bytes, parent capsules, source/command/log pins, complete type inventories
and final external-input readback are recorded in `CAPSULE.json` and the
phase subdirectories. The original finite source/object archive is on branch
`artifacts/p26-cell00-suppliers-9518e531726e-20261128` at
`e70a90d15ca73917cc500f4750bb205074fc2dda`.

## Replaying the checks

After restoring the pinned objects and `LEAN_PATH`, the independent supplier
steps are `lean --trust=0 --run tools/p26/cell00-integral/ReplayJoin.lean
/workspace/p26-cell00-next-20261128/INCOMING_MODULES.json` and
`lean --trust=0 tools/p26/cell00-integral/OwnedSuppliersAudit.lean`.
The published receipts retain all additional resource and elaboration flags.
`qualify_suppliers.py` is the preserved historical controller for the passed
kernel replay. `resume_owned.py` validates that exact replay checkpoint and
the extended canonical/shared inventory. The new leaf phases are verified by
`verify_phase.py` with `physical`, `separation`, `packing`, and `source`.

P2.6 remains open: Cell00 and the previously accepted Cell05 have source-cell
integral bounds; the other eleven original families and the global endpoint
still need their own checks. `original_full_snapshot_verified` remains false.
