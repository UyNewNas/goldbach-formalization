# Existing numerical work after Block01

Read-only result: **Block02 has complete existing P2-private evidence; Page0048 has normal compilation only.** This task did not query a live cloud environment, change the external repository, run Lean, or contact an external worker.

The external repository remains at `ac9e6404a9ff7e2f980da6eaa8b80a19677044c6` on `codex/p2-terminal-assembly-20261124`. The Block02 evidence files are staged additions, not a new commit or a remotely confirmed publication.

## Complete new scope

| Scope | Normal | Independent kernel | Complete owned audit | Original row range |
| --- | --- | --- | --- | --- |
| `P2Winner9NumericalPage0032` through `0047` | 16 receipts, exit 0 | 16 receipts, exit 0 | 34 declarations per page | 512–767 |
| `P2Winner9NumericalCheck02` | exit 0 | exit 0 | 1 declaration | Aggregates the same 512–767 range |

There are **17 modules, 545 distinct owned declarations, and 256 new original rows**. Combined with previously accepted Blocks00/01, the saved P2-private evidence covers 768 rows, ordinals 0–767, leaving 10,258 of the 11,026 selected inequalities outside this accepted prefix. This is not a P1 joint-import or full-owned acceptance result.

The source, object hash, normal closure signature, independent replay binding, full owned inventory, declaration types and axiom lists were checked for all 17 modules. Environment and serialized owned-name inventories agree with all 545 reported names. The only reported axioms are `propext`, `Classical.choice` and `Quot.sound`; no selected declaration is marked axiom, unsafe or partial. The page ranges are bound to the actual exported `checked` theorem types and unchanged source files, not inferred from subsequent tasks.

The source copies match existing candidate files committed at the observed `ac9e6404…` HEAD. The 17 normal/replay/audit receipt sets are bound to the archive below; 121 selected archive members were checked by byte count and SHA256. The old 74-module physical source closure and Blocks00/01 were not rescanned.

## Existing evidence location

External path:

`/workspace/scratch/89135e928d3c/goldbach-p2/docs/verification/20261124-p2-private/evidence-numerical32-47-20261124.slim.tar.xz`

```text
Bytes: 513608
SHA256: 91c8489fd5b9f0e70086689179b263da1ab77563b512d9902fb8e840c72911f9
Git index blob: 99e74fb2e03012588926309a20602d7d41471a1c
Original export manifest SHA256:
7fab475ce34e8cc0bb7a31e65b1bb9474861849c24b2fa2abb57bcc124ddc248
```

Saved job `23c42d0089b04ec38afe8f5bdad7e5d4` exited 0 after 1341.086896588 seconds. It reused the valid initial Block02 page compilations, completed the remaining pages and Check02, and finished the independent replay and owned audits. `INDEX.json` contains each of the 17 exact source/object/type/axiom/range bindings and the archive member hashes. The archive contains receipts and object fingerprints, not `.olean` objects; no object was copied or renamed by this task.

## Later boundary

Saved job `ef8c7238a2d64f6faa27a03240f8d209` really compiled Page0048 and exited 0, but explicitly records no independent replay or owned audit and grants zero accepted modules. It remains outside complete reusable coverage. No later complete numerical receipt was found in the inspected local saved records. This statement does not claim to know the state of unqueried live or queued external jobs.
