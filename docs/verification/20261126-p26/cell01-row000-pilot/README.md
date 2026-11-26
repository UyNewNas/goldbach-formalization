# Cell01 row000 finite verification checkpoint

Status: the first 22 owners passed normal compilation, independent kernel replay,
and complete owned-declaration audits in P3 job
`fd4d10cc40f14cb8a3137d1bf48204a0`. The separate 23rd owner,
`Cell01Row000OriginalFloorBridge`, remains pending. The generator itself only
authors candidate source and supplies no acceptance credit.

The source pilot contains 23 new owners, ordered in `cloud_order.txt`. The original
Cell00 owners and all generic arithmetic, determinant, prefix, higher-moment,
parser and decoder suppliers are unchanged.

## Exact scope

- `Geometry01BoundedAccess` transports the existing complete Cell01 shape facts
  to bounded lookups. It supplies the same original row → vertex ID → coordinate
  access equality for `r : Fin 144`, without a geometric or numerical claim.
- `Cell01Row000Input` selects only original row 0 and its original ordered IDs
  `[39, 35, 29, 28, 25, 13, 3, 1, 0]`. The typed literals are taken from
  `Geometry01DirectDecoding`; their equality with the bounded decoded accesses
  is a Lean obligation in this owner.
- The six arithmetic owners and their aggregator retain the original ten
  `RowDataChecksFor` clauses. `OldFloor` binds the actual decoded Moment01 row 0.
- `MomentEncoding` supplies the actual gap/deviation integer encodings.
  `MomentFactor00` through `MomentFactor09` each prove degrees 1–6, the original
  Q80 integer, and both floor inequalities using the existing prefix evaluator.
- `PrefixFloorChecks` closes the original five finite floor clauses using the
  literal `max(old,new)` operation. `OriginalFloorBridge` transports that result
  through the existing `HigherMomentsPrefix` and Q96 namespace bridges.

No other Cell01 row arithmetic, all-13 aggregate, ownership, or integral estimate
is asserted by the new owners.

## Original fixture identities

| Input | Bytes | SHA256 |
|---|---:|---|
| `eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json` | 470901 | `e19eee9d7e282cd3a618a71f12e93bcce28319485c9d0fd31bbeaf9f81a995a4` |
| `eighth-third-moment-refinement-20261009-a23-low-01.witness.json` | 75094 | `03e9360189414e240818a191e5b53102aa5e8c3a1e7c18fbd8553ba020078d8c` |

The generator reads these exact inputs and records their identities in both
manifests. Host calculations supply candidate rational literals only. The ten
original finite arithmetic clauses, moment old-floor consistency, Q80 candidates,
and saved new-Q96 candidate were checked for host consistency; this gives no
Lean or kernel acceptance credit. Each mathematical equality and inequality
remains explicit in the generated Lean source.

## Supplier and compilation boundary

The existing supplier roots needed by the pilot are:

1. `P2OriginalSaving19Geometry01Shape`, including its actual decoded input;
2. `P2OriginalSaving19Moment01Shape`, including whole original parse and decode;
3. `P2OriginalSaving19RowNumericsPure`;
4. `P2Winner9FastDetPure`;
5. `P2OriginalSaving19PrefixMoments`;
6. `P2OriginalSaving19HigherMomentsPrefix`;
7. `P2OriginalLogMomentQ96ArithmeticBridge`.

For the initial P3 finite phase, use `cloud_order_finite.txt`: it contains the
first 22 new owners. `Cell01Row000OriginalFloorBridge` remains a source candidate
for P1, using the HigherMomentsPrefix analytical suppliers now accepted separately on P1. The P3
driver never imports or compiles that bridge. The recursive project-source graph
and source hashes for the complete source pilot are recorded in
`SOURCE_CLOSURE.json`; external Lean, Mathlib and MathlibNt imports remain a
separate pinned environment boundary.

The finite P3 phase has 420 project modules: 22 targets and 398 existing suppliers.
Its frozen supplier manifest is `Cell01Row000_SUPPLIERS.json`; the driver reads
suppliers from `../cell00`, `../geometry01`, and `../moment01`. Every same-name
source and object must have the same SHA256 across those roots. Before Lean
starts, the driver installs those already verified bytes into the stage's own
`project/` and `objects/`, using hardlinks or an exclusive byte copy across
filesystems. It checks every installed identity and never overwrites a conflict.
The project part of `LEAN_PATH` contains only this complete `objects/` tree.

This installation fixes failed job `09da80e59b7f4b828b851df45f033d4c`: the prior
driver verified separate partial object trees but placed the new target tree
first. The import then selected that tree's `ImbalancedChen` directory, where
the existing `Geometry01Shape.olean` had not been installed. The 22 Lean sources,
22 audit sources, accepted supplier objects and proof obligations are unchanged.
Each new attempt records `SUPPLIER_INSTALLATION.json`; old verification attempts
and the v2 package are preserved.

The frozen supplier manifest and original P3 receipts retain their historical
normal-only entry for `P2Winner9HomogeneousRecurrence`. The separate
[`SUPPLIER_KERNEL_COMPLETION.json`](SUPPLIER_KERNEL_COMPLETION.json) joins the
P1 kernel receipt from `job_44f9f0a7371b4b16b477abae24876401`: both the source SHA
and the object SHA match the P3 supplier manifest, actual installed snapshot,
and exported P1 bytes. This closes the remaining supplier kernel item in the
combined evidence without changing the original P3 records or rerunning Lean.

The independent Moment01 supplier package is published at
[`../moment01-reuse/suppliers.tar.xz`](../moment01-reuse/suppliers.tar.xz), SHA256
`e5008887d1a13751396644280bd89c796052c2f3339d38f56c1143e5ae006181`.
It contains the 88-module matching source/object/receipt closure. This pilot
does not rebuild that package or its accepted owners.

## Reproduction

`tools/p26/generate_cell01_row000_pilot.py` reads the current, unchanged Cell00
row000 source owners as structural donors, and the established
`setup_and_generate.py` / `generate_final.py` workflow as the numerical-template
reference. It records all donor hashes and refuses to replace an existing output.
It has no Lean subprocess or cloud-tool invocation.

The cloud job completed all 66 steps in 191.924 seconds with sampled aggregate
process peak RSS 2,817,855,488 bytes. The individual step receipts separately
record 190.01490029697015 summed seconds and a largest step RSS of
2,793,291,776 bytes; these are different measurement scopes. Its successful attempt is
`20261126T034646622466Z`. The original `max(old,new)` formula is retained, and
only row 0 is covered by the new arithmetic/floor claims. The complete exported
receipts and same-object P1 recurrence backfill have been checked together;
their join is recorded separately from the historical P3 run.

The later v4 driver patch adds only an optional Mathlib package-directory
argument for P1 portability. This successful P3 job used v3; v4 has not been
used for a proof run. The mathematical sources and owned audit sources are
identical.

## Accepted evidence

[`evidence.tar.xz`](evidence.tar.xz) contains 308 individually hashed files plus
its export manifest. Its size is 783,012 bytes and SHA256 is
`ff86563d3aea2f49c899e8bf738cf656e29b73b95c6dea3b5bbf3e193c973f97`.
[`EXPORT_MANIFEST.json`](EXPORT_MANIFEST.json) is 197,586 bytes with SHA256
`448d9af0bbfa4f18ce5d3f40e504622b127022d9a0d136a4b548ae1caaab81d8`.
All 313 owned declarations are covered by exact serialized/environment
inventories, complete printed types and transitive axiom collection. The axiom
union is `propext`, `Classical.choice`, and `Quot.sound`.

Mathematical source comments retain their frozen pre-compilation wording;
current acceptance is recorded here and in the receipts without changing the
accepted source bytes. The separate original-moment bridge and the other 143
cell01 arithmetic rows remain outside this accepted 22-owner package.
