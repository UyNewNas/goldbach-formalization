# saving19: original physical vertices, gates, and pulling ledger

Parent: `652f83ecd0ef9a13f0bdecd17ade496662438b0e`; original source baseline `6848b4a69fd6f25806989dac7d305d27a6cd204e`. The current commit is identified by Git; no self-referential SHA is inserted. This is a finite data replay and handoff. It adds no Lean proof and discharges no formal premise.

## Exact source and manuscript scope

The complete source files below were read in this run, in addition to the prior handoffs. File hashes are SHA-256; blobs are Git object IDs.

* `docs/source-only/20261102-resume-30m/saving19_original28918/P2OriginalSaving19Archive.lean` (prior handoff blob `45220db20a3d99a759f875d2c7d5f1bd72a6cdf7`): typed original inputs and row-index/shape candidates.
* `.../saving19_original28918/P2OriginalSaving19Original28918.lean`, SHA-256 `ed126d258139d3ee671f164852f816255138657a035f74af67a0f610637c24b4`, blob `2fac317b16c2b27050ff691ac855930b02d15035`: `PhysicalQ`, `RowDataChecks`, `original_data_checks`, `original_saved_vertex_values` and `primitiveRow`.
* `.../saving19_owned_integral/P2OriginalSaving19OwnedSource.lean`, SHA-256 `e18f481c54879b7a51346db7f3549c1ac12f393a194b79322a600e7bf89c1c8b`, blob `23a4f4688b4e4721aff135cc2ef354f6dda1b6cf`: `original_gate_checks` requires all 97 per-cell gates to have nonzero linear parts and be nonnegative at every original vertex. `support_off_walls_in_cell` is the existing source candidate transferring these checks to strict ownership away from null walls.
* `.../saving19_owned_integral/P2OriginalSaving19PullingOwnership.lean`, SHA-256 `87fd625fc864128a001ba49deab415fd82eb944ee3c23bda036762c199f94dde`, blob `49a15fb31f001c8ac627b2b333d283b4f69e4277`: `original_pulling_checks`, `original_vertex_sets_distinct` and `original_polynomial_faces` are separate closed proof requests. The first includes the ordered pulling recursion, each face's maximal facet intersections, and a zero-set gate for each original facet. The last requires a polynomial supporting-face check and was not evaluated by this replay.
* `ImbalancedChen/OriginalAscendingThirteenLiteralAffineRows.lean` at registered source commit `d5f392f6717227ab94ad4004044a037ac83be877`, blob `48b4f14ec8baf09b9760289f65a7385bf6595e9e`, SHA-256 `129e18e8683582b2e0f8438e9baca31bec1e4b3551273ee079b35007fb55e592`: the *actual* 103 nine-coordinate rational `literalPool` vectors and the 13-by-97 `literalIndex`; `exportedCoefficients i r = literalPool (literalIndex i r)`. The companion `OriginalAscendingThirteenCellOwnership.lean` and `OriginalAscendingThirteenExportOwnershipJoin.lean` were also read, to distinguish strict source rows from closed vertex checks. The source's coefficient-to-semantic equality and strict-cell theorems are unevaluated Lean candidates.

The manuscript pin is unchanged: `9731290e8f53cffda44129906cde6a965eaa869b:paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, SHA-256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`, matches the prior chain pin. Lines 365–374, 435–453, 1327–1340 and 1354–1370 were reread: causal ancestor retention, new-minus-current-parent, factor 4, legal subset sufficiency, and same-domain replacement rather than second payment. No parameter or pin was changed.

## What was actually replayed

New `check_physical_ownership.py`, SHA-256 `5e992c6bd0385cf834efec01f938531916b5f63c3e73aac77d5ac4c4bfb807b9`, blob `00fc4d77fe19ca6c4e0aa131d935a58457e677f4`; output `PHYSICAL_OWNERSHIP.log`, SHA-256 `618480fe842e80fc90b126edf55abc624e336d799c1b968f1dd89b13a55a4d99`, blob `deff6315b55a7101db70f466ac25f1d0e20ca523`. The script hashes the exact Lean coefficient bytes, the publication manifest (SHA-256 `fccf400489947123dd088d7f6087b76dc7b777259a0348d9c31601f75565684f`), and each of the 13 original geometry witnesses against its manifest size and SHA-256. The prior handoff records the authenticated full witness package and all 26 original inputs.

The exact `Fraction` checker evaluates every clause of `PhysicalQ` for all 1,097 original cell-local vertices. It reads the source's 103 literal coefficient vectors and 13-by-97 indices, verifies every linear part is nonzero, and checks 106,409 vertex/gate pairs for **nonnegativity**, not strict positivity. It checks that every recorded facet's vertex set is the zero set of some corresponding gate. It then reconstructs all 3,704 recorded faces' max-pivot/maximal-intersection/count conditions and replays the original ordered pulling recursion exactly against all 28,918 recorded rows; unordered vertex sets are distinct within each cell. Each cell's results appear in the complete log.

This data check covers the finite physical and gate clauses and the specified pulling-ledger data, not the parser's Lean evaluation, the `original_polynomial_faces` condition, the proof of null overlap, strict membership on boundary vertices, or any actual prime occurrence. It does not prove equality of S12's held-sixth policy and the T03 licensed/full sixth parent. Gap-weighted simplex factors, reciprocal-prime frontier weights, and unit-weight physical frontier are distinct; no cross-dictionary identification is inferred. No new mathematical premise was removed.

## Reproduction and status

In the existing environment, Python 3.12.14, single process, no resource enlargement; shell `ulimit -v` reported unlimited. From `/workspace/scratch/8c9d3a651a4e`:

```sh
python3 -u /tmp/p2_saving19/check_physical_ownership.py \
  --manifest /tmp/full87.json \
  --coefficients /tmp/p2_saving19/OriginalAscendingThirteenLiteralAffineRows.lean \
  --witness-dir goldbach-research
```

Command exited 0; full output is the committed log. `python3 -m py_compile /tmp/p2_saving19/check_physical_ownership.py` exited 0. A direct `lean --version`, `lake --version`, and `lake env lean docs/source-only/20261102-resume-30m/saving19_owned_integral/P2OriginalSaving19OwnedSource.lean` from the incomplete formalization checkout each exited 127: command not found. Thus no elaboration occurred. The workspace cannot supply a matching Lean executable or import closure; no installation, CI, resource increase or pin change was performed.

SOURCE_ONLY=yes; COMPILED=no (UNCOMPILED); KERNEL_REPLAYED=no; TRANSITIVE_AXIOM_CHECK=NOT RUN; INDEPENDENT_REVIEW=NOT RUN; finite Lean bodies=UNEVALUATED. Declared pins: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; installed revisions remain unverified. No new external mathematical input is introduced; the inherited external input provenance and its transitive verification remain as in the earlier source registries.

Next: on the authorized matching existing environment, stage the registered effective source map and witness files and minimally compile the exact T03 bridge and actual consumer closure, preserving logs and limits; kernel-replay and audit transitive axioms. Continue checking the same actual policy, parent, frozen history and ordered weighted occurrences; only assert a mathematical gap if a required concrete consumer fails. In particular, the ideal-cap reorder theorem does not by itself establish a finite rounded-policy equality. No saving16 per-corner PP requirement is assigned to this node.
