# P3 independent01: FirstExitTree / FiniteSieveModel strict-linter repair

Status: SOURCE_REPAIR_PENDING_ACTUAL_RETRY. Compile credit = false; kernel credit = false.

## Actual failure and scope

P3 job `c2893ccf975843ecbcb24b39bba6ebe5` used source commit
`086696e51088eb93942abf2fcc1ce48e148ad842`. The complete log is
`p3-independent-symbolic-01.log` in this directory, 25,234 bytes,
SHA256 `aedb2e25f9de933b21f636e26499e1571f2c451573e8a6eb42fa8fa13c74f919`.

The only two direct failures were 26 strict-linter errors in FirstExitTree
and one in FiniteSieveModel. The root reported 51 fresh diagnostic passes,
39 reused inputs, and stable inputs; none of those other modules was edited here.

## Existing work checked before editing

The existing `verification/part2/p24_ci_candidate_index.json` entries
`overlay-015` and `overlay-007` already identify the pre-repair files as exact
successful CI overlays. That historical evidence is preserved; it is not a
pass for the present strict-linter invocation or for the changed source.

The independent stage reviewer inspected only the known P2 export
`docs/verification/20261125-p2-resume/evidence-numerical80-111-rank-20261125.slim.tar.xz`,
member `packages/all.tar.gz/context/records.json`. Its 16,227,671 bytes have
SHA256 `ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`,
matching that package's `ORIGINAL_EXPORT_MANIFEST` binding, with 619 top-level records.
Both target rows have cache schema 2 and exit code 0, but their source hashes are:

| Module | Source hash in the old 619-row export |
| --- | --- |
| FirstExitTree | `6ab5eeb136969f76afc8fcc83dfa211985e0b7ffe85e89dab0702f381ad42a6b` |
| FiniteSieveModel | `9112139c826b1ebf81b12d69b873c179a2cbd6e17305ec3d0818032fb34bfb0c` |

These differ from both current pre-repair hashes below. The examined export
therefore cannot accept these current bytes under the exact-source contract.
This local check does not claim to have inspected the live P2 registry.
No full archive or CI re-audit was performed.

## Minimal changes

- FirstExitTree: rename exactly six reported unused lambda binders to `_`
  at original lines 63, 65, 97 and 172; retain their positions and argument count.
  Remove exactly twenty reported unused simp arguments at lines 137, 139,
  206, 220, 224, 225, 239, 269, 291, 319, 346, 371, 480, 786 and 803.
- FiniteSieveModel: replace the reported unnecessary
  `simpa using (squarefree_one : Squarefree (1 : ℕ))` at line 47 with `simp`.

No linter option, theorem statement, import, branch condition, recursive call,
list concatenation order, mass update, sign flip, or residual Euler product changed.

## Frozen 1106 manuscript and classification

Read the frozen `UyNewNas/chen-imbalanced-semiprimes` commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/argument.tex`, lines 221–236,
  equation `eq:current-upper-exit`; Git blob
  `90234d94460f1d7d59982635d7bf54c9b19250da`.
- `paper/release-20261106/en/sieve-appendix.tex`, lines 41–80,
  lemma `sv:first-exit` and equation `sv:upper-exit`; Git blob
  `bf8bae30ff18f21d716138af0cc6d9fbb4a80747`.

The manuscript partitions excluded divisors by their first excluded prefix;
the remaining smaller primes form the residual Euler product, with the positive
correction sign supplied by odd first-exit rank. The code retains this same
processing and selection order. These changes are class (1), formal expression
and strict lint only. No omitted mathematical deduction was supplied and no
substantive manuscript gap is asserted.

## Static checks and exact source identities

All 74 theorem headers and 17 definition headers are byte-identical.
All 18 definition/structure blocks are byte-identical after normalizing only
the six approved unused binder renamings. The changed-line set is exactly
the set listed above; the complete log contains the corresponding 26 + 1 errors.
`git diff --check` passed. No prohibited proof token or linter suppression was added.

| File | Before SHA256 | After SHA256 |
| --- | --- | --- |
| `ImbalancedChen/FirstExitTree.lean` | `e12ba076eb7c79170b8f1dc18171dbb9fa94af14232018d7896a817a0f12fa72` | `490490bf81eb411e7fae00805ee02464f5fccee040d621d33fd2ece73dc1c117` |
| `ImbalancedChen/FiniteSieveModel.lean` | `7a8e872dbf76ae1285507f20b497737c3fe0c91ebe1b6c34f26ea817ae8f54e8` | `3bda22d12455339b6678ebd14830379e79f488ebfee9605db2927af26529a594` |

No Lean/Lake, cloud compilation, kernel replay, or Git commit was performed
for this repair. Actual strict compilation remains the root's next step.
