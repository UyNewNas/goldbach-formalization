# Part 1 stored historical cap permit: actual verification

## Result and exact receipt

**Status: VERIFIED.** This independent permit milestone passed three
strict original-frontend compilations and three original `leanchecker`
calls, all with exit code `0`. Its complete defining-module audit contains
36 declarations: 14 in the production module and 22 in the probe module,
including generated declarations. The only observed transitive axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

The exact machine-readable [VERIFICATION.json](VERIFICATION.json) is a
byte-for-byte copy of the final receipt collected at
`2026-10-12T12:56:10.056234+00:00`. Its SHA256 is
`7f687c1d1b61ec3142de63f1458b5dcf650928348e6b4231b871a121c99d4ee1`. The original receipt location was
`/workspace/scratch/127408f63891/lean-runtime/part1-permit-final-receipt.json`.
The report below records that receipt's actual execution and scope; no
additional compilation or checker invocation was used to prepare it.

| Reference | Complete identity |
| --- | --- |
| Mathematical baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Previously verified P1 milestone | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` |
| Repository head when this receipt was collected | `7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| Pinned Lean release | `leanprover/lean4:v4.33.0-rc1` |
| Official Lean source commit reported by the frontend | `62eed1db4d67327ec8120be05f1a1b0847d74561` |

The repository head in this table is the inherited parent of the new
permit files, not a claim that the permit source was already committed
under that SHA. The receipt precedes the eventual delivery commit and
binds the new files by their complete content hashes.

## Three current targets and complete source/object bindings

Every target below was actually compiled in this permit run at
`trustLevel = 0` with strict warning handling, and its defined declarations
were subsequently replayed by the original checker. Source hashes were
unchanged before and after these operations. The recorded `.olean` hashes
also remained unchanged across replay.

| Target | Source SHA256 | Main `.olean` SHA256 |
| --- | --- | --- |
| `ImbalancedChen.StoredHistoricalBoxPermit` | `50a9dc07e98046a664711572bcf69b58a528c0a97502bbd9f75de245dd43bc0d` | `c05b355bb77a95468850321807846cfb743955e2a77d5e2aafca02185bc4a8ee` |
| `verification.parts.p1.round2.permit.StoredCapProbe` | `41b1ac2242e8b4e84b72c98772bb52b7ec9814807466b9ef19ccb15f4e4dff49` | `9b7282d02b03c79a8ae6cc73520386934b09df64402f05ea91d2e57ae1c43cd8` |
| `verification.parts.p1.round2.permit.StoredCapAudit` | `c5cb2cd40e7d8b591302ccb2e3b0e36c2b3a99a786385316feeec62db4617b33` | `1e2783cf117947f93707fe78d3b1bd0d403330d3b9abf9144c3fb02981831950` |

| Source | Actual strict compile exit | Actual original checker exit |
| --- | ---: | ---: |
| [StoredHistoricalBoxPermit.lean](../../../../../ImbalancedChen/StoredHistoricalBoxPermit.lean) | 0 | 0 |
| [StoredCapProbe.lean](StoredCapProbe.lean) | 0 | 0 |
| [StoredCapAudit.lean](StoredCapAudit.lean) | 0 | 0 |

The strict run is recorded in the receipt's `closure.execution_result`;
its original result file has SHA256
`8c91d47aad24ce05dcefba18ec9bd94471644bcc99f2ec973baad4c581ce64a6`.
The complete source snapshots, command arrays, compile logs, artifact
parts, direct-import object hashes, and replay logs are bound inside the
receipt and the evidence archive. These are current-source results for
these three targets.

## Original toolchain and actual execution path

The stock Lean CLI fails during startup in this environment, before
parsing a project source, with `error: failed to locate application`.
The recorded `lean --version` attempts exited `1` both with and without
explicit release-root environment variables. The original `lake --version`
exited `0` and reported the fixed Lean release. The startup observation
record is bound by SHA256
`e42c8a012bdae189219f07cf1d2a2442e65392f4feffb645ec18bad6cd8a51c7`.

Actual project compilation used the unchanged official
`Lean.Elab.runFrontend` API through the original official Lake runtime.
The driver uses `Lean.enableInitializersExecution`, sets `trustLevel = 0`,
and enables `warningAsError = true` for the three targets. The actual logs
record `FRONTEND_OK` for each target. No metadata adapter was enabled
during compilation or replay. The shared operating-system file lock
serializes frontend and checker execution; it does not alter their trust
settings or replace any proof check.

The subsequent replay invoked the original `leanchecker` executable
once for each of the three named modules, sequentially, with `--verbose`.
All three calls exited `0` and reported their requested module. The calls
did not use `--fresh`: the checker replays declarations defined by the
requested module, including its private data, while loading imported
dependencies. This result does not assert a fresh replay of every imported
declaration.

| Rechecked original binary | SHA256 |
| --- | --- |
| `lean` | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |
| `lake` | `60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3` |
| `leanchecker` | `ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a` |
| `leantar` | `06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3` |

The official release archive hash is
`25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210`.
The receipt includes the restoration records and exact driver sources.
The available [check.sh](check.sh) gives stock-CLI reproduction commands
for an environment where the pinned CLI starts. Its execution is not
claimed by this receipt. Neither a stock `lake build` nor a full-repository
build or replay was executed for this independent result.

## Complete declaration audit and actual types

The audit enumerates the actual Lean environment by defining-module
metadata, includes private and compiler-generated declarations, and runs
the bundled transitive `collectAxioms`. It rejects unsafe declarations,
custom axiom declarations, and dependencies on axioms outside the allowed
standard three.

| Audited defining module | Actual declaration count |
| --- | ---: |
| `ImbalancedChen.StoredHistoricalBoxPermit` | 14 |
| `verification.parts.p1.round2.permit.StoredCapProbe` | 22 |
| Total | 36 |

The production census is exactly its two public definitions and ten
public theorems, plus `ImbalancedChen.storedBoxCapCheck.eq_1` and
`ImbalancedChen.storedMeshCapCheck.eq_1`. The audit module itself is the
third compiled and replayed target; its command inventories the two
modules in the table. The count of 36 is not a count of all imported
supplier declarations.

[KEY_THEOREM_TYPES.md](KEY_THEOREM_TYPES.md) preserves all twelve complete
source declarations and binds each by full name, kind, and defining
module to the actual audit. Its Appendix A contains the literal decoded
pretty-printed types of all fourteen production declarations, including
the generated equations. No abbreviated type substitutes for a dependent
field, hypothesis, strict endpoint, or selected-subproduct filter.

The actual raw audit log has SHA256
`f942c8432aee8ae28d70dc97dd804ffa0a1323e9f55edfb55d999c5f74a805f5` and was read from
the `log` entry for `verification.parts.p1.round2.permit.StoredCapAudit`
in the actual compile result. Its recorded path is
`/workspace/scratch/127408f63891/lean-runtime/logs/round2/permit/compile/attempt-20261012T124921086741Z/modules/verification.parts.p1.round2.permit.StoredCapAudit.log`.
The 36 distinct declaration records, the reported module counts, the
fourteen-member production set, and the standard axiom sets were checked
against both the raw log and the final receipt.

The probe exercises an accepted stored cap that differs from the automatic
midpoint, both strict equality endpoints, stronger inherited `old`, an
empty mask, a lower ceiling, and one selected common-mesh cell. Its
computed decisions use `decide +kernel`. These are interface regression
examples; they do not constitute the adopted manuscript's actual Part 2
tables, a performance benchmark, or a numerical K/c certificate.

## Dependency closure and unchanged pins

The independent source closure has exactly
`3384 = 3 + 13 + 3368` modules:

| Provenance in this permit run | Count | What the receipt establishes |
| --- | ---: | --- |
| Newly compiled local targets | 3 | Current strict compilations followed by current original checker calls. |
| Reused local supplier modules | 13 | Archived successful objects reused with current source, object, and direct-import hashes checked. |
| Official cached supplier modules | 3368 | Cached sources and available artifact-part hashes recorded in the dependency binding inventory. |
| Total source closure | 3384 | Sixteen local modules plus 3368 cached supplier modules. |

This distinction is part of the verification claim: the closure was not
freshly compiled or replayed in its entirety. The receipt states that all
local source/object/direct-import bindings were rechecked and that cached
source and artifact-part bindings were recorded. Its plan hash is
`ca26cefb08059294a692e795225a54e1c10e031cfe36bf524e66a6ead0c98bb9`; the full dependency-binding inventory
hash is `9768af50ad15bc25ae155cb356a5f24fbb47c833175c85af888f14e86c0b6dc0`.

All eleven dependency checkouts matched their exact manifest revisions,
with no tracked changes reported. The observed heads are:

| Dependency | Expected and observed full revision |
| --- | --- |
| `goldbach` | `09b97db5764ade1246bfb77206baa1b124760958` |
| `mathlib` | `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` |
| `LeanArchitect` | `78dd66840d3efe8c824c699fc03381cec817c271` |
| `plausible` | `b1c4a69a7e247ab7df20460212001673d74f08c0` |
| `LeanSearchClient` | `0498c7c070c143a3bf7379f4d99a2c63bb9d9715` |
| `importGraph` | `18a90119a5d316358fde6c86e0ca24e59212e32c` |
| `proofwidgets` | `b1436dc749e722c9920036b52cdc43b3451d0b69` |
| `aesop` | `57d3325be72a842920813bcb40f96a6f7393c185` |
| `Qq` | `ee41917ae11d38479fb8fb24745f7ca4bf0a784d` |
| `batteries` | `41bd267b3f6b7252f6676af46d4ffc6783b64de9` |
| `Cli` | `da07ca808b6718cb2aed14dba154e5a08b8f8ecf` |

The project toolchain and dependency declaration files were preserved and
are bound as follows:

| Project pin file | SHA256 |
| --- | --- |
| `lean-toolchain` | `62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef` |
| `lake-manifest.json` | `35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849` |
| `lakefile.toml` | `b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254` |

## Separate historical results and pending integration

The previous six P1 targets retain source/object matches to the verified
`b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` milestone. The receipt explicitly
marks them `compiled_in_permit = false` and `replayed_in_permit = false`.
Their previous receipt hash is
`2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1`. Those preserved results
are not counted as current permit compilations or checker calls, and the
three current permit results are not substituted for their historical
receipt.

At this receipt, the separate four main round-2 targets remain
**UNCOMPILED CANDIDATES** pending their own actual gates:

- `ImbalancedChen.HistoricalUpperFiveCellGeometry`;
- `ImbalancedChen.ActualHistoricalFifthCellIntegral`;
- `verification.parts.p1.round2.HistoricalCellProbe`;
- `verification.parts.p1.round2.Part1HistoricalCellAudit`.

They are outside this permit's three-target verification and the verified
import proposal. The independently reported complete inherited-fifth
integral source remains **SOURCE_PENDING**. This result proves neither
the complete adopted historical saving/integral combination nor a final
K/c bound.

The final [P0 intake](../FINAL_P0_INTAKE.md) records that
`28fd630ef7cc38eba86beb6c0ba123336b5d05f2` now formally accepts and imports
all four prior verified P1 production leaves from `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f`.
Exact-head GitHub step metadata reports successful full-root build,
original checker, axiom audit and complete-type export at that P0 SHA.
This intake did not download its raw artifact or execute a new local
root gate, and those earlier integration results do not cover this permit.

For that current P0 root, use the unapplied incremental
[PART0_28FD_PERMIT_IMPORT.patch](../PART0_28FD_PERMIT_IMPORT.patch). The
actual `git apply --check` against an unchanged, byte-exact copy of the
fixed P0 root exited zero; [PART0_IMPORT_CHECK.json](../PART0_IMPORT_CHECK.json)
binds its base, source, patch and command. The frozen cumulative
[INTEGRATION.patch](INTEGRATION.patch) remains an unapplied proposal
against the original P1 parent root and is retained unchanged in this
permit's evidence archive. Part 0 must run its canonical integration
gates after adding the new permit. Those new-permit integration gates
remain pending.

The checked rational `old j` must still be identified with the actual
effective inherited ancestor value before these local permits are applied
to a historical policy. Part 2 must supply the fixed adopted table and
prove its finite check and those history equations. Coverage, actual
carrier dictionaries, global support/factorization, the separate old/new
own-cube interfaces, and the remaining adopted integral ledger obligations
are not inferred from this local verification. The receiving Parts and
precise scope are recorded in [HANDOFF.md](HANDOFF.md).

## Artifacts and reproduction material

| Artifact | Contents |
| --- | --- |
| [VERIFICATION.json](VERIFICATION.json) | Exact final gated receipt with current source/object, import, command, dependency, replay, audit, and toolchain bindings. |
| [KEY_THEOREM_TYPES.md](KEY_THEOREM_TYPES.md) | Complete source definitions/theorem types and actual audit pp types, with the full production census. |
| [HANDOFF.md](HANDOFF.md) | Mathematical interface, field ownership, scope, and receiving Parts. |
| [EVIDENCE.tar.gz](EVIDENCE.tar.gz) | Archived original text evidence; compiled binaries are represented by hashes rather than copied as deliverables. |
| [ARTIFACT.json](ARTIFACT.json) | Sealed archive digest, size and counts; the complete file/hash inventory is `MANIFEST.json` inside the archive. |
| [archive_evidence.py](archive_evidence.py) | Evidence-only collector for the existing successful receipt, without invoking Lean, Git, or CI. |
| [check.sh](check.sh) | Stock-CLI reproduction commands for a compatible environment; not a record of stock-CLI execution here. |
| [INTEGRATION.patch](INTEGRATION.patch) | Frozen, unapplied cumulative import proposal against the original P1 parent root. |
| [PART0_28FD_PERMIT_IMPORT.patch](../PART0_28FD_PERMIT_IMPORT.patch) / [PART0_IMPORT_CHECK.json](../PART0_IMPORT_CHECK.json) | Preferred incremental permit-only proposal against the exact current P0 root, with actual successful text applicability check. |

The evidence archive's digest is supplied by its sealing manifest rather
than invented in this report. Receipt and source identities above are
already fixed independently of that archive packaging.
