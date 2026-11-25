# P2.5 saving16 continuation — 2026-11-25

Status at source checkpoint: **SOURCE SELECTED; current P2 closure not compiled or kernel accepted. Full P2.5 remains open.**

This continuation uses the 2026-11-06 manuscript, the current P2 branch at
`a929011ec95843553fc2e10b7291c8077e0952c0`, the original full87 manifest, and
existing P1 repairs at `298670f119d24874b719facb3ef756f1e01223a1`.

The new `P2Saving16Full87IntegralIdentity` identifies the whole original
saving16 integral with exactly its fourteen original full87 summands. It also
partitions the full87 sum into that contribution and the unchanged complement
of 73 source integrals. IDs 0 through 14 except 7, all 96 affine rows per cell,
the original factor-four kernel, the two residual denominators and the eight
coordinate factors are preserved. No quantitative PP, Q96 lower bound, or
complete P2.5 acceptance is inferred from this identity.

The original `P2OriginalSaving16CellOwnership` and
`P2OriginalSaving16Full87SourceBinding` are reused. Thirty original archived
logical modules are restored; existing P1 proof repairs are reused where
available. Six restored original owners import their already accepted
definition cores and remove exactly 34 byte-identical declarations. This is
the previously published owner movement, not a replacement of the original
sources, cells, caps or integrals.

Evidence:

- `SOURCE_SELECTION.json`: original minimal source-selection analysis.
- `P1_SOURCE_REUSE.json`: the eleven existing P1 repaired sources reused.
- `OWNER_MOVEMENT.json`: exact declaration identity and before/after hashes.
- `CURRENT_SOURCE_CLOSURE.json`: the complete current source/import graph.

Independent static mathematical review found no changed kernel, hidden
premise, double-counted saving or lost complement. This review is not Lean
compilation or kernel evidence. Current strict compilation, independent
replay and owned-declaration auditing will be recorded separately.

The initial native-context preflight (`face0a20e6874991a93f7c9266cc443e`)
reported a Lean memory exception while loading/elaborating
`ImbalancedChen.RosserEndpointBridge` with `-M5800`. The verification driver
therefore uses one worker and at least 11264 MiB for closures requiring the
qualified native environment. Non-native settings are unchanged; the
explicit `--external-memory-mb 0` option preserves the caller's requested
worker and heap settings. Actual Lean commands remain in the receipts, and
all source/dependency checks and strict proof flags remain unchanged. This
resource adjustment is not evidence that the failed module has passed.

## Q96 source preparation

The original Q96/ownership chain is now selected from thirteen existing
P1 source files, including the already repaired `SimplexMoments` and
`SourceMeasure`. Six unchanged affine-geometry declarations have been
moved from `P2OriginalSaving19OwnedSource` to
`P2OriginalAffineSimplexGeometry`, retaining their original namespace,
types and complete proof bodies. The old owner imports the new module;
saving16's pulling-ownership module changes only that import. The
`OwnedIntegral` source closure is reduced from 361 to 357 modules and no
longer reads the unrelated 26 M19 numerical inputs. The original fourteen
saving16 witnesses, 39741 simplices and exact Q96 endpoint are unchanged.

P1's live copies of all fourteen witnesses have the exact registered sizes
and SHA256 hashes. This authenticates the inputs; it does not evaluate
the Lean finite checks. Current Q96 elaboration and kernel acceptance are
still pending. The original 355-module integral-identity source graph is
unchanged by this preparation.

The production import scanner previously misread a double quote in a
Lean `Char` literal in the existing pure JSON reader. Its fix has five
passing regression cases, including the actual reader. The old/new
scanners return identical import graphs for the existing 355 modules,
and the fixed production runner now scans all 357 Q96 modules normally.

Additional evidence:

- `P1_CACHE_AND_INPUT_INVENTORY.json`: live read-only cache/input census;
  object existence is distinguished from historical kernel acceptance.
- `Q96_EXISTING_INPUTS_AND_SOURCES.json`: original input and source reuse.
- `Q96_EXACT_SOURCE_INSTALLATION.json`: thirteen exact source preimages.
- `AFFINE_SIMPLEX_DECLARATION_IDENTITY.json`: six byte-identical declarations
  and the two precise owner/import changes.
- `Q96_LIGHT_SOURCE_CLOSURE.json`: complete 357-module source graph.
- `IMPORT_SCANNER_REGRESSION.json`: observed failing and passing checks.
- `ACCEPTANCE_SCOPE.md`: actual P2.5 responsibilities and the cross-P3
  distribution boundary, without promoting a target definition to a theorem.

## Observed dependency compatibility failures

Strict P2 task `79d36731cb5e434dbbbdead05f3573c5` actually compiled source
checkpoint `0cc5e76506e2d3ca88d3d6a7df8185d468c766b6`. The larger heap
allowed `RosserEndpointBridge` to pass that compilation step. Later the
required dependency graph exposed ten failing source modules; these are
recorded in `OBSERVED_COMPATIBILITY_REPAIRS.json` with exact before,
existing-donor and after hashes.

Eight existing `v3repairs` proof sources are reused. Four reported
deprecated Set names are replaced by their exact current aliases, and
one orphaned documentation comment left by the H3 definition-owner move
is removed. Independent static review found unchanged imports and all
338 top-level declaration headers. It also verified the eight existing
source copies byte for byte before the listed API renames.

Historical passed downstream audit contexts bind several donor source
hashes, but those contexts do not contain the repaired modules' own
independent replay and complete declaration receipts. These repairs are
therefore **pending current strict recompilation and audit**. The running
batch and its eventual postcheck are separate evidence; no whole-P2.5
acceptance or new mathematical premise is inferred.

Later diagnostics in the same batch added three more repairs, bringing
the observed list to thirteen modules. `P1HistoricalFourthResidualIntegral`
reuses its exact existing v3 repair. `P1FourthNearOneKernel` reuses the
newer P14/P15 source, including the already corrected Suzuki namespaces
and the explicit original `s = 2` argument. The fixed external goldbach
source confirms those declarations and their unchanged hypotheses.
The remaining change removes one reported unused `hnot` simp argument
while preserving its use in the preceding proof. These three sources
also remain pending recompilation.

The initial batch has now finished with exit code 1. Its complete output
is `initial-strict-compile.log`, bound by SHA256 in
`INITIAL_STRICT_COMPILE.json`. The final driver summary has 272 successful
records (97 reused and 175 fresh strict compilations), thirteen direct
failures, sixty-four dependent modules blocked by them, and six pending
modules at the time-budget boundary. Independent kernel replay and
owned-declaration audit were not run for this failed root. These counts
describe the exact old source checkpoint, not acceptance of the later
repairs or of the complete P2.5 theorem.

## Fourteen-family finite core and common schedule sources

`docs/source-only/20261125-p2-5-fourteen-family/` now records the finite
owner extraction and the new whole-family consumers. The production
candidates `P2Saving16NegativeFiniteCore` and
`P2Saving16FourteenNegativeFibrePartition` have an actual 362-module
source closure. Thirty-one existing declarations retain their original
public namespaces; identifier quoting, two exact deprecated aliases
and the private helper's changed module ownership are recorded separately.
Five support sources are restored from existing P14/P15 work. Every
preexisting production source is unchanged by this extraction.

The two further source-only modules
`P2Saving16FourteenCornerReciprocalResidual` and
`P2Saving16R17StrictFourteenCorners` express one joint error and one common
R17 parameter choice. Only selected pieces occur under the fourteen-cell
sum. The fourth-layer terms, positive outer sum, complete negative-inner
complement, compiler expense and final distribution error remain single
terms. All full `(s,d)` occurrences, signed gaps and count tails remain.

Independent static review and the checked source-identity script cover
the exact moved declarations, remaining owners, provenance and source
graphs. The production verification driver's own import scanner also
reproduced the 362-module graph. No current Lean, independent replay,
owned-declaration or numerical acceptance is inferred for these new
sources. The larger R17 consumers require the recorded owner postimages
and November 23 selected API before they can be compiled together.

## Continuation compatibility repairs and exact input preparation

Source checkpoint `a5d960eed7a4fff90d7a572d383bb6b497173f18` publishes the
finite-core package. The subsequent P2 task
`b7672994901946b18d53a01d75f7dafd` runs the older pinned `c79b9ab` production
sources; it does not compile the new finite core. Its first 20,954 log bytes
are retained in `continuation-strict-compile-prefix.log`. That prefix is
incomplete and must not be used as a final batch summary.

`CONTINUATION_API_REPAIRS.json` records reuse of five existing P14/P15
proof repairs. Four postimages are exact donor bytes; the fifth additionally
renames the one Set alias reported by this compiler. Historical normal and
kernel logs were checked against their receipts, but they do not grant
current P2 acceptance. `CONTINUATION_LINTER_REPAIRS.json` records fourteen
reported sites in six other modules. No warning gate is disabled. All
mathematical statements and premises remain; the sole header difference is
the unused binder `D` becoming `_D` with unchanged type, order and body.
`CONTINUATION_SOURCE_CLOSURE.json` maps the actual next five roots to
376 project modules. These candidate repairs still require compilation.

The continuation also observed that all fourteen saving16 witness files
are absent from `/workspace/goldbach-research` in P2. The bounded
`prepare-q96-original-inputs.py` command reuses matching existing files and
first searches the same workspace for a matching ZIP. If needed it fetches
the fixed original release, verifies the complete archive and every one
of the fourteen selected members, then installs only missing exact files
without overwriting an existing target. It preserves original JSON bytes.
Its only result is input readiness; it supplies no Lean or numerical
acceptance. Run from the actual P2 project root:

```sh
python3 docs/verification/20261125-p2-5-saving16/prepare-q96-original-inputs.py
```
