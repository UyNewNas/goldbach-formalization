# Part 1 verified milestone: lower fourth and finite historical caps

## Result and fixed identity

**PASS for the six targets below:** actual strict Lean compilation,
defining-module axiom audit, and six original `leanchecker` replays.
The verified mathematical scope is the ordinary-parent lower-fourth
restoration integral and the finite common-mesh upper-third/fourth/fifth
cap interface. The complete adopted policy and inherited-fifth integral
remain open; their exact obligations are in [HANDOFF.md](HANDOFF.md).

| Reference | Fixed value |
| --- | --- |
| Common proof baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Earlier source-only checkpoint / delivery parent | `70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` |
| Delivery branch | `chatgpt/chen-p1-history` |
| Frozen manuscript | `ba6ec11d800eccc54406490631895e174de85766` |
| Official Lean version | `leanprover/lean4:v4.33.0-rc1` |
| Official Lean githash | `62eed1db4d67327ec8120be05f1a1b0847d74561` |
| Final receipt time | `2026-10-12T07:46:05.597741+00:00` |
| Final receipt SHA256 | `2a23599ce539e7768a938e729b9beb7516210ff49221f6a8fd8a0938107765a1` |

The delivery commit is created after verification and contains this record.
Its mathematical inputs are bound by the six complete source and object
hashes in [VERIFICATION.json](VERIFICATION.json), rather than by pretending
that the old source-only checkpoint already contained the updated checker.
The original baseline's 303 files remain byte-identical. No shared root
import, dependency pin, toolchain configuration, workflow or final theorem
entrypoint was changed.

## Actual target gates

| Target module | Strict compilation | Original replay | Audited defining-module declarations |
| --- | --- | --- | ---: |
| `ImbalancedChen.OrdinaryLowerFourFrontier` | Exit 0 | Exit 0 | 27 |
| `ImbalancedChen.ActualSelectedPrefixLowerCellSum` | Exit 0 | Exit 0 | 9 |
| `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral` | Exit 0 | Exit 0 | 8 |
| `ImbalancedChen.HistoricalPrefixCertificate` | Exit 0 | Exit 0 | 96 |
| `verification.parts.p1.LevelCheckProbe` | Exit 0 | Exit 0 | 10 |
| `verification.parts.p1.Part1HistoryAudit` | Exit 0 | Exit 0 | Audit execution module |

The audit inventories all **150 declarations** defined by the four
production modules and the computation probe, including private and
generated declarations, structure fields, and three auxiliary kernel
proofs. It uses Lean environment defining-module metadata and the bundled
transitive `Lean.collectAxioms`, rejects owned unsafe or axiom declarations,
and accepts only `propext`, `Classical.choice`, and `Quot.sound`. Those
three are exactly the observed axiom union. There is no admitted proof,
custom axiom or native decision procedure in the accepted targets.

[KEY_THEOREM_TYPES.md](KEY_THEOREM_TYPES.md) contains fourteen complete
source declaration headers matched to this actual audit, together with
their original Lean pretty-printed types. The pretty-printer may hide
implicit and proof-irrelevant arguments; the complete source headers keep
every declared parameter and hypothesis. The archive retains all 150
original declaration/type/axiom records, not just this selected list.

## Actual execution path

The stock `lean --version` executable in this environment failed before
proof parsing with `error: failed to locate application`. The original
failure record is retained. Compilation instead used the unmodified
official Lake executable to call the official `Lean.Elab.runFrontend` API
with `trustLevel = 0`, normal initializer execution, and explicit source,
module name and output object paths. All six P1 targets used
`warningAsError = true`; unchanged supplier modules used their original
warning policy. This is actual Lean compilation, and is not recorded as
an executed standard `lake build` command.

The final dependency graph has **9,368 source modules**: 8,679 fixed
official cached modules and 689 locally compiled modules (174 project,
506 goldbach, 9 LeanArchitect). The final graph completed 689/689. The
receipt rechecks every local source, main object and direct import hash,
all six target object sidecars, all eleven dependency HEADs and tracked
sources, original toolchain binary hashes, and unchanged project pin
files. Official cached imports are distinguished from local compilation.

An early metadata adapter was used only for the pinned Cache bootstrap
and setup. It was absent from project/supplier compilation and all six
target replays. Its exact source and original cache logs remain in the
archive. The driver, scheduling transition, and normal initializer call
are scratch orchestration records; they do not modify the proof kernel
or add mathematical declarations to the project.

The six original checker commands each had the form

```text
<official-toolchain>/bin/leanchecker --verbose <full-target-module>
```

They ran sequentially with `LEAN_NUM_THREADS=1`, each exited zero, and
each raw log contains exactly its corresponding `replaying <module>`
line. The aggregate replay process also exited zero (277.015 seconds).
The source and all target object hashes were unchanged across replay.
The original checker's default mode replays declarations defined by each
selected module, including private data; it does not freshly replay every
declaration of every imported dependency. The matching original
`LeanChecker.lean` is included as the semantic reference.

## Preserved failures and source repairs

The first graph was frozen before the repository computation probe was
added. It completed 687/688 and the Audit failed because the Probe object
did not exist. That actual diagnostic, graph and original result are
retained in `closure-attempt-01`. A subsequent graph included all six
targets and the final 689 local modules.

The historical checker was changed from an implicitly selected global
decider to three explicit `Finset.decidableDforallFinset` deciders, so its
outer checks traverse the selected cell sets. Its public definition and
theorem types stayed unchanged. The archive preserves the old source and
compilation record with its object hash; the old object itself remains
only in the local historical directory. The new source was strictly
recompiled and replayed.

The first Probe then failed to reduce its three ordinary `decide` goals.
The pinned `Rat.mul` and `Rat.inv` are irreducible to default elaborator
reduction. Changing only the three proof tactics to `decide +kernel`
lets the same proof terms undergo kernel conversion. The original failure
is retained in `closure-attempt-02`; its error-recovery placeholders are
not accepted evidence. The current Probe passed strict compilation and
original replay, including its generated helper declarations. The original
`Decide.lean` and `Rat/Basic.lean` explain this distinction in the archive.

The accepted probe fixes a nonempty one-cell table at each rank, with
base cap `1/2` and new caps `3/5`, `5/8`, `2/3`. It proves acceptance,
then rejection when the fourth cap is `1/2` or the fifth is `3/5`.
These checks exercise actual inherited old values. They are not the
adopted manuscript certificate or a large-table performance claim.

## Evidence archive

Download [EVIDENCE.tar.gz](EVIDENCE.tar.gz), containing 2,196 members and
11,850,281 bytes of uncompressed payload. Archive size is 1,776,240 bytes;
SHA256 is

```text
c56fc707d40ad255fd2d9c8b6c94dc7442c9c62b7238d833188b18cdf10f601d
```

`MANIFEST.json` maps every preserved original path to an archive member,
byte count and SHA256, and records hashes for omitted binaries/objects.
Its SHA256 is
`6cf28ed59750e93205e195dd802c1c8679111aba595794bc5ba19b8bf179b819`.
The archiver read every member back, compared its captured bytes, and
rechecked all watched input hashes before publishing the archive.

Useful members include:

- `runtime/part1-final-receipt.json`: the complete gated real receipt.
- `runtime/logs/closure/`: all 689 current raw compilation logs, graph,
  state and final result; the Audit log contains the complete census/types.
- `runtime/logs/replay/`: six individual original replay logs, their
  aggregate `six-targets.log`, and structured results.
- `runtime/logs/closure-attempt-01/` and `closure-attempt-02/`: the earlier
  attempts and their original source identities and outcomes.
- `repo/`: the six verified Lean source snapshots and unchanged pin and
  workflow files selected by the archiver.
- `scratch/`: the fixed source-checkpoint CI evidence and latest read-only
  Part 0/5 intake snapshots; these are context, not additional P1 gates.

Original absolute paths inside receipts remain intact; the manifest
provides the portable mapping. No object files or toolchain binaries are
embedded. Historical smoke stdout was not separately archived and is
explicitly identified as original session evidence only; no replacement
stdout was manufactured.

## CI and Part 0 integration

The automatically triggered runs at the earlier source checkpoint
`70ad4d737a2ff4a77413a5975af2fb41bdfb7d66` have distinct scopes:

| Run | Actual outcome | Scope |
| --- | --- | --- |
| [Variable envelope 38205489708](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205489708) | Success | Six existing VariableEnvelope modules and two boundary regressions; eight replays and 358 audited declarations |
| [Lean core 38205489711](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38205489711) | Cancelled | Full build cancelled; root checker and root axiom audit skipped |

Neither run verifies the six new P1 targets. The cancellation's root cause
is not established by the saved metadata. CI for any later delivery SHA
must be read at that SHA; these old outcomes are never transferred to it.
No manual workflow run or Codex task was launched.

In a normal environment where the pinned stock Lean CLI starts, the
explicit P1 reproduction command is:

```bash
bash verification/parts/p1/check.sh
```

The script has passed shell syntax checking here; its stock-CLI execution
is not claimed. [INTEGRATION.patch](INTEGRATION.patch) contains the proposed
root imports and remains unapplied. Part 0 owns the fixed integration
commit, complete root build, root checker and canonical full-root audit.
Until those imports are integrated, a root build alone does not include
these auxiliary leaves. The mathematical remaining inputs and receiving
Parts are listed in [HANDOFF.md](HANDOFF.md).
