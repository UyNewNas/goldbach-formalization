# P2.4 finite checks and complete owned-declaration audit

## Status and fixed scope

Last completed selected canonical source: `284ceef1ba7dd0fcd813b159bdf7f9629f236ec9`.
Its strict-symbolic-27 task `f85fa738fbeb46d08d6450e11b7eb1ad` finished
with exit0: **320 of320 selected symbolic modules accepted**,319 reused,
complete=true and empty failed/pending lists. CachedRun is the sole excluded
symbolic module; the full321-module joint gate remains required. Both finite
candidates, the whole endpoint and the complete independent owned audit have
not been accepted. Keep the accepted320 records and original input bindings.

The prior repair reused an existing own-cube dictionary that was not imported
by the failed PolicySaving source. This added exactly two existing project
modules, both now accepted by strict05. The current closure is **321 symbolic modules
+ two finite candidates + the whole endpoint = 324 modules**.
`p2-strict04-policy-import-scope.json` records the exact delta; external
and native direct imports are unchanged. Keep the existing qualified
snapshot and scoped baseline mirror.

The source pin in the command template below is deliberately a placeholder.
Replace it only with the exact published source at which the original checker
has accepted all 321 symbolic modules. The finite commands have not run.
Do not repeat cleanup, cloning, migration, or native qualification. Existing
valid records must be reused by the unchanged checker.

The ordered module list returned by the existing `project_nodes` for
`ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint`, encoded as one
name per line with a final newline, has SHA-256:
`c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f`.

## Finite checks

Use three separate jobs, A then B then W, each with **job memory 13107 MB,
hard job timeout 3600 seconds, one worker and one Lean thread**. Every job
starts with the following common prelude. Keep the existing migration lock
for the entire job; use the existing scoped baseline mirror and the original
qualified native snapshot. There is no automatic fetch, checkout, reset, or
repeat disk recovery. A different runtime HEAD requires a deliberate new pin
and renewed prerequisite validation.

```bash
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0

P24_PIN=P24_ACCEPTED_SYMBOLIC_COMMIT
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
P24_ACTUAL_HEAD="$(git rev-parse HEAD)"
printf 'P24_SOURCE_HEAD=%s\n' "$P24_ACTUAL_HEAD"
test "$P24_ACTUAL_HEAD" = "$P24_PIN"
test -z "$(git status --porcelain --untracked-files=no)"

P24_SNAPSHOT=/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json
P24_BASELINE=/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001
P24_CHECK=(
  python3 -B verification/part2/run_winner9_private_checks.py
  --baseline-root "$P24_BASELINE"
  --external-snapshot "$P24_SNAPSHOT"
  --memory-mb 11264 --workers 1 --threads 1
)
P24_SYMBOLIC=(
  ImbalancedChen.P2OriginalCompactQ80CompleteSoundness
  ImbalancedChen.P2OriginalCompactCachedRun
  ImbalancedChen.P2OriginalCompactQ80FixedBindings
  ImbalancedChen.P4AOrdinaryRootFirstIntegral
  ImbalancedChen.Part4ActualThirdFiniteDensityReserve
)
P24_A=ImbalancedChen.P2OriginalCompactArchivedTotalCandidate
P24_B=ImbalancedChen.P2OriginalCompactCachedEndpointCandidate
P24_W=ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint
```

| Job | Zero-budget prerequisite closure | Subsequent root | Successful root closure |
|---|---:|---|---:|
| A | Symbolic: 321 | Archived total candidate | 102 |
| B | Symbolic + A: 322 | Cached endpoint candidate | 103 |
| W | Symbolic + A + B: 323 | Whole functional endpoint | 324 |

Append only the corresponding pair of commands to each job's prelude:

```bash
# Job A: archived rational total; no adaptive run is evaluated by this root.
"${P24_CHECK[@]}" --time-budget-seconds 0 "${P24_SYMBOLIC[@]}"
"${P24_CHECK[@]}" --time-budget-seconds 3000 "$P24_A"
```

```bash
# Job B: the cached two-million-split finite check.
"${P24_CHECK[@]}" --time-budget-seconds 0 "${P24_SYMBOLIC[@]}" "$P24_A"
"${P24_CHECK[@]}" --time-budget-seconds 3000 "$P24_B"
```

```bash
# Job W: consume both finite results in the whole endpoint.
"${P24_CHECK[@]}" --time-budget-seconds 0 "${P24_SYMBOLIC[@]}" "$P24_A" "$P24_B"
"${P24_CHECK[@]}" --time-budget-seconds 3000 "$P24_W"
```

The zero-budget gate is the original strict checker, not a source-only
precheck. It starts no new Lean source compilation, but still validates
recursive records, actual source/object bytes, dependency signatures, and
native inputs. It may save records through its existing rules; zero new
compilation does not mean zero filesystem writes. Its exit codes are 0 for
complete, 1 for failed/blocked, and 2 for pending. `set -e` prevents the second
command from starting unless the prerequisite exits 0.

The **3000-second budget is a soft scheduling limit**, not a timeout for an
already running Lean process. The prerequisite also consumes wall time, so
this budget cannot guarantee a fixed postcheck allowance before the job's
3600-second hard limit. A `PASS` line or an emitted object before a hard
timeout does not establish acceptance. Each job needs exit 0, final
`complete = true`, empty `failed_or_blocked` and `pending`, the closure count
above, and successful native postchecks with `PASSED_BATCH_PRE_POST` and
identical before/after bindings. Separating A and B lets A complete its
postcheck and registry publication before B begins. These are compilation
gates; independent replay and declaration audit remain separate.

## Independent audit

Start this phase only after the original checker has accepted the complete
324-module closure. Reuse the fixed source, lock, and snapshot from the
prelude above. Run one active audit worker per job; do not overlap it with
source changes, compilation, cache migration, or another audit of the same
module.

The existing `run_winner9_private_audit.py` accepts explicit `modules ...`,
`--summary-name NAME.json`, `--external-snapshot PATH`, and
`--memory-mb {6144,11264}`. It has no worker, thread, time-budget, or timeout
option. It checks each requested target's complete compilation closure, but
audits only that target's owned inventory. Passing only the whole endpoint
does not audit the other 323 owned inventories.

`p24-owned-audit-template-import-preflight.md` records a concrete missing-core-
import risk for the pure-Std `OriginalNodeArraysV1.DataCore` target. No template
has been changed. First export and preserve accepted historical receipts as
described below, then handle any actually missing DataCore audit explicitly.
Do not invalidate or rerun accepted work merely because of this preflight.

For each target it runs, in order:

```text
leanchecker --verbose MODULE
lean -t0 -j1 -M11264 -DwarningAsError=true \
  -DmaxRecDepth=50000 -DmaxHeartbeats=40000000 ATTEMPT/Audit.lean
```

`--memory-mb 11264` selects the second command's Lean limit. The independent
`leanchecker` command has no added memory flag and remains bounded by the
outer job. Retain job memory 13107 MB and hard timeout 3600 seconds.

The current audit driver SHA-256 is
`571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5`;
the unchanged template SHA-256 is
`2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`.
The template requires exact serialized/environment owned-inventory agreement,
including private/generated declarations, complete types without truncation,
and no unsafe, partial, or axiom declaration. Allowed transitive axioms are
only `propext`, `Classical.choice`, and `Quot.sound`. Loaded project imports
must equal the source closure. Compilation and both audit stages retain the
original source/object/dependency/runtime and native pre/post gates.

### Preserve accepted historical work

The audit runner directly reuses only a module's `latest.json` when it is
accepted, its complete current input snapshot matches (including driver,
template, physical project-object paths, and native binding), and every bound
artifact still matches. It can separately reuse a successful stable replay
while retrying the declaration audit. Changing only the requested memory
limit does not invalidate an already accepted audit.

Before scheduling new work, use the existing
`export_winner9_private_evidence.py` on all 324 explicit targets. Its existing
`validate_receipt` scans historical attempts and validates registered old
driver receipts against current inputs and their original artifacts. Retain
those accepted audits and send only `unselected_modules` to the runner.
The 69 transported compilation records do not themselves supply audit credit;
a changed native external binding still prevents historical audit reuse.

Populate `P24_ALL_MODULES` with the exact list, checking both count and order:

```bash
mapfile -t P24_ALL_MODULES < <(
  python3 -B - <<'PY'
import hashlib
import sys
from pathlib import Path
sys.path.insert(0, str(Path("verification/part2").resolve()))
from run_winner9_private_audit import project_nodes
names = list(project_nodes(Path.cwd(),
    "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"))
assert len(names) == 324
assert hashlib.sha256(("\n".join(names) + "\n").encode()).hexdigest() == \
    "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
print("\n".join(names))
PY
)
test "${#P24_ALL_MODULES[@]}" -eq 324

python3 -B verification/part2/export_winner9_private_evidence.py \
  "${P24_ALL_MODULES[@]}" \
  --output-dir .lake/p24-audit-export/preflight-001 --split all
```

Use a fresh export directory for every export. The exporter does not invoke
Lean or replay, but does write evidence packages. An exit code of 0 alone
does not mean every requested module was accepted.

### Batches, continuation, and final coverage

From the preflight manifest's unselected modules, start with a small symbolic
batch (for example ten), then size later batches using actual replay/audit
times. Schedule each finite candidate and the whole endpoint separately if
still unselected. `P24_BATCH_MODULES` below is the explicit selected array;
use a distinct summary name for each batch or retry:

```bash
python3 -B verification/part2/run_winner9_private_audit.py \
  "${P24_BATCH_MODULES[@]}" --external-snapshot "$P24_SNAPSHOT" \
  --memory-mb 11264 --summary-name p24-owned-symbolic-000-r01.json
```

Each completed module immediately saves its receipt. A hard job interruption
does not erase earlier completed receipts, but gives the current unfinished
stage no credit. Rerun the same explicit batch to use the original reuse
rules; retain all attempt directories and logs. Regenerate preflight after
any source, object, or runtime change. A batch summary covers only its
requested modules, not the full 324-module scope.

After the missing audits finish, run the original exporter again on the
complete list:

```bash
python3 -B verification/part2/export_winner9_private_evidence.py \
  "${P24_ALL_MODULES[@]}" \
  --output-dir .lake/p24-audit-export/final-001 --split all
```

Final coverage requires the `accepted_modules` name set to equal the exact
324-module set, `accepted_module_count = 324`, `unselected_modules = []`,
and no duplicate owned declarations. The selected receipts supply every
module's full inventory, types, and axiom evidence. Rejected older attempts
do not invalidate another accepted, verified receipt for the same module.
Keep the exporter's generic Winner9 coverage fields and `full_p2_complete:
false` unchanged; they neither establish nor replace this task's exact
scope check. Only the completed original gates supply acceptance.
