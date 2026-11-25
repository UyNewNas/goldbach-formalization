# G3 single-owner partition execution

> Implementation is confined to this README and `run_partition.py`. Root owns
> source publication and every compiler job. Existing helpers, proof sources,
> fixtures, configuration and historical receipts remain unchanged.

**Goal:** install the reviewed 25-source partition safely, then perform one
explicit owner's normal or audit phase with immutable fixture provenance.

**Architecture:** load the unchanged source-parameterized Batch13 normal/audit
API from commit `4cea0407c1258eaddd7d4952cffa4aea67310422`, SHA256
`95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea`.
Reuse the original Batch10 overlay graph, source installer, frozen-file and
snapshot utilities, plus the original Batch5/6 serializer/guard/operations.
Adapt the existing G3 pilot's before/after fixture companion design to a
single explicit owner and source commit; do not patch historical constants.

**Spec:** root's bounded single-owner task and
`../g3-partition-review/SOURCE_PARTITION.json`, SHA256
`67ca0a0157134c1c93cc1130d7ed80e56e85edadb4373ee18981c6f68048693d`.

## Fixed interface and state layout

```text
run_partition.py --source-commit FULL_SHA --module FULL_MODULE
                 (--check | --normal | --audit)
                 [--config-basis runtime|source]
                 [--source-repo PATH --project PATH]  # --check only
```

The owner must be one of the manifest's 24 providers or the existing Data
facade. Runtime is the default. Source basis is allowed only for a local,
non-cloud `--check`; it never reads fixtures or live runtime files and must
report `SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`.

Each owner has its own immutable root:

```text
/workspace/p1-complete-proof/20261125-g3-partition-v1/<source_commit>/<module>/
```

The unchanged normal API writes `normal/<module>/NORMAL_PASS.json` there.
Its sibling `FIXTURE_BOUND_NORMAL.json` is required for any later reuse.
Each owner's e9 plans/audits stay in that same root, and a durable
`FIXTURE_BOUND_AUDIT.json` binds the complete result to fixture checkpoints.
Per-owner audit roots avoid mixing another owner's receipt into a one-owner
`passed` map.

## Implementation steps and review gates

- [x] Load exact published manifest, 25 payloads, original Data preimage,
  Reader receipt, fixture inventory, source/runtime configuration evidence
  and unchanged helper APIs. Construct the 92-module source graph using the
  published payload overlay; all noncandidate sources must match the chosen
  commit. Verify Reader's 67-source accepted closure and protected sources.
- [x] Preflight the complete 25-file batch without writes. All occupied
  target paths must be regular, non-symlink files. New providers permit only
  absence or exact postimage; Data permits original preimage or postimage.
  Only then delegate installation to unchanged `d.install_sources`.
- [x] Under the original lane-0 serializer, verify all 188 existing fixture
  size/hash records, the exact accepted Reader source/five outputs, runtime
  and configuration. Hold any old monolith NORMAL_PASS/fixture companion.
  Before the first facade replacement, verify its recorded failed facet
  metadata. Preserve the existing setup file and all object bytes during
  source installation; record fingerprints without copying large payloads.
- [x] Normal phase: reject orphan generic normal/companion files. A fresh
  normal must be enclosed by immutable fixture/Reader checkpoints and its
  actual command timestamps; only then save the new companion. Existing
  valid companion+normal pairs use the original no-build/reuse path. A ready
  object without provenance remains held.
- [x] Audit phase: require an already valid normal companion, then use the
  original one-owner e9 API. Save a separate immutable fixture-bound audit
  record. Complete bound audits are validated and reused. Partial audits or
  unaccompanied generic audit results remain held, with no reconstruction of
  missing before/after evidence.
- [x] Facade gate: independently validate all 24 providers' fixture-bound
  normal **and full-owned audit** evidence before facade work. The unchanged
  normal API must also pass direct dependency `--no-build` checks. Audit the
  facade only as its own owner; it never substitutes for provider acceptance.
- [x] Verify syntax, source-only CLI behavior against the published source
  commit, and focused local rejection/reuse cases; request independent review.
  No Lean/Lake, cloud task, fixture payload read or Git publication is part of
  local implementation verification.

## Rulings and limits

The original Batch10 preflight permits a symlink whose contents match a
postimage. The new thin layer adds whole-batch regular-file/symlink checks
before calling it, including dangling symlinks, without changing that helper.

Root confirmed the strict facade prerequisite: every provider needs both its
fixture-bound normal and complete fixture-bound audit. Generic e9 completion
without its fixture audit companion holds for inspection; it is never
retrospectively blessed or repeated automatically.

The first intended tasks are `...DataC0000ToC0046`, then `...DataF0020`, each
normal and audit separately. There is no 24-owner batch loop. Large original
blocks, facade import, kernel replay and downstream Archive proofs may still
hit limits. This caller never claims the 94 Checked proofs, G3's integral
conclusion or complete P1 acceptance.

## Exact published inputs

The first checked source commit is
`e421f8cd5aad3d9c53933dec3c77bb530bb52f8c`. The caller's own publication may
be a later commit; the explicit source commit binds all 25 proof payloads and
their full dependency graph independently of the caller's frozen hash.

| Input | SHA256 |
| --- | --- |
| `SOURCE_PARTITION.json` | `67ca0a0157134c1c93cc1130d7ed80e56e85edadb4373ee18981c6f68048693d` |
| Original fixture inventory | `c89fd6388cfb269ebe74bad97e62454a8ad36fc317d7e5685253f4c13785047e` |
| Accepted Reader receipt | `18a4660cae2ce1f0fa2d233f84be244f46b7a9522bd46f7289c89e50d72adcd1` |
| Actual runtime configuration snapshot | `df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614` |
| Historical configuration review | `34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880` |
| Exact failed monolith source/artifact snapshot | `d6063b581259ce08e394493e44e52ed821239b4cd5f3efaf331638f62dc319a9` |

The entire overlay contains 92 source modules. Each provider has a 68-module
source closure: itself and the unchanged 67-module Reader closure. Reader's
source SHA256 remains
`59d3c878507d07dff88790ed2c9fc626768fd7155dc3250c01763273e2f0d5b6`.
Its already accepted source and five output fingerprints must match exactly.
No Reader build, kernel replay or re-audit is scheduled.

Git source configuration and actual runtime configuration remain separate.
Runtime mode pins the existing 1823-byte `lakefile.toml`, SHA256
`e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48`,
plus the other two config files and five accepted runtime artifacts. Source
mode checks the 394-byte Git `lakefile.toml` instead. Neither mode changes
configuration, heartbeat, thread or memory limits. Runtime checks use the
same existing environment confirmed by all 75 earlier accepted normals and
the three new Batch13 normal receipts in the pinned configuration review.

## Source installation and checkpoint semantics

Every normal task first preflights the complete batch and verifies all 188
existing fixture files before installation. The first task installs all
25 sources; later tasks find exact postimages and use no-op installation.
Only the requested owner may compile. Direct dependency readiness comes from
the unchanged generic API's `lake --no-build build` gate, preventing a cold
Reader or facade dependency fan-out.

The old monolith's durable NORMAL_PASS and fixture companion paths must both
remain absent. Before replacing its original source, the exact failed-state
snapshot must match: four outputs absent and the 6,334,162-byte setup file
present with SHA256
`02b7248c74edcbf9a293e9ebc65b9a7f16a90b3ebf8bc0e25a6213d81a7c2d83`.
The installer preserves all five existing artifact states, checked before
and after installation; it records only metadata, never a copy of the large
setup payload. An eventual authorized facade normal may generate its own
new outputs in the usual way.

A provider normal companion binds its exact fixture subset and Reader reuse
context. The facade's companion binds all 188 fixtures and references every
provider's validated normal and full-owned audit companions. Each checkpoint
records both the start and finish of its verification. Actual normal command
start must follow the before-check finish, and actual command finish must
precede the after-check start. Audit companions apply the same enclosure to
all actual readiness, kernel and owned-audit commands. These records cannot
be created after an unaccompanied generic success on a later invocation.

Completed paired evidence is revalidated against current sources, fixtures,
Reader, objects/traces, configuration, runtime, raw logs and output hashes.
Normal reuse may perform the original no-build checks; complete audit reuse
validates the original result without another kernel/audit command. Every
audit plan must have exactly one corresponding audit directory, and its
original frozen plan must match the prepared copy. Unknown or partial state
holds for inspection. Existing logs and durable receipts are not overwritten.

## Commands

Local read-only source check, without fixtures or cloud runtime files:

```bash
python3 -B docs/p1/20261125/g3-partition-execution/run_partition.py \
  --source-commit e421f8cd5aad3d9c53933dec3c77bb530bb52f8c \
  --module ImbalancedChen.P4AOriginalNewFifthArchiveDataC0000ToC0046 \
  --check --config-basis source \
  --source-repo /workspace/scratch/cba105ac8c38/goldbach-p1 \
  --project /workspace/scratch/cba105ac8c38/goldbach-p1
```

Root schedules the actual cloud phases separately, using the reviewed caller:

```bash
python3 -B docs/p1/20261125/g3-partition-execution/run_partition.py \
  --source-commit e421f8cd5aad3d9c53933dec3c77bb530bb52f8c \
  --module ImbalancedChen.P4AOriginalNewFifthArchiveDataC0000ToC0046 \
  --normal --config-basis runtime

python3 -B docs/p1/20261125/g3-partition-execution/run_partition.py \
  --source-commit e421f8cd5aad3d9c53933dec3c77bb530bb52f8c \
  --module ImbalancedChen.P4AOriginalNewFifthArchiveDataC0000ToC0046 \
  --audit --config-basis runtime
```

The next distinct pilot substitutes
`ImbalancedChen.P4AOriginalNewFifthArchiveDataF0020` as the one owner. Later
providers are individually scheduled by root. The facade owner is
`ImbalancedChen.P4AOriginalNewFifthArchiveData` and remains blocked until all
24 provider prerequisites are independently accepted. Keep the same source
commit and caller bytes when resuming an owner root.

`--check` performs no Lean/Lake invocation and writes no project or receipt
files. Runtime `--check` verifies live fixtures, Reader and runtime; checking
the facade also verifies its provider evidence. It still makes no compiled
readiness or acceptance claim. Execution paths are restricted to the existing
cloud source repository and project. Source-basis execution is rejected before
Git/project/runtime access.

## Local verification and review

- Python syntax compilation passed, using temporary bytecode outside the repo.
- Eight focused temporary checks passed: matching symlink, dangling symlink
  and unknown provider rejection before writes; exact postimage no-ops;
  orphan normal/companion rejection; actual-command checkpoint enclosure;
  orphan/partial audit state rejection; source-basis execution rejection.
- The orphan audit-plan case was observed failing, then passed after adding
  the plan/directory bijection and frozen-plan copy comparison. No old helper
  was changed to fix it.
- The actual source-only CLI against published `e421f8cd...` passed with all
  25 local postimages, 92 union sources and 68 selected-owner sources.
- A second actual CLI used a temporary project containing only the original
  Data facade, noncandidate sources and source configuration. It passed with
  exactly 24 `CREATE_ABSENT` and one `REPLACE_PREIMAGE` action. All 77 project
  files remained byte-identical, all 24 new paths remained absent, and no
  fixture directory existed. This verifies the published-payload overlay and
  source-only behavior before installation.
- Root reviewed the complete initial caller; independent peer review was
  requested. Actual compiler execution and publication remain root's task.

These checks provide local orchestration evidence only. The implementation
author performed no Lean/Lake, cloud task, fixture payload read, source install
into the cloud project, or Git commit/publication.
