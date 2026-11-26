# P2.4 finite A03 and raw-kernel diagnostic checkpoint

Recorded: 2026-11-26 07:33:09 UTC; latest status below updated through 08:00 UTC. This evidence checkpoint does not grant acceptance to an uncompleted gate. Earlier scheduling sections preserve the state at their recorded time.

## Latest continuation status

The newer [kernel memory and audit checkpoint](p24-memory-and-audit-checkpoint-20261126.md) supersedes the queued states below: raw05 and prefix06 both returned explicit kernel memory-limit exceptions, and the original full324 exporter preflight selected no valid receipts. The following bullets preserve the earlier 08:00 UTC status.

- The full raw A diagnostic was successfully submitted after the first queue-full rejection: task `548f0b1357034b6e8c16afe4aef9d1a5`, initially queue position 5. At the latest check it was still queued, with no start time or diagnostic result. Production P2 remains at the exact `909214bb…` source pin.
- The local map-prefix-03 candidate is complete and independently reviewed: SHA256 `1b284797644b124a7864a6fa952ce1d10ce0686aad82d955e5296f5bdddd6800`, 13477 bytes. It executes the same update from `2*g+1` for `8*g` steps. Its total-reader equality is only to the `10*g` prefix; transport to the original `12*g` table is explicitly a single-query equality. Both public theorem blocks, the archived rational, original options and fixed formulas are unchanged. This candidate is not the published production source and its closed finite equality has not run.
- P1 exact-source integration task `job_26289695035640389e3588975739a95e` passed, child 1.271302392 seconds, outer 1.415184021 seconds, peak 515121152 bytes. The frozen original arithmetic fragments and 25 consecutive candidate helpers were copied byte-for-byte; extraction hashes are retained in `P24KernelTablePrefixIntegration-extraction.json`. The six printed private theorem axiom sets are subsets of the original allowed three. This checks the Q80 prefix/query adapters, not the full fixed formula or finite A.
- P1 raw-smoke owned diagnostic `job_0bc5bc6d6bfd4b3f8f9e99bf8929a857` passed, child 1.022791457 seconds, outer 1.127823830 seconds, peak 463208448 bytes. All four serialized/environment declarations agree exactly, all are safe/nonpartial/nonaxiom, full types are untruncated, and transitive axioms stay within the original three. The parser, small theorem and checked auxiliary theorem have no axioms; the elaborator implementation has exactly the permitted three. The original smoke directory is unchanged. This is not a 324-module P2 audit.
- The backup worker rejected the integration submission because its retained-job limit was reached; it issued no task ID. No historical jobs were archived or removed. The same integration source subsequently passed on P1 as recorded above.
- A separate eight-node, two-block proof-generation experiment is queued on P1 as `job_15e61b459f9a4561996ce871ef04192c`, source SHA256 `7c6e6fc560a4b1508b0cca38ab377a83f78e05306bb7e0b1726aa3ad58bfca4a`. Its compilation, independent replay and complete owned rules have not yet passed. See the [isolated experiment plan](../../superpowers/plans/2026-11-26-p24-node-proof-blocks-toy.md).
- Read-only review confirmed that the original exporter/runner permit early audits of independently accepted symbolic modules. The [symbolic audit preflight plan](p24-symbolic-audit-preflight-plan-20261126.md) preserves the full 324 selection and every original gate. Its first submission was rejected for a full P2 queue, so there is no preflight task ID or selection result yet.

New completed diagnostic receipts:

- [Exact Q80 prefix integration summary](p1-kernel-table-prefix-integration-01-summary.json)
- [Exact Q80 prefix integration log](p1-kernel-table-prefix-integration-01.log)
- [Raw tactic complete owned diagnostic summary](p1-kernel-exception-owned-01-summary.json)
- [Raw tactic complete owned diagnostic log](p1-kernel-exception-owned-01.log)

## Current accepted boundary

The original symbolic gate has accepted all **321 symbolic modules**. Strict28 task `9ece666f923b40ea8ef6a0368e4eed82` passed at `94c7fcd9117dc1c5e58f2388b3bc0eb9236e5bba`; the A03 prerequisite check subsequently reused and passed all 321 at the current candidate pin.

The full project scope remains **324 modules**, with the unchanged ordered fingerprint:

```text
c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f
```

Finite A has not passed. B and W have not been started in this continuation, and the complete 324-module owned audit has not been accepted. Numeric `#eval`, isolated helper compilation and diagnostic smoke tests grant none of these credits.

## Exact current source and recovery paths

- Published candidate pin: `909214bbfb5ca9caa74fcc1b6f95b469bf43e125`.
- Candidate module: `ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean`.
- Published map candidate SHA256: `f3b608cd96e21bd7bc425526d3731f86ed2440874a00ff61f14f3cfeb77e0e54`, 7705 bytes.
- Matching local copy: `p24-recovery/candidates/P2OriginalCompactArchivedTotalCandidate-map-02.lean`.
- The recovery directory is not a synchronized repository checkout. Its `p24-recovery/ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean` is still the earlier 2133-byte direct-decide source, SHA256 `4eb7f889b753d3c5b2e263d9d4f3ab0586ef7d8db97787f07ef1f1ee6415983a`; do not confuse that copy with the published map candidate.
- The two public theorem headers, archived rational definition, existing local options, and symbolic transfer theorem are unchanged between the original recovery source and the map candidate. This checkpoint independently compared those exact source fragments. The private map helpers do not alter the original Array, sourceState, nodeUpdate, parameters or public endpoint.

## Completed generic and map diagnostics

P3 generic attempt01 `74568a998ec24adc8ebe7fab727af9b3` failed and its exact attempt was retained. Generic attempt02 `63be1a3f1fe04c5cb7c05a20f16800e5` succeeded, exit 0, in 0.689500666 seconds under the pinned Lean and the recorded flags `-t0 -j1 -M4096 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000`. Its source hash was `9fe39709cf3dd4069a057df4a3add98fb2d8d1e00811b23f30f4a28b1dc5701e`. The displayed theorem axiom set was exactly `propext, Classical.choice, Quot.sound`. These are diagnostic results, not canonical P2 acceptance.

The bounded full map diagnostic `ac4040c4373b4568b949955b365b1772` crossed all 19 private-helper declaration markers and reached the closed equality, then timed out. Its child exited -9 after 121.435804 seconds; its Lean error log was empty. The recorded diagnostic used a 500000-heartbeat setting and a 120-second child limit; this was not the subsequent original A gate. Its source, registry and canonical object were unchanged, and the native binding compared equal before and after.

Published evidence at the exact candidate pin:

- [Generic attempt01 summary](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/docs/source-only/20261125-p24-original-compact/p3-kernel-table-generic-01-summary.json)
- [Generic attempt02 log](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/docs/source-only/20261125-p24-original-compact/p3-kernel-table-generic-02.log)
- [Map diagnostic04 summary](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/docs/source-only/20261125-p24-original-compact/p2-finite-a-map-diagnostic-04-summary.json)

## A03: completed original gate, finite target failed

Task: `abd469bb2a8646ebbcf3e0fda4b03ff6`, source pin `909214bbfb5ca9caa74fcc1b6f95b469bf43e125`.

| Stage | Result | Elapsed |
|---|---|---:|
| Original 321-symbolic prerequisite | 321/321, reused 321, complete, exit 0 | 81.099 seconds |
| Original A closure | 101/102, reused 101, A failed, no pending modules, exit 1 | 143.511 seconds |
| Outer task | failed, exit 1 | 229.490866324 seconds |

The outer status records peak memory `12047663104` bytes. The final error says the `decide` instance did not reduce to `isTrue` or `isFalse`. It does **not** print the original kernel exception. Peak RSS does not establish OOM; the underlying exception remains unknown.

The complete 7087-byte log has SHA256 `3d7cb74302c23b637cb8e0976737171b1baa6c31b729d2f35bde2e564efcaa87`, with no truncation or discarded bytes. Both checker summaries and all false finite/whole/audit credit flags are retained:

- [A03 full log](p2-finite-a-03.log)
- [A03 task status](p2-finite-a-03-status.json)
- [A03 dual gate summary](p2-finite-a-03-summary.json)

A02's completed failure remains separate evidence in `p2-finite-a-02.*`; it is not replaced by A03.

## Raw exception diagnostic: smoke passed; full A probe has not run

### P1 smoke: actual successful diagnostic

Task `job_b80d6b1194644863a136fe9e1b4e2989` succeeded. The Lean child exited 0 in 1.376881636 seconds; the outer task took 1.540512800 seconds.

The actual tested source imported `Lean.Elab.Tactic.Decide`, defined the raw tactic, and proved the small Nat equality `(17 : Nat) * 23 + 6 = 397`. `#print axioms` reported no axioms for that theorem. Tested source SHA256: `df56fea377ce6dbb6e164a4bd1edfa0d6df2e82b53902f99ae90ff046fe8b529`.

The compiler was the locked Lean 4.33.0-rc1 commit `62eed1db4d67327ec8120be05f1a1b0847d74561`, with the same binary SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. The smoke touched neither canonical P2 nor the existing P1 project.

The smoke confirms tactic API elaboration and a successful kernel check. It did not exercise the exception handler, solve finite A, or audit all generated tactic declarations.

- [P1 smoke full log](p1-kernel-exception-smoke-01.log)
- [P1 smoke status](p1-kernel-exception-smoke-01-status.json)
- [P1 smoke summary](p1-kernel-exception-smoke-01-summary.json)

### P3 smoke: cancelled before execution

P3 task `86227a50cd5f454c88b49bded6eb9faf` was cancelled by the root agent while queued, with `started_at = null` and zero execution, because P3 was occupied by other work. This is a scheduling fact reported in the handoff, not a failed compilation. Do not rerun or claim a P3 smoke result from it.

### P2 full raw probe: prepared, submission rejected, no task ID

The local script is `p24-recovery/diagnostics/p2-finite-a-kernel-raw-05.sh`, 8891 bytes, SHA256 `2caefa91251661f46fbe323e92d839edd22d4e902925a8d145ae5601e8215837`. A local `bash -n` check passed; the script has not executed.

P2 submission was rejected because the queue was full. **No task ID was issued.** At the root's reported queue snapshot, reconfirmed at 07:35 UTC, another task `de733cb34db040809cba4096a5cfc0b7` was active under `/workspace/p2-saving16-20261125`, with eight other queued tasks. Do not cancel, alter or reuse their workspaces. This snapshot is not a claim that the queue remains unchanged.

The prepared script checks the exact published pin and source hash, takes the existing project lock, uses a separate diagnostic output directory, and verifies canonical source/object/registry and native binding stability. It first repeats the small smoke, then runs the instrumented raw proof with a 300-second child timeout and the recorded flags `-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000 -DElab.async=false`. All diagnostic credits remain false.

The raw tactic retains `mkDecideProof → mkAuxLemma`, restores saved state on failure, and rethrows the original exception instead of substituting the ordinary decide fallback message. An external process kill may still produce no catchable Lean exception. Until an actual raw run returns one, do not label A02 or A03 as OOM, excessive recursion, or any other specific kernel failure.

## P1 generic prefix and point-query stability: completed diagnostic

Task `job_c6a7045554924e07a06196a9ba025dda` succeeded with child exit 0 in 0.906056742 seconds; the outer task took 1.046144485 seconds and recorded peak memory `495316992` bytes. The original pinned compiler and the same recorded generic-proof flags were used.

Local source: `p24-recovery/diagnostics/P24KernelTablePrefix.lean`, 7501 bytes, SHA256 `0c005158cc6676dc14b9b5552cb72fb57c1c1a8cd7c2754a3b31d54f12d51af7`. The successful diagnostic covers the generic arbitrary-update source recurrence, constant-prefix transport and completed-index stability. The five printed theorem names were:

- `mapBuildFrom_empty_lookup`
- `sourceState_completed_index_stable`
- `sourceState_constant_prefix`
- `mapBuildFrom_constant_prefix_lookup`
- `mapBuildFrom_constant_prefix_query_stable`

Every printed axiom set was a subset of `propext, Classical.choice, Quot.sound`. No original numerical specialization or finite A equality was tested. Canonical P2 and the existing P1 project were unchanged, and all compile/kernel/acceptance/finite credit flags remain false.

- [P1 prefix full log](p1-kernel-table-prefix-01.log)
- [P1 prefix status](p1-kernel-table-prefix-01-status.json)
- [P1 prefix summary](p1-kernel-table-prefix-01-summary.json)

At the root's 07:35 UTC handoff, the boundary agent was preparing a local `map-prefix-03` candidate. It had not been published to production or compiled. That candidate is separate from the full-update map source at pin `909214bb…`; this generic diagnostic must not be presented as a successful run of the future candidate.

## Owned audit: unchanged rules and generated tactic declarations

The exact unchanged audit files are:

- `verification/part2/run_winner9_private_audit.py`
- `verification/part2/winner9_private_audit_template.lean`

Template SHA256 remains `2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`. The template contents were checked equal at pins `94c7fcd9…` and `909214bb…`.

The template inventories every declaration owned by the target module, including private and generated declarations, and requires exact agreement between the serialized and environment inventories. For each declaration it rejects `info.isUnsafe || info.isPartial || info.isAxiom`; it then runs `collectAxioms` and permits only `propext`, `Classical.choice`, and `Quot.sound`. Complete untruncated types are also required. No generator or syntax declaration is excluded.

Locked Lean's `elab` command expands through `syntax` and `elab_rules`; the generated parser and `aux_def` elaborator are `meta def` declarations. In this Lean version, `meta` is a computation-stage modifier, separate from `isUnsafe` and the partial-recursion modifier. Ordinary nonrecursive `meta def` is therefore not automatically unsafe or partial. This removes one possible classification mistake; it does not establish a full audit pass.

The raw smoke only printed the axiom dependencies of the small resulting theorem. It did not print or audit the generated parser/elaborator inventory. A future proof-producing tactic must still satisfy the unchanged owned and transitive-axiom checks for every owned declaration. Changing from `elab` syntax to a private helper and an existing tactic entry point does not waive these checks.

Pinned source evidence:

- [Original audit template](https://github.com/UyNewNas/goldbach-formalization/blob/909214bbfb5ca9caa74fcc1b6f95b469bf43e125/verification/part2/winner9_private_audit_template.lean)
- [Elab command expansion](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/ElabRules.lean)
- [AuxDef emits meta def](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/AuxDef.lean#L25-L42)
- [Syntax emits meta parser definitions](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/Syntax.lean)
- [ComputeKind, recKind and isUnsafe are distinct](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/DeclModifiers.lean#L119-L137)
- [Kernel safety is separate from markMeta](https://github.com/leanprover/lean4/blob/62eed1db4d67327ec8120be05f1a1b0847d74561/src/Lean/Elab/PreDefinition/Basic.lean#L186-L220)

The template path, exact checks and classification result were shared directly with `/root/p24_kernel_table_design_review`. That agent is examining the deeper proof-producing cbv API dependency boundary. No audit rule or template was changed here.

## Remaining original gates and next evidence

1. Obtain the complete result of queued raw task `548f0b1357034b6e8c16afe4aef9d1a5`. The first queue-full rejection and the successful Nat smoke remain distinct from an actual full A diagnostic.
2. Use actual diagnostics to choose and review any minimal proof repair. Keep the original public mathematics, all numerical parameters, source definitions, scope fingerprint, native binding and original gate limits.
3. Re-run the original prerequisites at the exact published source, then require **A: 102/102**, exit 0, empty failed/pending and completed normal native postcheck.
4. Only after A is accepted, run **B** with its 322-module prerequisite and 103-module target closure. Preserve the exact original two-million-split run and endpoint check.
5. Only after A and B are accepted, run **W** with its 323-module prerequisite and require the unchanged full **324-module** closure.
6. Complete the existing owned-audit/export sequence for all 324 modules. The 321 independently compiled symbolic modules may be audited while finite A remains open, following the linked preflight plan. First apply the existing historical receipt selection rules, then audit only entries lacking valid evidence. Preserve the current template and require final complete coverage, no unselected modules and no duplicate owned declarations.

No new compilation, cloud submission, source publication, production edit or audit modification was performed while writing this checkpoint.
