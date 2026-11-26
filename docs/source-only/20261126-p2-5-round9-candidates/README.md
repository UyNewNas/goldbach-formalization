# P2 round 9: two existing P1 repairs

The final source selection contains only the two direct normal failures in the completed round-8 attempt: `P1OriginalProducerAttainedRowBinding` and `P1OriginalVariableFourthSourceCoefficient`. Both after sources are byte-identical to the earlier `round8-existing-reuse` package. No new Lean proof is written, compiled or installed here.

The completed round-8 normal summary is 349/377, comprising 346 reused modules and three newly passed round-8 repairs. Owned acceptance is 46/69, including the newly accepted 96-declaration Ownership inventory; all seven postflight checks are true and aggregate acceptance remains false. The final source preparer succeeded and pinned this terminal state.

The selected prior result SHA is `acd7946f25d329159df22e51c44d9baf7ff8967d19477519ea6c963ee81ab0bc`. Its bytes were reconstructed from the complete actual task stdout using the published round8 runner's exact `save_json` serialization: sorted keys, indent 2 and one trailing newline. That runner saves and then prints the same terminal state without intervening mutation. This is **not** an independently downloaded original result file or independently received remote file digest. `RESULT_PROVENANCE.json` records that distinction. The unchanged execution preflight must hash the actual remote original `RUN_RESULT.json` and match this SHA before creating new output, checking out source or running Lean; any mismatch stops execution. The separate read-only export remains queued.

## Source provenance

| Module suffix | Existing donor postimage | Evidence already retained |
|---|---|---|
| ProducerAttainedRowBinding | `6270f6ca5f2b6d4d50681c65c4210e61bead0ded08f3e5b72d5c08a8fab08ddb` | Batch79 exact source, normal, kernel and complete owned PASS |
| VariableFourthSourceCoefficient | `20aa46c64b1077eab865a534f388ee1f2fef1f2e0787cd7a6bbe30887dc67bb5` | Batch85 exact source, normal, kernel and complete owned PASS |

The Producer repair replaces an unavailable convenience parity name with the existing rank-four depth-splice/rank-two parity composition. SourceCoefficient makes the existing finiteMax arguments explicit and uses the current indicator lemma name. The prior source inventory already verified unchanged theorem headers, definitions, imports and options. Both candidate preimages have now also been checked against published round8 source commit `796c905eee062f06e2cfb707367e44994b4cf69e` and the graph reconstructed through rounds 4–8. Actual receipt identity must still confirm that fixed source commit before continuation can execute.

The FifthAttained donor is not selected or modified; its graph-external import is not introduced.

## Unchanged scope and gates

The graph remains 377 modules and five roots. All 69 owned targets remain in their original order; both changed sources are dependency-only modules, so there is no new priority owned target. The two-source reverse dependency closure contains 28 project modules and 23 owned targets, exactly the terminal failed/blocked scope. The actual completed result confirms that no one of the 349 successful normal modules or 46 accepted owned targets is invalidated.

The driver extends the prior control chain with the exact round8 runner and selection and preserves attempts 1–8. The normal/audit commands, strict flags, original 1 GiB minimum, original baseline and external-context checks, per-target receipts and seven postflight checks are unchanged. The compile-log admission guard still requires an actual `FAIL` for every selected repair; a merely blocked module cannot be selected.

`SOURCE_SELECTION.json`, `RUN_CONFIG.json` and `OFFLINE_VALIDATION.json` describe the final prepared candidate. Three targeted delta tests passed in 0.061 seconds: unchanged complete owned scope with two dependency repairs, exact reconstruction from the real terminal stdout, and the original remote-hash gate's ordering plus rejection of stale prior controls/counts. No historical test suite or Lean compilation was repeated. Files containing `DRAFT` and `SOURCE_SCOPE_PREVIEW.json` retain the earlier nonexecutable preparation state and are not execution inputs.

After independent review of this final delta, the parent owns production installation, publication and cloud execution. The new P2 output is `.lake/p25-followup-repairs-attempt009`; it is distinct from P3's separate continuation. Historical donor evidence is not transferred as current proof acceptance. P2.5 remains unproved by this preparation.
