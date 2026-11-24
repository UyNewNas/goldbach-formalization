# Batch8 first-five residual repairs

Status: **source-only candidates, complete actual error logs reviewed, not compiled**.
The final record is `MANIFEST.json`; `PRELIMINARY_MANIFEST.json` preserves the earlier state before the complete logs arrived.

## Exact scope

The source baseline is Git commit `15fbbdd842d11df0ca4db340cae2eddfa7ed39d7`. Only these two failed modules are supplied:

| Module | Preimage SHA256 | Candidate SHA256 |
| --- | --- | --- |
| `P4AOriginalFull87SourceDictionary` | `50a8b31050fde72e41fb7ba0d03ede59d9f21998cbb448eb8a3c099871f82be5` | `623b24cec83e7a232dca41dbfcab3070866c7e5480e2d1ddb35efcd1d54a9803` |
| `P5OriginalPhaseBPhysicalBinding` | `ff4abdbcc5385f37ad37924f25033ee28854a1c4134e5a7a876d9b4975bbae80` | `5b04f98525802be49fea6f130186201f2ebb17b43d8df9543a3614c013ac098d` |

## Complete observed failures and repairs

The Batch8 first-five command exited 1 after 499.083589816 seconds. Its complete 242284-byte log has SHA256 `e577ae9114ee7811bebc250d82e6411c71f36d2c32989c349b864befcf77e270`. The original `SOURCE_INSTALL.json` independently confirms both exact preimages above. Both extracted module blocks occur byte-for-byte in that complete group log.

Full87 has four error sites, containing seven remaining goals. Every goal is `t ⟨2, …⟩ = t 2` or `t ⟨3, …⟩ = t 3`. The repair reuses the explicit `Fin.ext rfl` and `simp only` pattern already present in `P5OriginalAdoptedEighthPhysicalMasks.PhysicalRows.current_residual_gt_last`. It changes only the proofs of `source_all_old_tents` and `oldSubsetSum_third_masks`. The complete error block is 2788 bytes, SHA256 `e01827616863bc8c34974475d890e51e029b258f44dabf8147f6a7ec329e4b04`.

PhaseB has one error site containing all 63 nonempty-subset cases. Each has a concrete rational left side and the identical right side `(1 + P5OriginalAdoptedEighthPhysicalMasks.e h3Cell00Vertex) / 2`. The existing definition is `e t := t 0 + t 3`; slot 58 selects `VariableEnvelope.A (e t)`. The only change adds that fully qualified existing definition to the existing `norm_num` list. The complete error block is 25828 bytes, SHA256 `ad9baddd80096fecd0edc07be517409b1d422170cf90f439cece259c3b6ec42d`. This review does not rerun or replace the numerical checker.

These are expression and definition-expansion repairs. No omitted analytic argument or substantive manuscript gap was identified in these complete failure contexts. Actual proof acceptance awaits the next normal build and subsequent audits.

## Interface and manuscript checks

All 23 public theorem headers and all 11 definition bodies are unchanged. Imports, namespaces, owners and options are unchanged. Only three existing proof bodies change; there are no new global declarations, assumptions, evaluators, `sorry` or axioms.

At manuscript pin `a988cba584d803ae2856a0de50efb582f4f3dd6a`, the relevant 1106 main-text references are `paper/release-20261106/en/argument.tex` lines 213–219 and `sieve-appendix.tex` lines 202–217 (`sv:eighth-range`, `sv:eighth-density`). The pinned supporting review `proof-library/source/eighth-history-first-failure-analytic-review-20261009.tex` lines 11–20 and 61–70 gives `e=t₁+t₄`, `R=A(e)` and the selected old-plane bounds, including the omitted winner's literal identity. The distinction between a weak old-plane check at one witness vertex and strict interior/causal admission is preserved.

Existing-work searches found six local copies and only two distinct versions per module: the earlier failing version and the current Batch8 preimage. No later accepted donor or receipt was found; the pending-repairs agent independently confirmed that result.

## Handoff

`ImbalancedChen/` contains the two complete candidate files. `CANDIDATES.patch` is their combined minimal patch. `MANIFEST.json` and `ERROR_REVIEW.json` bind the unchanged interfaces, actual error blocks, original command and source-install records. Parent-controlled publication and cloud verification are the next steps. No canonical file, cloud environment, passed module or numerical page was modified or recompiled by this task.
