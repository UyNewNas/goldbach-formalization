# Canonical cell00 binding and complete parse/decode diagnostic

Status: **SOURCE ONLY / NOT COMPILED**. No new runtime or theorem acceptance is claimed.

`P2Saving16CanonicalCell00Binding.lean` imports the unchanged OriginalInput owner and the already accepted raw attempt003 module. It first states `originalText (0 : Fin 14) = oldString00` by `rfl`, then composes that equality with the existing `originalStringeq00`. It adds no loader and does not reprove the raw 53,305-character identity.

`P2Saving16CanonicalCell00ParseDiagnostic.lean` imports that binding, the unchanged M16 Decoder and the accepted SourceJson character-input companion. Its closed target is precisely the original `parsedCellSuccess 0` after expanding the two original definitions: the full original parse, full `decodeCell`, and the same Except-constructor Bool test. It rewrites the entire parse/decode bind through the existing representation theorem and attempts the remaining original predicate with `decide +kernel`. No success premise, smaller fuel, parser substitute, prefix check or record-equality test is added.

The sources do not import or modify FiniteArchive or its four closed guards. The binding has a three-project-module source closure; the consumer has nine. The detailed selected-source hashes, exact original target blocks, actual raw acceptance receipt/object binding and generic helper receipts are in `MANIFEST.json`.

## Required execution order

1. Reuse the now actually accepted Input792a and Decodere1b23 objects from b80. Their strict normal, independent replay, complete owned inventories (3 and 84 declarations), and Input fresh fourteen-file binding are recorded in `RUNNER_MANIFEST.json` and `PIN_READY_REVIEW.json`. Runtime must revalidate those exact files and receipts.
2. Reuse the accepted raw attempt003 object `a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a`, source `d2353e0a96ce78a8ba2da3d3d47f835593dcf758ea6110fd088c82df038f008c`, and full seven-declaration receipt. Do not recompile its large equality.
3. Compile, independently replay and completely audit only the new canonical binding first. Preserve that result before starting the separate consumer.
4. Attempt the consumer with the original strict gates and a separate resource/result record. A consumer failure gives no parse/decode success and must not erase a valid canonical binding result.

Each stage needs one isolated union library for the `ImbalancedChen` package, containing the exact bound prerequisite objects. Multiple package roots are not a per-file fallback. The source preparation performed no cache installation, synthetic compilation-record creation or remote execution.

The subsequently prepared two-stage runner is documented in `RUNNER_README.md` and has its own independent review. Its manifest is now `READY_FOR_BOUNDED_RUN` after the actual b80 evidence was checked. The runner and these two candidates have not yet executed. The original NOT_READY manifest, old reviews, two Lean source files and source manifest are preserved; the later readiness evidence is separate. The original pending wording in frozen preparation sources describes their historical state.

No source options are added. In particular the raw module's local maxRecDepth setting is not silently treated as an option inherited by these consumers. Any future execution records must report their actual effective options and preserve the approved budgets and gates.
