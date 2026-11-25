# Canonical cell00 binding and complete parse/decode diagnostic

Status: **SOURCE ONLY / NOT COMPILED**. No new runtime or theorem acceptance is claimed.

`P2Saving16CanonicalCell00Binding.lean` imports the unchanged OriginalInput owner and the already accepted raw attempt003 module. It first states `originalText (0 : Fin 14) = oldString00` by `rfl`, then composes that equality with the existing `originalStringeq00`. It adds no loader and does not reprove the raw 53,305-character identity.

`P2Saving16CanonicalCell00ParseDiagnostic.lean` imports that binding, the unchanged M16 Decoder and the accepted SourceJson character-input companion. Its closed target is precisely the original `parsedCellSuccess 0` after expanding the two original definitions: the full original parse, full `decodeCell`, and the same Except-constructor Bool test. It rewrites the entire parse/decode bind through the existing representation theorem and attempts the remaining original predicate with `decide +kernel`. No success premise, smaller fuel, parser substitute, prefix check or record-equality test is added.

The sources do not import or modify FiniteArchive or its four closed guards. The binding has a three-project-module source closure; the consumer has nine. The detailed selected-source hashes, exact original target blocks, actual raw acceptance receipt/object binding and generic helper receipts are in `MANIFEST.json`.

## Required execution order

1. Wait for actual current Input792a and Decodere1b23 source/object/input-bound compilation, replay and complete owned acceptance. Their queued four-owner job is not credited by these source files.
2. Reuse the accepted raw attempt003 object `a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a`, source `d2353e0a96ce78a8ba2da3d3d47f835593dcf758ea6110fd088c82df038f008c`, and full seven-declaration receipt. Do not recompile its large equality.
3. Compile, independently replay and completely audit only the new canonical binding first. Preserve that result before starting the separate consumer.
4. Attempt the consumer with the original strict gates and a separate resource/result record. A consumer failure gives no parse/decode success and must not erase a valid canonical binding result.

Each stage needs one isolated union library for the `ImbalancedChen` package, containing the exact bound prerequisite objects. Multiple package roots are not a per-file fallback. No runner, cache installation, synthetic compilation record, Git action or remote task is part of this source-only package.

No source options are added. In particular the raw module's local maxRecDepth setting is not silently treated as an option inherited by these consumers. Any future execution records must report their actual effective options and preserve the approved budgets and gates.
