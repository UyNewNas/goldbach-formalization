# Synthetic exact String/Char-list bridge diagnostics

## Latest authorized phase isolation: data-only prefix passed normal

After the three binding candidates below, Root authorized exactly one final
stage-isolation run. `P2OriginalSaving19StringChunks2KiBDataPrefix.lean` gathers
all five independent data declarations from the existing 2 KiB probe and its
emitting elaborator, preserving each line verbatim and retaining the two
`noncomputable` character lists. All theorem goals are absent.

The prefix passed normal compilation in **2.919216 seconds**, exit **0**, with
peak sampled process-tree RSS **1614929920 bytes** under the unchanged 2 GiB /
60-second budget. All eight explicitly flushed stderr markers were observed
in order, ending in `all_data_complete`. The generated olean is 111624 bytes,
SHA256 `e886e629f676b10d8b445b9a7af16a42f71c05ff8988352b380fa0886d5b5ad9`.

The source SHA256 is
`d5cb8eb426fec95fb734ba65df1cea733ed28a12f0fbed099e93b45e0e836f1a`.
See `DATA_PREFIX_MANIFEST.json`, `DATA_PREFIX_RESULT.json`, and its exact normal
log in `logs/`. No independent kernel replay was requested or performed for
this data-only phase diagnosis; this is not acceptance of a binding theorem.

This isolates the successful small-scale data-definition part: quoting two
1 KiB character lists and elaborating their String data definitions can finish
under this budget. The previously failing full 2 KiB candidate also asks for
concrete String binding/conversion proofs. Which of those proof commands or
reduction phases is expensive remains unprofiled. The result does not certify
128 KiB data elaboration, any actual fixture, any original Core equality, or
parser success. No further binding or larger-input run followed.

A source review before this last run found that `run_cmd` normally isolates
stderr as messages: `Lean/Elab/BuiltinEvalCommand.lean:228` uses
`Core.stderrAsMessages`, whose default is true in `Lean/CoreM.lean:581–584`.
The prefix explicitly sets `stderrAsMessages false`; each tiny marker calls
`IO.getStderr`, `putStrLn`, and `flush`. This is why the final stage evidence is
durable rather than depending on unflushed snapshot diagnostics.


## Earlier complete binding probes

Three separately authorized representations were tested locally with the same
2 GiB sampled process-tree RSS limit, 60-second wall limit, and one Lean thread.
All three stopped at the RSS limit during normal compilation. None produced a
target olean; no independent leanchecker replay or axiom audit could follow.
These are diagnostic failures, not counterexamples to the stated equalities.

| Candidate | Normal time (s) | Peak sampled RSS (bytes) | Exit | Olean |
|---|---:|---:|---:|---|
| P2OriginalSaving19StringOfList128KiBProbe | 13.586768 | 2148528128 | -9 | no |
| P2OriginalSaving19StringOfList128KiBNoncomputableProbe | 13.898906 | 2147651584 | -9 | no |
| P2OriginalSaving19StringChunks2KiBProbe | 12.524709 | 2148028416 | -9 | no |

The first source uses a 131072-byte independent synthetic String literal and
an explicitly emitted character list. The second changes only its namespace,
`explicitChars` from `def` to transparent `noncomputable def`, disables
`Elab.async`, and adds `#check` stage messages. Its literal data, closed
statements, and proof bodies are unchanged; this is machine-checked in
`FOLLOWUP_RESULT.json`. Avoiding executable compilation for the character-list
definition did not make this whole candidate pass the stated budget.

The third is the authorized small fallback: two distinct 1024-byte ASCII
chunks, each an independent String literal plus an emitted List Char; a
separately fixed 2048-byte String literal is their concatenation. The exact
closed theorems in the source are:

```lean
chunk0_eq_ofList : chunk0 = String.ofList chars0
chunk1_eq_ofList : chunk1 = String.ofList chars1
original_eq_append : originalText = chunk0 ++ chunk1
original_toList_eq : originalText.toList = chars0 ++ chars1
```

The first three use `rfl`. Intermediate chunk `toList` equalities use
`String.toList_ofList`, and the final theorem uses `String.toList_append` plus
those equalities. This small complete candidate also failed its budget. No
128-block candidate, full-source parse, length goal, actual fixture, production
source, remote job, or P1 queue was touched by these local probes.

## Phase evidence and its limit

All three normal logs are empty. `#check` messages plus `Elab.async=false` did
not supply an observed durable stage boundary before the monitor killed the
process. Empty redirected stdout must not be read as proof that the first
String declaration, character-list elaboration, or `rfl` was the failing
operation. The exact phase remains undetermined.

The same-pin reporting code supports this caution: `Lean/Language/Basic.lean`
414–459 routes snapshot messages through `IO.print`/`IO.println` and does not
flush the stream there. `Lean/Elab/Frontend.lean` 334–343 runs the snapshot tree
reporter. A future phase-only diagnostic would need explicit stream flushing
or separately compiled prefixes; neither was silently added after the last
resource failure.

## Source mechanism relevant to the hypothesis

The local runtime is Lean 4.33.0-rc1, commit
62eed1db4d67327ec8120be05f1a1b0847d74561, under
`/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux`.

- `Lean/ToExpr.lean` 189–191 emits a Char as `Char.ofNat` of a Nat literal;
  239–248 emits a List as a nested constructor expression.
- `Lean/Meta/ExprDefEq.lean` 220–229 handles literal-versus-`String.ofList`.
- `Lean/Meta/WHNF.lean` 27–30 handles a String literal by weak-head normalizing
  `String.ofList` applied to a Meta-emitted character list.
- `Init/Prelude.lean` 3514–3515 defines `List.utf8Encode` through character
  encoding, flatMap, and a byte-array builder; its own comment calls this an
  inefficient model implementation. Lines 3557–3558 define `String.ofList`
  using that model. `noncomputable` does not remove this logical body or its
  role in kernel conversion.
- `Init/Data/String/Basic.lean` 334 and 385 provide the exact structural
  `String.toList_ofList` and `String.toList_append` consumer theorems.

These observations explain why a Meta literal optimization is not itself a
large-value kernel cost guarantee. They do not identify which reduction or
compiler phase exhausted the memory in these runs. The source review does not
replace the missing closed input-binding certificate.

## Preserved exact-data obligation

The emitter `toExpr s.getString.toList` generates data only. A host equality,
ASCII check, byte count, or SHA never substitutes for `original_eq_ofList` or
`original_eq_append`. Any eventual application to accepted ArchiveCore must
still prove equality with its unchanged original `geometryText` or
`momentText`; no such theorem is claimed here.

The existing data-independent parser/character bridge belongs to the separate
`archive-char-input` candidate and can consume a checked old-text equality.
Its availability does not discharge the concrete binding or parser-success
obligations for the real fixtures.

## Files and reproducibility

`run_probe.py` records the exact argv, source SHA, limits, sampled RSS/CPU,
exit code, and resulting object state. `logs/` preserves each run independently.
`MANIFEST.json`, `NONCOMPUTABLE_MANIFEST.json`, and `TWO_CHUNK_MANIFEST.json`
are frozen preparation records; the matching result files record observation.
`FOLLOWUP_RESULT.json` includes all three results and controlled-delta/static
checks. All owned Lean candidates are free of forbidden proof escapes.

The original text SHA is
364a1ccfa1b7efaf34434f4906e173f76a51c443a53a56747de0f8aa27fbe3a2.
The source SHAs and exact per-chunk data hashes are in the manifests. Logs and
failure records remain intact. No accepted P2.6 theorem is claimed.
