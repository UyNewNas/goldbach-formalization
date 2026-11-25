# Saving19 pure JSON diagnostic

## Subsequent String.length isolation

The only additionally authorized isolation also failed at the same 6144 MB
budget. Job `da2b8f472ebd4fc7b266c0bdc8eff255` attempted only
`geometry00Text.length = 195134` with `decide +kernel`, importing `Lean`
alone. It did not import or call SourceJson. It ended with `memory_limit`,
exit 137, after 21.856370210647583 seconds, with 21.73 CPU seconds and a
recorded peak RSS of 6154.61 MB. The wall-time limit was 60 seconds; no
resource increase or repeated complete parser run was performed.

The preflight confirmed the same 195134-byte fixture SHA256, ASCII=true,
and UTF-8 character count=195134. This host computation only supplied
and checked the expected text length; the proposed closed length equality
still had to be proved by the kernel and did not obtain acceptance.

This failure is already present without JSON syntax recursion or any
typed payload. For the pinned standard library, String.length unfolds to
String.toList.length, and String.toList passes through UTF-8 decoding.
Moreover SourceJson.parse evaluates its initial fuel from this length.
The results therefore justify investigating the original text/character
list representation before changing JSON semantics or typed decoders.
They do not identify the exact allocation hotspot without a reduction
profile, and do not establish that the length equality is false.

The exact task output, resource response, local input source and invocation
are retained in STRING_LENGTH_RESULT.json, evidence/, and
logs/string_length00-task-output.log. A subsequent read-only command to
export the redirected compiler log and post-run object listing was rejected
by the backup service with `retained-job limit reached; ask owner to archive
jobs`. No existing job was deleted or altered. That compiler log is marked
unexported; its contents and target-object absence are not fabricated.
No leanchecker or completed axioms acceptance is claimed for this failure.

## Recorded outcome

The exact original geometry cell 00 pure JSON success-tag goal did not
complete: the backup `cloud_compile` service terminated job
`e7989022f6e94b0990903107304b045b` with `memory_limit`, exit 137, after
30.89200448989868 seconds. Recorded peak process-tree RSS was 6147.96 MB
under a 6144 MB budget; CPU time was 30.78 seconds. No target olean was
created. The normal compiler log was empty, and the post-theorem axioms
command was not reached. No independent leanchecker run was attempted
on this failed target. This gives no formal credit and is not evidence
that the input is invalid JSON.

The theorem statement is exactly:

```lean
(SourceJson.parse geometry00Text).toOption.isSome = true
```

Its proof body is `by decide +kernel`. The only imported project module
is the byte-identical `P2OriginalSaving19SourceJson`. There is no typed
Geometry/Moments decoder, record equality, rational arithmetic, row
checker or host mathematical replay. The original moment 00 text is
also loaded as an ordinary String literal but its parser is not run.

The result narrows the resource failure to this pure String/JSON
diagnostic. It excludes the typed decoder and payload equality as
necessary causes of this failure; no reduction profile identifies the
specific primitive or field responsible.

## Reader and fixture binding

The source reader was copied from the backup environment's
`/workspace/p1-stage-20261124/ImbalancedChen/P2OriginalSaving19SourceJson.lean`.
It is exactly 6035 bytes, SHA256
`ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424`,
and matches P1 baseline `298670f119d24874b719facb3ef756f1e01223a1`.

Only this foundational reader was newly compiled before the diagnostic.
Reader normal job `b441e27fb7354fefa854b7c6b12c250c` succeeded in
2.4533950389998154 compiler seconds, with a recorded peak 888.68 MB.
Its olean has SHA256
`ec7361a2e508c323bf2dfa5f384d31a4bd71ffd47e032bfbf428c13bc1c2e467`
and size 741272 bytes. This is a normal compilation record, not a new
independent full-owned acceptance claim.

The geometry 00 fixture is 195134 bytes with SHA256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.
The moment 00 fixture is 28999 bytes with SHA256
`d88e9d02334dfa840f81c0e2be8e97d559978ac3848fdea13990deced9a65052`.
Both exact size/hash pins were checked before and after the run. Their
existing original files were only read and were never rewritten.

## Reproducibility and limits

All remote writes were inside the new dedicated directory
`/workspace/p26-parser-diagnostics-20261125`. All source, command and
log files are synchronized in this candidate directory. The remote
collection job was `d38f6bfcf0b148aaa997d5842f035296`; it succeeded.

`SOURCE_MANIFEST.json` records the immutable preparation inputs.
`RESULT.json` records the observed failed outcome. `evidence/` retains
the exact compiler environment metadata, task responses and exported
file hashes. `logs/geometry00-normal.log` is intentionally empty,
matching the observed remote file rather than a fabricated diagnostic.

The exact invocation used `maxRecDepth=1000000`, `maxHeartbeats=0`,
one CPU thread, a 6144 MB process-tree RSS budget, and a 180 second
wall-time limit. No P1/P2/P3 compilation queue or production source was
modified. No 216-module supplier rebuild was performed.
