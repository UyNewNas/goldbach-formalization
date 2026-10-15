# CI runtime and trigger repair

This change restores the original integration-PR verification jobs and makes the original full core workflow reusable by an exact, pure root-dispatch commit. All original proof outcomes remain required. No mathematical source, dependency pin, or declaration-migration verifier is changed in this publication.

The lightweight PR admission reads the exact synchronize before/head delta using isolated inline Python and Git. It skips duplicate heavy work only for a verified same-repository, one-parent commit changing exactly one known dispatch file. All ambiguous, failed, fork, mixed, and multi-commit cases retain the original heavy gates. The shared heavy lock belongs only to the actual heavy jobs; their original IDs remain. A visibly skipped duplicate job is not fresh proof acceptance. GitHub may treat a skipped required job as satisfied; this scheduling outcome must not substitute the actual root-dispatch verification result. No branch-protection setting was changed or asserted.

Actual compiler children use the fixed toolchain with -t0 -j2 -M4096 and a shared inherited compiler slot. Native compiler flags and the bundled checker policy remain unchanged. Runtime/input/wrapper/script hashes and actual normalized commands are audited. The first full environment probe follows cache preparation, before formal verification.

The 35 static/stub tests and syntax checks are recorded here. They do not establish that the new workflows run successfully, or that any Lean proof passes. This publication is explicitly [skip ci]; a later separately authorized pure dispatch is required for real verification.
