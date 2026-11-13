# P4 inventory diagnostic handoff (2026-11-13)

Status: SOURCE_ONLY_UNCOMPILED. No CI dispatched by this preparation.

- Failed reference run: 43108198136.
- Driver baseline: fb34e16802e8d0dffdd7d77b3ab442fc84ad55ed.
- Exact unchanged proof source: 4c2d214d2d40160dc400e4b7816f4189f482b374.
- Diagnostic code commit: 6db365047227e79e3c7f4b78db30f7df23e1587c.
- Reused byte-for-byte exporter: docs/source-only/20261113-resume/p2-validation-v6/reused/Round6Audit.lean at 81cb87f5cd18ab8dc4e85300340de92d91c551bb.

Static comparison confirmed that removing the diagnostic insertion yields exactly the original P4 Round6Audit.lean bytes. No declaration, proof source, dependency pin, rejection predicate, type export, axiom allowlist, object snapshot or runtime requirement was changed. The mismatch still throws the original error after flushing a JSON diagnostic. The diagnostic lists multiplicity differences, canonical owners, and occurrences across loaded module data. It does not infer the cause or make the mismatch acceptable.

Next: after currently running Stored031-041 and pending P2 r5, validate this P4 compact profile using this branch's candidate-validation.yml through a deliberate isolated trigger. The existing workflow_dispatch entry checks out github.sha and the unchanged proof source. For a push trigger, first isolate unrelated workflow triggers and target this branch. Never dispatch a second heavy job solely because this file exists. Retain the full 146-module closure, kernel replay, complete serialized types/axioms, strict ownership, immutable objects and 12 GiB trust-zero audit. A diagnostic failure is expected unless the actual root cause is separately repaired; report its exact difference rather than marking green.

This compact profile does not validate the complete six-target P4 scope or hUpper, and cannot establish mathematical closure.
