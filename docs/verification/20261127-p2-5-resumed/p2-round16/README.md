# P2.5 round 16: accepted original cell-0 after-Seed7 semantics

The native P2 job `e45dc88ab5d545ca925360a478d607f3` completed on source
`ed611834b2af8d14d9d468b98dd1e63cdd8a38e9`. Its normal closure is
360/377 (359 reused); its full owned-declaration acceptance is 52/69.
The newly accepted owner is `P4AOriginalAscendingCell0AfterSeed7`, with
29 declarations. Normal compilation, stock kernel replay and the complete
owned declaration/type/transitive-axiom audit passed for that owner.

All nine original postflight checks are true. The raw terminal result,
normal and audit logs, new owner artifacts, exact object archive, and
transport hashes are preserved here. Export job
`9edd1b39ab894da7a034a11477e74b5e` transported these existing bytes; it did
not rerun a proof. The compiled theorem uses `VariableEnvelope.C` and has
no additional implicit `C` parameter, as checked against the complete
native type by `check_constant_binding.py`.

One module directly failed: `P4AOriginalAscendingCell0Literal96`. Four
private vector identities produced eleven rational-coordinate reduction
errors in `decide`; sixteen dependent modules remained blocked. The
original 96 rows have not changed. The existing round-17 candidate replaces
those four unnecessary computations with definitional equality proofs.

This is a scoped acceptance, not completion of P2.5. The full fourteen-cell
finite arithmetic, physical geometry, integral assembly and common signed
compiler/distribution obligations remain tracked by `ACCEPTANCE_SCOPE.md`.
