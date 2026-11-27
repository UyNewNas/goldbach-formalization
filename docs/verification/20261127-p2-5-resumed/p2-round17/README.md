# Round 17: complete literal Cell00 rows accepted

The P2 task `3fda29a9291941b78840da0249e6fb0f` completed at source
`f0c80794844b7a1318eb386ce454988af1c678a3`. Its original terminal receipt,
normal and audit logs, complete new-owner artifacts and exact compiled object
were transported by task `b37c653bb62f4f2eb2fb6d3c89c6f395`. All 31 exported
files were checked against the capsule and per-file SHA-256 values before use.

## Accepted scope

- Normal compilation: **361 of 377**, including **360 exact qualified reuses**.
- Complete owned-declaration audit: **53 of 69**.
- New accepted owner: `ImbalancedChen.P4AOriginalAscendingCell0Literal96`,
  **8 declarations**, with strict normal compilation, stock `leanchecker`
  replay, complete declaration/type and transitive-axiom audit.
- All **nine** source, environment, gate and prior-result postflight checks
  passed. The original 377-module scope and 69 owned targets were retained.

The result is not acceptance of the complete P2.5 endpoint. There is one direct
normal failure, `P4AOriginalCell0AffineChronology`, and fifteen downstream
blocked modules. The corresponding owned audits reject their missing accepted
compilation context; they are not sixteen independent mathematical failures.

## Actual remaining failure

The preserved full failure log identifies a rational `decide` reduction at
`plane_row_exact`, ambiguous unqualified `R` names in tactic unfold lists,
the `evalAffine`/`evalRow` expression mismatch at a rewrite, and an order proof
whose exhaustive tactic branches report `No goals to be solved`. The compiler
stopped after its normal maximum of 100 errors. Later source positions therefore
must be checked after the first failures are repaired; this receipt asserts no
success for them.

The original mathematical statements, affine rows and manuscript scope remain
unchanged. The next candidate is limited to this actually failed owner.
