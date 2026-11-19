# P5.6 / h34 — external-input boundary for Q80 initial support

This additive packet introduces **zero** new external analytic inputs and
implements **zero** external number-theory proofs.

It imports the existing fixed project definitions of the original
`P2Selected430CausalOccurrenceExporter`: `seed`, `read`,
`suffix`, `ordinaryDecision`, `scan`, `iterate`, and
`queryCell`; `Part5OriginalUpsilon5CausalDictionary.floorValue`;
and the previously submitted manuscript-local first-failure source.
Its proofs use standard imported Mathlib tactics and finite-sum rewrites.

No PNT/Mertens/BV input, distribution statement, numerical integral
certificate, F seed estimate, PP/same-rho comparison or new axiom is
postulated. These manuscript-local consumers are not relabelled as
external results. The prior dependency/analytic input ledger remains
unchanged and unaudited transitively.

Pin: `leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No Lean compilation or kernel replay was performed.
