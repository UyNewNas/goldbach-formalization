# Compact04: historic sieve expression repairs

Status: SOURCE_REPAIR_PENDING_ACTUAL_RETRY. Compile/kernel credit = false.

## Exact failure and existing work

The P1 compact04 input was commit `086696e51088eb93942abf2fcc1ce48e148ad842`.
Its complete log is `p1-compact-04.log` in this directory, SHA256
`f015edcbd99538444447dea15cf96860121c0972e4724f30211f0d91ffee86dc`.
It reports three denominator-cast mismatches in TableSemantics and six
errors in TrapezoidError. Only these two source files were edited here.

The shared 619-row P2 registry, SHA256
`ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`,
contains neither target module. No archive or full CI audit was repeated.
The repairs retain and reuse the existing integer ceiling bound,
quadratic-chord integral, actual DDE derivatives, and local curvature bounds.

## Frozen manuscript boundary

Read the frozen publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, directed arithmetic
  and delayed-function sections, lines 94–164; SHA256
  `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
- `verification/data/certify_extended_prefix.py`, lines 7–16 and 51–76;
  SHA256 `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.

The historical Q80 recurrence uses ordinary trapezoids of the actual normalized
factors: upper-factor convex curvature at most 2 gives the L-update allowance
`1/(6*g^3)`; lower-factor concave curvature magnitude at most 1 gives the
H-update allowance `1/(12*g^3)`. Its numerator interpolation allowance remains
`1/(8*g^2)`. The manuscript's separate P112 weighted-numerator-chord formula
is not substituted for this recurrence. All rounding layers, constants,
endpoint conventions, table definitions, and final inequalities remain unchanged.

## Minimal proof changes

| Actual error location | Repair | Classification |
| --- | --- | --- |
| TableSemantics 237/239/241 | State one local, explicitly typed Nat-to-Int-to-Real denominator identity; rewrite the real denominator back to the cast integer denominator, then apply the existing reciprocal ceiling bound directly. This avoids repeating the failed `simpa` conversion. | Cast / elaboration expression |
| TrapezoidError 68 | Remove `ring` after `field_simp` already closed the common-factor identity; rewrite with the existing quadratic integral and cancel the same nonzero `a` explicitly. | Redundant tactic and algebra normalization |
| TrapezoidError 76 | Give `hi` the explicit type `IntervalIntegrable e volume a b`. | Measure inference API |
| TrapezoidError 98/116 | Expose bare function subtraction with `Pi.sub_def`; fix `μ := volume` in `intervalIntegral.integral_sub`. | Function / integration API |
| TrapezoidError 179 | Use an explicit scalar `change` for the already-derived inverse-power derivative before denominator clearing and `ring`. | Pointwise function expression |
| TrapezoidError 242 | Type the existing local curvature result using `cellLeft j`, matching the reciprocal-bound expression consumed by `linarith`. | Definition alias normalization |

All errors are class (1), formal expression/API or strict tactic behavior.
No omitted analytic estimate is supplied; no substantive manuscript gap is
identified. The factor curvature bounds and the exact denominator 12 are retained.

The pinned Mathlib API was checked at
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`:
`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
(blob `89cf34cb5387b20f311300f6e708aa752ebf3a23`) makes the measure implicit in
`intervalIntegrable_of_Icc` and `integral_sub`; the latter's integrand is
the pointwise subtraction. The existing pinned Pi definitions supply
`Pi.sub_def` for the bare function expression.

## Static verification and source hashes

All 46 theorem headers (including private helpers) and all 27 complete
definition/structure blocks are byte-identical. Imports are unchanged.
`git diff --check` passed. No prohibited proof construct, linter suppression,
new premise, or changed numerical definition was introduced.

| File | Before SHA256 | After SHA256 |
| --- | --- | --- |
| `P2HistoricSieveTableSemantics.lean` | `1c7aedc7101576908fc10097ea2cff00abfcdf2fa030a26f2f09fd55211a3a06` | `664ca9a5c92c41adad80c55a17a04d49d6740b63492d17f01703a1a9c41b66a0` |
| `P2HistoricSieveTrapezoidError.lean` | `0dd1f5c93d4d1cfb6858d773c39b66e7912a27a519c499712178a5912de373fc` | `3b5130defd65d34c2af9a42880c111421353bc99b7fed634e70c7561a9154a98` |

No Lean/Lake, remote job, compiler, kernel replay, staging, or commit was performed.
These are minimal source candidates for the root's next actual compilation.
