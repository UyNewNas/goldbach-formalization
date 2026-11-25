# Compact05: range-32 integer guard and symmetric mass transport

Date: 2026-11-25. Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

## Actual failures

The input is P1 compact05 at source
`f51e91aad4a63fa5167d8a1377b988db633a817c`. Its recorded log is
`p1-compact-05.log`, 17,685 bytes, SHA-256
`916894d7a1d84a6fde68dd230d3bca2b9c8248b19fe66f6e37c24d21f5e9ab38`.
Only the two assigned production files were edited, at the three reported
proof sites. No compiler, cloud job, new CI/archive audit, or generator ran.

## Frozen formulas and unchanged construction

The already frozen 1106 sources at publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` were consulted:

- `numerical-appendix.tex`, SHA-256
  `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`:
  directed floors/ceilings, four-product interval multiplication, and
  positive denominator guards.
- `certify_extended_prefix.py`, SHA-256
  `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`:
  `density_mass` uses the reciprocal-box factor
  `4*D*(z1-z0)/(z0*z1)` and the two logarithmic widths;
  `symmetric_half` halves the lower endpoint downward and the upper
  endpoint upward once before the final cell product ceiling.

The existing original-positive implementation remains unchanged:
z = 1-1/x, P160 = 2^160, all 256 loop updates, the original tail and the
rounded log(2) multiple. The range-32 branch still reduces by exact powers
of two and retains its `<= 2` exits, including equality at 2, 4, 8, 16 and 32.
The odd-power formula described elsewhere in the appendix was not
substituted for this existing construction. The separately named historical
`numerical-w2-affine-series-independent-20261010.py` remains outside the
already available bounded local source set; no new full source-equivalence
claim or wider retrieval is made here.

For the symmetric mass, the existing proved `symmetric_mass_formula` gives
`log(b/a)^2 * (4*(d-c)/(c*d)) / 2`. The literal integer operation tree remains
`divNat (mul (mul lx lx) (literalMassZ z0 z1)) 2`, followed later by the
unchanged `up (high*mass.hi) P160`. No second half, reassociation, extra
normalization, altered interval operation or new assumption was added.

## Repairs and classification

| Original location | Repair | Classification |
|---|---|---|
| `ActualThirdOriginalPositive256LogRange32IntegerGuard:125` | Replace `mul_le_mul_left` with `mul_le_mul_iff_right₀`, using the existing proof `0 < (128 : Int)`. | Current positive common-left-factor cancellation API. |
| Same file, 172 | From `hupper : x1 <= (25/128)*D`, explicitly multiply both sides by nonnegative 128, then prove `128*((25/128)*D)=25*D` by `ring`. Keep the existing `exact_mod_cast`. | Elementary algebraic normalization omitted from the failed `linarith` path. |
| `ActualThirdOriginalSymmetricMassCeil:115` | Rewrite `Nat.cast_ofNat` before the existing mass equality `heq`. | The inferred divisor was `((2 : Nat) : Real)` while `heq` used `(2 : Real)`; no numerical discrepancy. |

The explicit multiplication pattern already occurs in
`ActualThirdOriginalPositive256LogIntegerGuards`, which compact05 reports
as `DIAGNOSTIC_PASS_NOT_ACCEPTANCE`. The integer-width argument, positive
first series term, original rounded-log positivity, and all weak/strict
coordinate boundaries remain unchanged. No substantive mathematical gap
was identified in these three reported errors.

## Source bindings and verification boundary

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/ActualThirdOriginalPositive256LogRange32IntegerGuard.lean` | `b362a2b87de847bfeddf4e7acb3adc349377cf68064283063b00a7baa3c175ab` | `42f7f6e1b94a7fbfa1dba89b2c96bf6f5c81c15a2e40ce0cb7563cfd9ec87afa` |
| `ImbalancedChen/ActualThirdOriginalSymmetricMassCeil.lean` | `89af05ca540777586db8707a78ae7840152399937a962ca128b7af5333f19a3a` | `e0d25d340908d8006271b8804154d64f02580bf4c258890b8338ca8b0a97bb2c` |

Captured pre-edit comparisons show all 11 theorem headers, including private
helpers, and all three computational declarations byte-identical. Imports
are unchanged. `git diff --check` passes; no proof placeholder, new axiom,
`native_decide`, `unsafe`, or linter-disabling option was added. This task
did not stage or commit. Root owns the next actual Lean run; these edits
have no new compilation, kernel, finite-evaluation or completion credit.
