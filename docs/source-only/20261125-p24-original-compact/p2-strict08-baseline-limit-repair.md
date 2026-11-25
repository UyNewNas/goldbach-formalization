# Strict 08: pointwise baseline-limit normalization

The original P2 strict-symbolic-08 checker compiled proof source
`4ac06da3`. Its complete `p2-strict-symbolic-08.log` is 7,480 bytes;
SHA-256 `580e1ad83e9bd1b7fdd9694f40b881eb4e3801eb772ad8e3041742f7fa700e0a`.
The batch finished with 293/321 symbolic modules successful, comprising
289 reused records and 4 fresh passes. Three modules failed directly.

## Actual failures and manuscript boundary

At old line 77 of `P4ACompactBaselineLimit.lean`, the assembled `Tendsto`
proof retained function composition and pointwise function division. Its
mathematical expression agreed with the declared baseline limit, but the
existing `simpa only` did not normalize those function applications.
At old line 91, the proof concerned the explicit function
`fun k => actualExtendedThirdDyadicStep k / 8`, while the target retained
the bare function constant `baselineBuffer`.

Both failures are expression/API normalization issues. The frozen 1106
`argument.tex`, in the upper-construction section, fixes `rho = 19/96`
and `theta = 299/500`; `certify_extended_prefix.py` uses the same exact
fractions. The current `thirdPrefixRho` and `thirdPrefixTheta` definitions
match those values. The existing baseline uses the actual floor stop in
both its leading denominator and upper-factor argument. Its limiting
expression is unchanged:

`(2 * exp(-gamma) / rho) * suzukiContinuousUpperFactor (theta / rho)`.

The continuity supplier remains the existing
`continuousOn_suzukiContinuousUpperFactor` on `Ioi 1`; the existing proof
establishes `theta/rho > 1` before applying it. Buffer and mesh convergence,
legal-buffer assumptions, the actual floor operation, and the limiting
root are unchanged. No additional regularity or nonvanishing premise is
introduced.

## Minimal proof edits

- Add `Function.comp_apply` and `Pi.div_apply` to the existing final
  simplification of the product/composition limit.
- In `tendsto_baselineBuffer`, first `change` the target to the explicit
  pointwise function, then simplify only `zero_div` in the existing
  `Tendsto.div_const` proof.
- Replace the sole single-goal `field_simp ... <;> ring` sequence in
  `baselineMesh_step` with successive `field_simp` and `ring` tactics.
  The source-bound baseline `unnecessarySeqFocus=false` exception is not
  carried over to the changed source; no linter setting is changed.

Static comparison against `4ac06da3` confirms that the entire diff is
exactly these three proof replacements. All nine public theorem headers,
three complete definitions (`originalOrdinaryRoot`, `baselineBuffer`,
`baselineMesh`), and two imports remain byte-identical.
`git diff --check` passes.

Original source SHA-256:
`696ce1ba4e97ac69af24fcaa7965b75048ef80661cafd61376ad48acb0f1ad6a`.

Frozen candidate SHA-256:
`ab28a21f60a0fb9f56d1b56d84f34cbadf4326b15d179999f33ca09f0bb7b46e`.

The candidate has not been compiled. Strict elaboration and lint remain
for the next original-checker run; no new compilation or kernel credit is
claimed. No index, remote task, or running P2 input was changed.
