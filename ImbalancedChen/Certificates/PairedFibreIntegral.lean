import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Verification status: uncompiled candidate. See `docs/part2/HANDOFF.md`.

# Genuine integrals for the adopted paired positive fibre

The local certificate has coordinates `(t, u, z, w)` with
`tl < t < tr`, `ul < u < ur`, and `a < w < z < Z`.
Its integrand is `K / (80 * t * u * z^2 * w)`.

This file defines the literal iterated Lebesgue integral and evaluates it
using the fundamental theorem of calculus. The definitions contain no
stored certificate bounds. Endpoints are finite interval endpoints; for
Lebesgue measure, changing a finite set of one-dimensional endpoints does
not change these integrals.

The equality proved here does not assert that the local fibre has passed
the manuscript's region and mask checks, or that a family of such fibres
has been combined with its error ledger. Those are separate obligations.
-/

namespace ImbalancedChen.Certificates

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- The remaining genuine one-dimensional fibre integral after integrating
`1 / w` over the actual interval from `a` to `z`. -/
def pairedFibreIntegral (a Z : ℝ) : ℝ :=
  ∫ z in a..Z, Real.log (z / a) / z ^ 2

private theorem hasDerivAt_pairedFibrePrimitive {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (fun x : ℝ => -((1 + Real.log x - Real.log a) / x))
      (Real.log (z / a) / z ^ 2) z := by
  have hd := (((hasDerivAt_const z (1 : ℝ)).add
    (Real.hasDerivAt_log hz.ne')).sub_const (Real.log a)).div
      (hasDerivAt_id z) hz.ne'
  convert hd.neg using 1
  rw [Real.log_div hz.ne' ha.ne']
  field_simp [hz.ne'] <;> ring

/-- The fibre kernel is integrable on the complete closed interval.
Its logarithm and denominator stay within their actual domains. -/
theorem intervalIntegrable_pairedFibreKernel {a Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    IntervalIntegrable (fun z : ℝ => Real.log (z / a) / z ^ 2)
      volume a Z := by
  have hzpos : ∀ z ∈ Set.uIcc a Z, 0 < z := by
    intro z hz
    rw [Set.uIcc_of_le hAZ] at hz
    exact ha.trans_le hz.1
  apply ContinuousOn.intervalIntegrable
  refine ((continuousOn_id.div_const a).log ?_).div (continuousOn_id.pow 2) ?_
  · intro z hz
    exact (div_pos (hzpos z hz) ha).ne'
  · intro z hz
    exact pow_ne_zero 2 (hzpos z hz).ne'

/-- Exact analytic evaluation of the positive triangular fibre.
The hypotheses allow the degenerate endpoint `a = Z`, when both sides
are zero. -/
theorem pairedFibreIntegral_eq {a Z : ℝ} (ha : 0 < a) (hAZ : a ≤ Z) :
    pairedFibreIntegral a Z =
      1 / a - (1 + Real.log (Z / a)) / Z := by
  let F : ℝ → ℝ := fun z => -((1 + Real.log z - Real.log a) / z)
  have hzpos : ∀ z ∈ Set.uIcc a Z, 0 < z := by
    intro z hz
    rw [Set.uIcc_of_le hAZ] at hz
    exact ha.trans_le hz.1
  have hd : ∀ z ∈ Set.uIcc a Z,
      HasDerivAt F (Real.log (z / a) / z ^ 2) z := by
    intro z hz
    exact hasDerivAt_pairedFibrePrimitive ha (hzpos z hz)
  calc
    pairedFibreIntegral a Z = F Z - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (intervalIntegrable_pairedFibreKernel ha hAZ)
    _ = 1 / a - (1 + Real.log (Z / a)) / Z := by
      dsimp [F]
      rw [Real.log_div (ha.trans_le hAZ).ne' ha.ne']
      ring

/-- The actual rational kernel, written in factored form to expose Fubini
coordinates without introducing an external numerical approximation. -/
def pairedFibreKernel (t u z w : ℝ) : ℝ :=
  (1 / t) * ((1 / u) * ((1 / z ^ 2) * (1 / w)))

theorem pairedFibreKernel_eq (t u z w : ℝ) :
    pairedFibreKernel t u z w = 1 / (t * u * z ^ 2 * w) := by
  simp [pairedFibreKernel, one_div, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc]

/-- The complete local contribution is a genuine four-variable iterated
integral over `a < w < z < Z`, with the literal manuscript coefficient.
It is independent of any claimed stored lower or upper endpoint. -/
def pairedLocalIntegral (K a tl tr ul ur Z : ℝ) : ℝ :=
  (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
    ∫ z in a..Z, ∫ w in a..z, pairedFibreKernel t u z w

/-- No alternate model is hidden by the factored kernel notation. -/
theorem pairedLocalIntegral_eq_literal (K a tl tr ul ur Z : ℝ) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * ∫ t in tl..tr, ∫ u in ul..ur,
        ∫ z in a..Z, ∫ w in a..z, 1 / (t * u * z ^ 2 * w) := by
  simp only [pairedLocalIntegral, pairedFibreKernel_eq]

/-- Integrating the actual inner `w` coordinate gives the logarithmic
fibre profile. -/
theorem pairedFibreIntegral_eq_iterated {a Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z) :
    (∫ z in a..Z, (1 / z ^ 2) * (∫ w in a..z, 1 / w)) =
      pairedFibreIntegral a Z := by
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le hAZ] at hz
  rw [intervalIntegral.integral_one_div_of_pos ha (ha.trans_le hz.1)]
  simp only [div_eq_mul_inv, one_mul, mul_comm]

/-- The exact logarithmic expression for the actual local integral.
All three logarithms arise from proved real integration identities. -/
theorem pairedLocalIntegral_eq (K : ℝ) {a tl tr ul ur Z : ℝ}
    (ha : 0 < a) (hAZ : a ≤ Z)
    (htl : 0 < tl) (htr : 0 < tr) (hul : 0 < ul) (hur : 0 < ur) :
    pairedLocalIntegral K a tl tr ul ur Z =
      (K / 80) * Real.log (tr / tl) * Real.log (ur / ul) *
        (1 / a - (1 + Real.log (Z / a)) / Z) := by
  unfold pairedLocalIntegral pairedFibreKernel
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_one_div_of_pos htl htr,
    intervalIntegral.integral_one_div_of_pos hul hur,
    pairedFibreIntegral_eq_iterated ha hAZ,
    pairedFibreIntegral_eq ha hAZ]
  ring

end

end ImbalancedChen.Certificates
