import ImbalancedChen.Part3ImaginaryOrderKSecondQDerivative
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24.  No acceptance credit.

The actual integral K_t(q) is tested against a C² real function with compact
support strictly inside a positive finite interval.  We use the previously
proved actual q-derivatives and modified-Bessel ODE.  A product derivative
and the finite-interval fundamental theorem give the weak Bessel eigen
identity; support, rather than an assumed boundary condition, kills the
endpoint flux.  No automorphic spectral assertion is made.
-/

namespace ImbalancedChen.Part3.ActualKWeakBesselTest20261024zz

noncomputable section

open Set
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKSecondQDerivativeSourceOnly

/-- Flux used when testing the actual radial Bessel equation. -/
def kTestFlux (t : ℝ) (h : ℝ → ℝ) (q : ℝ) : ℝ :=
  q * qDerivative t q * h q

private theorem test_deriv_continuous (h : ℝ → ℝ)
    (hh : ContDiff ℝ 2 h) : Continuous (deriv h) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) h := by simpa using hh
  exact (contDiff_succ_iff_deriv.mp hs).2.2.continuous

/-- Differential Green identity before removing the endpoint flux. -/
theorem kTestFlux_hasDerivAt (t : ℝ) (h : ℝ → ℝ)
    (hh : ContDiff ℝ 2 h) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (kTestFlux t h)
      (q * qDerivative t q * deriv h q +
        q * imaginaryOrderK t q * h q -
          4 * t ^ 2 * imaginaryOrderK t q * h q / q) q := by
  have hD := qDerivative_hasDerivAt_qSecond t hq
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have htest := (hdiff q).hasDerivAt
  have hproduct := ((hasDerivAt_id q).mul hD).mul htest
  have hraw : HasDerivAt (kTestFlux t h)
      (qDerivative t q * h q +
        q * qSecond t q * h q +
          q * qDerivative t q * deriv h q) q := by
    convert hproduct using 1
    · funext r
      rfl
    · ring
  have hODE := actual_K_modifiedBessel_equation_integral t hq
  have hmul : q *
      (qDerivative t q * h q +
        q * qSecond t q * h q +
          q * qDerivative t q * deriv h q) =
      q ^ 2 * qDerivative t q * deriv h q +
        q ^ 2 * imaginaryOrderK t q * h q -
          4 * t ^ 2 * imaginaryOrderK t q * h q := by
    linear_combination (h q) * hODE
  apply hraw.congr_deriv
  calc
    qDerivative t q * h q +
        q * qSecond t q * h q +
          q * qDerivative t q * deriv h q =
      (q ^ 2 * qDerivative t q * deriv h q +
        q ^ 2 * imaginaryOrderK t q * h q -
          4 * t ^ 2 * imaginaryOrderK t q * h q) / q :=
            (eq_div_iff hq.ne').2 hmul
    _ = q * qDerivative t q * deriv h q +
        q * imaginaryOrderK t q * h q -
          4 * t ^ 2 * imaginaryOrderK t q * h q / q := by
            field_simp [hq.ne']
            ring

/-- Finite-interval weak equation for the genuine K mode.  The endpoint
values of `h` vanish because its support lies in the open interval. -/
theorem actualK_weakBessel_on_compact_test (t : ℝ) (h : ℝ → ℝ)
    (hh : ContDiff ℝ 2 h) (_hcompact : HasCompactSupport h)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hsupp : tsupport h ⊆ Ioo a b) :
    (∫ q in a..b,
      q * qDerivative t q * deriv h q +
        q * imaginaryOrderK t q * h q) =
      4 * t ^ 2 *
        (∫ q in a..b, imaginaryOrderK t q * h q / q) := by
  have hK : ContinuousOn (imaginaryOrderK t) (Ioi 0) :=
    (imaginaryOrderK_differentiableOn_q t).continuousOn
  have hD : ContinuousOn (qDerivative t) (Ioi 0) :=
    qDerivative_continuousOn t
  have htest : ContinuousOn h (Ioi 0) := hh.continuous.continuousOn
  have htestD : ContinuousOn (deriv h) (Ioi 0) :=
    (test_deriv_continuous h hh).continuousOn
  have hleftCont : ContinuousOn
      (fun q : ℝ => q * qDerivative t q * deriv h q +
        q * imaginaryOrderK t q * h q) (Ioi 0) :=
    ((continuousOn_id.mul hD).mul htestD).add
      ((continuousOn_id.mul hK).mul htest)
  have hrightCont : ContinuousOn
      (fun q : ℝ => 4 * t ^ 2 * imaginaryOrderK t q * h q / q)
      (Ioi 0) :=
    ((continuousOn_const.mul hK).mul htest).div continuousOn_id
      (fun q hq => hq.ne')
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro q hq
    exact ha.trans_le hq.1
  have hleft : IntervalIntegrable
      (fun q : ℝ => q * qDerivative t q * deriv h q +
        q * imaginaryOrderK t q * h q) volume a b :=
    (hleftCont.mono hsub).intervalIntegrable_of_Icc hab.le
  have hright : IntervalIntegrable
      (fun q : ℝ => 4 * t ^ 2 * imaginaryOrderK t q * h q / q)
      volume a b :=
    (hrightCont.mono hsub).intervalIntegrable_of_Icc hab.le
  have hmass : IntervalIntegrable
      (fun q : ℝ => imaginaryOrderK t q * h q / q)
      volume a b := by
    have hc : ContinuousOn
        (fun q : ℝ => imaginaryOrderK t q * h q / q) (Ioi 0) :=
      (hK.mul htest).div continuousOn_id (fun q hq => hq.ne')
    exact (hc.mono hsub).intervalIntegrable_of_Icc hab.le
  have hd : ∀ q ∈ uIcc a b,
      HasDerivAt (kTestFlux t h)
        (q * qDerivative t q * deriv h q +
          q * imaginaryOrderK t q * h q -
            4 * t ^ 2 * imaginaryOrderK t q * h q / q) q := by
    intro q hq
    have hqI : q ∈ Icc a b := by
      simpa only [uIcc_of_le hab.le] using hq
    exact kTestFlux_hasDerivAt t h hh (ha.trans_le hqI.1)
  have hFTC :
      (∫ q in a..b,
        (q * qDerivative t q * deriv h q +
          q * imaginaryOrderK t q * h q) -
            4 * t ^ 2 * imaginaryOrderK t q * h q / q) =
        kTestFlux t h b - kTestFlux t h a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hleft.sub hright)
  have haz : h a = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (lt_irrefl a) (hsupp hmem).1
  have hbz : h b = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact (lt_irrefl b) (hsupp hmem).2
  rw [intervalIntegral.integral_sub hleft hright] at hFTC
  simp only [kTestFlux, haz, hbz, mul_zero, sub_self] at hFTC
  have hscale :
      (∫ q in a..b,
        4 * t ^ 2 * imaginaryOrderK t q * h q / q) =
      4 * t ^ 2 *
        (∫ q in a..b, imaginaryOrderK t q * h q / q) := by
    calc
      (∫ q in a..b,
        4 * t ^ 2 * imaginaryOrderK t q * h q / q) =
          ∫ q in a..b,
            (4 * t ^ 2) * (imaginaryOrderK t q * h q / q) := by
              apply intervalIntegral.integral_congr
              intro q
              ring
      _ = _ := intervalIntegral.integral_const_mul
  rw [hscale] at hFTC
  -- `hmass` records integrability of the unscaled `dq/q` pairing as well.
  linear_combination hFTC

end

end ImbalancedChen.Part3.ActualKWeakBesselTest20261024zz
