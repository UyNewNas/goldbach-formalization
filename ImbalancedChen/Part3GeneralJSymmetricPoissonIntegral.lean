import ImbalancedChen.Part3GeneralJBetaPoissonIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
The actual symmetric [-1,1] exponential Poisson integral for general J.
The square substitution is proved using monotone change of variables,
including integrability transfer from the genuine Beta weight. Reflection
then pairs the exponential phases into twice the cosine. No endpoint
integrability, substitution formula, or representation is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Set Filter MeasureTheory intervalIntegral

namespace ImbalancedChen.Part3.GeneralJSymmetricPoissonIntegralSourceOnly

open ActualGeneralJBesselSourceOnly GeneralJBetaPoissonIntegralSourceOnly

def jSymmetricPoissonWeight (nu : ℂ) (t : ℝ) : ℂ :=
  (1 - (t : ℂ) ^ (2 : ℕ)) ^ (nu - 1 / 2)

def jSymmetricPoissonIntegrand (nu : ℂ) (q t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) * jSymmetricPoissonWeight nu t

def jSymmetricPoissonIntegral (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, jSymmetricPoissonIntegrand nu q t

private theorem square_derivative (t : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (2 : ℕ)) (2 * t) t := by
  convert (hasDerivAt_id t).pow 2 using 1 <;> ring

private theorem square_derivative_nonneg (t : ℝ)
    (ht : t ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) : 0 ≤ 2 * t := by
  have ht0 : 0 < t := by simpa using ht.1
  exact mul_nonneg (by norm_num) ht0.le

theorem jPoisson_square_weight_jacobian (nu : ℂ) {t : ℝ} (ht : 0 < t) :
    (2 * t : ℝ) • jPoissonWeight nu (t ^ (2 : ℕ)) =
      (2 : ℂ) * jSymmetricPoissonWeight nu t := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hc := Complex.cpow_mul_ofReal_nonneg ht.le (2 : ℝ) ((1 / 2 : ℂ) - 1)
  have he : (2 : ℂ) * ((1 / 2 : ℂ) - 1) = -1 := by ring
  rw [Complex.ofReal_ofNat, Real.rpow_two, he, Complex.cpow_neg_one] at hc
  have hhalf : ((t ^ (2 : ℕ) : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) = (t : ℂ)⁻¹ := hc.symm
  have hexp : (nu + 1 / 2) - 1 = nu - 1 / 2 := by ring
  dsimp [jPoissonWeight, jSymmetricPoissonWeight]
  rw [hhalf, hexp, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  field_simp [htC]
  <;> ring

theorem jSymmetricPoissonWeight_even (nu : ℂ) (t : ℝ) :
    jSymmetricPoissonWeight nu (-t) = jSymmetricPoissonWeight nu t := by
  simp only [jSymmetricPoissonWeight, Complex.ofReal_neg, neg_sq]

/-- Endpoint integrability on [0,1] is a consequence of the actual Beta
weight and the square-map Jacobian; it is not a separate input. -/
theorem jSymmetricPoissonWeight_integrable_positive {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) :
    IntervalIntegrable (jSymmetricPoissonWeight nu) volume 0 1 := by
  have hchange := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (f := fun t : ℝ => t ^ (2 : ℕ)) (f' := fun t : ℝ => 2 * t)
    (g := jPoissonWeight nu) (a := 0) (b := 1)
    (by fun_prop) (fun t _ => square_derivative t) square_derivative_nonneg
  have hjac : IntervalIntegrable
      (fun t : ℝ => (2 * t : ℝ) • jPoissonWeight nu (t ^ (2 : ℕ))) volume 0 1 := by
    apply hchange.mpr
    simpa using jPoissonWeight_intervalIntegrable hnu
  have htwo : IntervalIntegrable
      (fun t : ℝ => (2 : ℂ) * jSymmetricPoissonWeight nu t) volume 0 1 := by
    apply hjac.congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num)] at ht
    exact jPoisson_square_weight_jacobian nu ht.1
  have hscaled := htwo.const_mul (1 / 2 : ℂ)
  have heq : (fun t : ℝ => (1 / 2 : ℂ) * ((2 : ℂ) * jSymmetricPoissonWeight nu t)) =
      jSymmetricPoissonWeight nu := by funext t; ring
  rw [heq] at hscaled
  exact hscaled

theorem jSymmetricPoissonWeight_integrable {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) :
    IntervalIntegrable (jSymmetricPoissonWeight nu) volume (-1) 1 := by
  have hp := jSymmetricPoissonWeight_integrable_positive hnu
  have hn := (IntervalIntegrable.iff_comp_neg (f := jSymmetricPoissonWeight nu)
    (a := (0 : ℝ)) (b := 1)).mp hp
  have hleft : IntervalIntegrable (jSymmetricPoissonWeight nu) volume (-1) 0 := by
    simpa only [neg_zero, jSymmetricPoissonWeight_even] using hn.symm
  exact hleft.trans hp

theorem jSymmetricPoissonIntegrand_integrable {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (q : ℝ) :
    IntervalIntegrable (jSymmetricPoissonIntegrand nu q) volume (-1) 1 :=
  (jSymmetricPoissonWeight_integrable hnu).continuousOn_mul (by fun_prop)

/-- The actual x=t² substitution. It remains valid for totalized interval
integrals; the endpoint-integrable regime is established separately above. -/
theorem jBetaPoissonIntegral_eq_twice_cosine (nu : ℂ) (q : ℝ) :
    jBetaPoissonIntegral nu q = (2 : ℂ) *
      ∫ t in (0 : ℝ)..1, Complex.cos ((q : ℂ) * (t : ℂ)) * jSymmetricPoissonWeight nu t := by
  have hchange := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (f := fun t : ℝ => t ^ (2 : ℕ)) (f' := fun t : ℝ => 2 * t)
    (g := fun x : ℝ => Complex.cos ((q : ℂ) * (Real.sqrt x : ℂ)) * jPoissonWeight nu x)
    (a := 0) (b := 1) (by fun_prop)
    (fun t _ => square_derivative t) square_derivative_nonneg
  have hchange' : (∫ t in (0 : ℝ)..1, (2 * t : ℝ) •
      (Complex.cos ((q : ℂ) * (Real.sqrt (t ^ (2 : ℕ)) : ℂ)) *
        jPoissonWeight nu (t ^ (2 : ℕ)))) = jBetaPoissonIntegral nu q := by
    simpa only [Function.comp_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      one_pow, jBetaPoissonIntegral] using hchange
  calc
    jBetaPoissonIntegral nu q = ∫ t in (0 : ℝ)..1, (2 * t : ℝ) •
        (Complex.cos ((q : ℂ) * (Real.sqrt (t ^ (2 : ℕ)) : ℂ)) *
          jPoissonWeight nu (t ^ (2 : ℕ))) := hchange'.symm
    _ = ∫ t in (0 : ℝ)..1, (2 : ℂ) *
        (Complex.cos ((q : ℂ) * (t : ℂ)) * jSymmetricPoissonWeight nu t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      rw [Real.sqrt_sq_eq_abs, abs_of_pos ht.1]
      have hj := jPoisson_square_weight_jacobian nu ht.1
      simp only [Complex.real_smul] at hj ⊢
      calc
        _ = Complex.cos ((q : ℂ) * (t : ℂ)) *
            (((2 * t : ℝ) : ℂ) * jPoissonWeight nu (t ^ (2 : ℕ))) := by ring
        _ = _ := by rw [hj]; ring
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem jSymmetricPoisson_phase_pair (nu : ℂ) (q t : ℝ) :
    jSymmetricPoissonIntegrand nu q (-t) + jSymmetricPoissonIntegrand nu q t =
      (2 : ℂ) * (Complex.cos ((q : ℂ) * (t : ℂ)) * jSymmetricPoissonWeight nu t) := by
  have hpos : Complex.I * (q : ℂ) * (t : ℂ) = ((q : ℂ) * (t : ℂ)) * Complex.I := by ring
  have hneg : Complex.I * (q : ℂ) * ((-t : ℝ) : ℂ) =
      (-((q : ℂ) * (t : ℂ))) * Complex.I := by push_cast; ring
  dsimp only [jSymmetricPoissonIntegrand]
  rw [hneg, hpos, jSymmetricPoissonWeight_even]
  calc
    _ = (Complex.exp (((q : ℂ) * (t : ℂ)) * Complex.I) +
        Complex.exp ((-((q : ℂ) * (t : ℂ))) * Complex.I)) *
          jSymmetricPoissonWeight nu t := by ring
    _ = _ := by rw [← Complex.two_cos]; ring

/-- Reflection cancels the odd phase, with all integrability obligations
discharged from the Beta integral rather than supplied by a caller. -/
theorem jSymmetricPoissonIntegral_eq_twice_cosine {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) (q : ℝ) :
    jSymmetricPoissonIntegral nu q = (2 : ℂ) *
      ∫ t in (0 : ℝ)..1, Complex.cos ((q : ℂ) * (t : ℂ)) * jSymmetricPoissonWeight nu t := by
  have hw := jSymmetricPoissonWeight_integrable_positive hnu
  have hp : IntervalIntegrable (jSymmetricPoissonIntegrand nu q) volume 0 1 :=
    hw.continuousOn_mul (by fun_prop)
  have hm : IntervalIntegrable (fun t : ℝ => jSymmetricPoissonIntegrand nu q (-t))
      volume 0 1 := by
    have heq : (fun t : ℝ => jSymmetricPoissonIntegrand nu q (-t)) =
        (fun t : ℝ => Complex.exp (Complex.I * (q : ℂ) * ((-t : ℝ) : ℂ)) *
          jSymmetricPoissonWeight nu t) := by
      funext t
      simp only [jSymmetricPoissonIntegrand, jSymmetricPoissonWeight_even]
    rw [heq]
    exact hw.continuousOn_mul (by fun_prop)
  have hl : IntervalIntegrable (jSymmetricPoissonIntegrand nu q) volume (-1) 0 := by
    have h := (IntervalIntegrable.iff_comp_neg
      (f := fun t : ℝ => jSymmetricPoissonIntegrand nu q (-t))
      (a := (0 : ℝ)) (b := 1)).mp hm
    simpa only [neg_zero, neg_neg] using h.symm
  have href : (∫ t in (-1 : ℝ)..0, jSymmetricPoissonIntegrand nu q t) =
      ∫ t in (0 : ℝ)..1, jSymmetricPoissonIntegrand nu q (-t) := by
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg
      (f := jSymmetricPoissonIntegrand nu q) (a := (0 : ℝ)) (b := 1)).symm
  unfold jSymmetricPoissonIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hp, href,
    ← intervalIntegral.integral_add hm hp]
  simp_rw [jSymmetricPoisson_phase_pair]
  exact intervalIntegral.integral_const_mul _ _

theorem jSymmetricPoissonIntegral_eq_beta {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re)
    (q : ℝ) : jSymmetricPoissonIntegral nu q = jBetaPoissonIntegral nu q := by
  rw [jSymmetricPoissonIntegral_eq_twice_cosine hnu q,
    jBetaPoissonIntegral_eq_twice_cosine]

/-- Literal symmetric exponential Poisson--Schläfli representation for the
actual general complex-order J, with the exact Gamma/sqrt(pi) normalization. -/
theorem generalJ_eq_symmetric_poisson_integral {nu : ℂ}
    (hnu : -(1 / 2 : ℝ) < nu.re) {q : ℝ} (hq : 0 < q) :
    generalJ nu q = (((q / 2 : ℝ) : ℂ) ^ nu) /
      ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) *
        ∫ t in (-1 : ℝ)..1,
          Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
            (1 - (t : ℂ) ^ (2 : ℕ)) ^ (nu - 1 / 2) := by
  change generalJ nu q = (((q / 2 : ℝ) : ℂ) ^ nu) /
    ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)) * jSymmetricPoissonIntegral nu q
  rw [jSymmetricPoissonIntegral_eq_beta hnu q]
  exact generalJ_eq_betaPoissonIntegral hnu hq

end ImbalancedChen.Part3.GeneralJSymmetricPoissonIntegralSourceOnly
