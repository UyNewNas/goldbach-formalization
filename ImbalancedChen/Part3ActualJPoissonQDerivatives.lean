import ImbalancedChen.Part3GeneralJSymmetricPoissonIntegral
import ImbalancedChen.Part3JBesselPoissonEvenMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Genuine q differentiation under the actual symmetric J Poisson integral.
Every finite q moment has the same actual integrable weight majorant,
since |t|<=1 and the phase exp(i*q*t) has norm one for real q. Thus the
moment derivative is the next literal (i*t) moment, with no order increase.

The existing literal generalJ Poisson formula is consumed, not reproved.
Differentiating its positive-q principal prefactor and the actual integral
then identifies the native derivative of the original generalJ series.
No derivative-under-integral, integrability or J representation premise is
supplied, and the existing series Bessel ODE is not repeated.
-/

namespace ImbalancedChen.Part3.ActualJPoissonQDerivatives20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a

def jPoissonMomentIntegrand (k : ℕ) (ν : ℂ) (q t : ℝ) : ℂ :=
  (Complex.I * (t : ℂ)) ^ k * jSymmetricPoissonIntegrand ν q t

def jPoissonMoment (k : ℕ) (ν : ℂ) (q : ℝ) : ℂ :=
  ∫ t in Ioo (-1 : ℝ) 1, jPoissonMomentIntegrand k ν q t

def jPoissonPrefactor (ν : ℂ) (q : ℝ) : ℂ :=
  (((q / 2 : ℝ) : ℂ) ^ ν) / ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2))

private theorem symmetricWeight_eq (ν : ℂ) (t : ℝ) :
    jSymmetricPoissonWeight ν t = poissonWeight ν t := by
  simp only [jSymmetricPoissonWeight, poissonWeight, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow]

private theorem weight_integrable {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) :
    IntegrableOn (jSymmetricPoissonWeight ν) (Ioo (-1 : ℝ) 1) := by
  simpa only [symmetricWeight_eq] using poissonWeight_integrable hν

private theorem phase_norm_one (q t : ℝ) :
    ‖Complex.exp (Complex.I * (q : ℂ) * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- One actual weight dominates every finite q moment, uniformly in real q. -/
theorem jPoissonMomentIntegrand_norm_le (k : ℕ) (ν : ℂ) (q : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖jPoissonMomentIntegrand k ν q t‖ ≤ ‖jSymmetricPoissonWeight ν t‖ := by
  have hp : |t| ^ k ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) (abs_lt.mpr ht).le k
  simp only [jPoissonMomentIntegrand, jSymmetricPoissonIntegrand, norm_mul,
    norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
    phase_norm_one]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
    (norm_nonneg (jSymmetricPoissonWeight ν t))

theorem jPoissonMoment_integrable (k : ℕ) {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (q : ℝ) :
    IntegrableOn (jPoissonMomentIntegrand k ν q) (Ioo (-1 : ℝ) 1) := by
  have hc : Continuous (fun t : ℝ => (Complex.I * (t : ℂ)) ^ k *
      Complex.exp (Complex.I * (q : ℂ) * (t : ℂ))) := by fun_prop
  have hbase := (weight_integrable hν).bdd_mul hc.aestronglyMeasurable
    (c := (1 : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hp : |t| ^ k ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) (abs_lt.mpr ht).le k
      simpa only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, one_mul, phase_norm_one, mul_one] using hp)
  simpa only [jPoissonMomentIntegrand, jSymmetricPoissonIntegrand, mul_assoc] using hbase

theorem jPoissonMomentIntegrand_hasDerivAt (k : ℕ) (ν : ℂ) (q t : ℝ) :
    HasDerivAt (fun x : ℝ => jPoissonMomentIntegrand k ν x t)
      (jPoissonMomentIntegrand (k + 1) ν q t) q := by
  have hp : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ) * (t : ℂ))
      (Complex.I * (t : ℂ)) q := by
    simpa using (((hasDerivAt_id q).ofReal_comp.const_mul Complex.I).mul_const (t : ℂ))
  have h := (hp.cexp.const_mul ((Complex.I * (t : ℂ)) ^ k)).mul_const
    (jSymmetricPoissonWeight ν t)
  convert h using 1 <;>
    dsimp only [jPoissonMomentIntegrand, jSymmetricPoissonIntegrand] <;>
    simp only [pow_succ] <;> ring

/-- Genuine dominated q differentiation on the entire real q-line. -/
theorem jPoissonMoment_hasDerivAt (k : ℕ) {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (q : ℝ) :
    HasDerivAt (jPoissonMoment k ν) (jPoissonMoment (k + 1) ν q) q := by
  have hmeas : ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (jPoissonMomentIntegrand k ν x)
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    Eventually.of_forall (fun x => (jPoissonMoment_integrable k hν x).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable (jPoissonMomentIntegrand (k + 1) ν q)
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    (jPoissonMoment_integrable (k + 1) hν q).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ x ∈ (univ : Set ℝ),
      ‖jPoissonMomentIntegrand (k + 1) ν x t‖ ≤ ‖jSymmetricPoissonWeight ν t‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact fun x _ => jPoissonMomentIntegrand_norm_le (k + 1) ν x ht
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ x ∈ (univ : Set ℝ),
      HasDerivAt (fun y : ℝ => jPoissonMomentIntegrand k ν y t)
        (jPoissonMomentIntegrand (k + 1) ν x t) x :=
    Eventually.of_forall (fun t x _ => jPoissonMomentIntegrand_hasDerivAt k ν x t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun x t => jPoissonMomentIntegrand k ν x t)
    (F' := fun x t => jPoissonMomentIntegrand (k + 1) ν x t)
    (bound := fun t => ‖jSymmetricPoissonWeight ν t‖)
    (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 q) hmeas
    (jPoissonMoment_integrable k hν q) hmeas' hbound (weight_integrable hν).norm hdiff).2

theorem deriv_jPoissonMoment (k : ℕ) {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (q : ℝ) :
    deriv (jPoissonMoment k ν) q = jPoissonMoment (k + 1) ν q :=
  (jPoissonMoment_hasDerivAt k hν q).deriv

theorem jPoissonMoment_norm_bound (k : ℕ) {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re) (q : ℝ) :
    ‖jPoissonMoment k ν q‖ ≤ ∫ t in Ioo (-1 : ℝ) 1, ‖jSymmetricPoissonWeight ν t‖ := by
  apply norm_integral_le_of_norm_le (weight_integrable hν).norm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact jPoissonMomentIntegrand_norm_le k ν q ht

theorem jPoissonMoment_eq_interval (k : ℕ) (ν : ℂ) (q : ℝ) :
    jPoissonMoment k ν q = ∫ t in (-1 : ℝ)..1,
      (Complex.I * (t : ℂ)) ^ k * Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
        jSymmetricPoissonWeight ν t := by
  rw [jPoissonMoment, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    dsimp only [jPoissonMomentIntegrand, jSymmetricPoissonIntegrand]
    ring)

theorem jPoissonMoment_zero (ν : ℂ) (q : ℝ) :
    jPoissonMoment 0 ν q = jSymmetricPoissonIntegral ν q := by
  rw [jPoissonMoment_eq_interval]
  simp only [pow_zero, one_mul, jSymmetricPoissonIntegral, jSymmetricPoissonIntegrand]

private theorem prefactor_hasDerivAt (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (jPoissonPrefactor ν)
      ((ν / (q : ℂ)) * jPoissonPrefactor ν q) q := by
  have hhalf : 0 < q / 2 := by positivity
  have hb : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hhalf.ne'
  have hs : ((q / 2 : ℝ) : ℂ) ∈ Complex.slitPlane := by simp [hhalf]
  have hp := (Complex.hasStrictDerivAt_cpow_const (c := ν) hs).hasDerivAt.comp_ofReal.scomp
    q ((hasDerivAt_id q).div_const 2)
  have hpower : HasDerivAt (fun x : ℝ => (((x / 2 : ℝ) : ℂ) ^ ν))
      ((ν / (q : ℂ)) * (((q / 2 : ℝ) : ℂ) ^ ν)) q := by
    convert hp using 1
    · funext x
      rfl
    · rw [Complex.cpow_sub _ _ hb, Complex.cpow_one]
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
      field_simp [Complex.ofReal_ne_zero.mpr hq.ne'] <;> ring
  have h := hpower.div_const ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2))
  convert h using 1 <;> dsimp only [jPoissonPrefactor] <;> ring

private theorem generalJ_eq_prefactor_moment {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    generalJ ν q = jPoissonPrefactor ν q * jPoissonMoment 0 ν q := by
  rw [jPoissonMoment_zero]
  exact generalJ_eq_symmetric_poisson_integral hν hq

/-- The original actual generalJ has this derivative, proved by actual
dominated Poisson differentiation rather than a derivative-supplier premise. -/
theorem generalJ_poisson_hasDerivAt {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (generalJ ν)
      ((ν / (q : ℂ)) * generalJ ν q + jPoissonPrefactor ν q * jPoissonMoment 1 ν q) q := by
  have hp := (prefactor_hasDerivAt ν hq).mul (jPoissonMoment_hasDerivAt 0 hν q)
  have hvalue : ((ν / (q : ℂ)) * jPoissonPrefactor ν q) * jPoissonMoment 0 ν q +
      jPoissonPrefactor ν q * jPoissonMoment (0 + 1) ν q =
      (ν / (q : ℂ)) * generalJ ν q + jPoissonPrefactor ν q * jPoissonMoment 1 ν q := by
    rw [generalJ_eq_prefactor_moment hν hq]
    ring
  have hd := hp.congr_deriv hvalue
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact generalJ_eq_prefactor_moment hν hx

/-- Exact native q derivative integral of the literal actual J series,
with the original complex order unchanged. -/
theorem deriv_generalJ_eq_poisson_integral {ν : ℂ} (hν : -(1 / 2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    deriv (generalJ ν) q = (ν / (q : ℂ)) * generalJ ν q +
      jPoissonPrefactor ν q * ∫ t in (-1 : ℝ)..1,
        (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
          (1 - (t : ℂ) ^ (2 : ℕ)) ^ (ν - 1 / 2) := by
  rw [(generalJ_poisson_hasDerivAt hν hq).deriv, jPoissonMoment_eq_interval]
  simp only [pow_one, jSymmetricPoissonWeight]

end
end ImbalancedChen.Part3.ActualJPoissonQDerivatives20261025a
