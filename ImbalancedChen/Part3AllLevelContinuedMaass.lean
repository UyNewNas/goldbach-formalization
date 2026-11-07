import ImbalancedChen.Part3FiniteCompletedOldformSpatial
import ImbalancedChen.Part3LevelOldformScatteringMoments
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-!
New all-level continuation mathematics, 2026-10-26.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED / ZERO FORMAL CREDIT.

The shared completedLevelOldform is the actual completion of the native
GammaInfinity\Gamma0(N) series on Re(s)>1. Its finite numerator is analytic
off the genuine completed parameter exceptions 0,1. The exact finite Euler
denominator is nonzero already on Re(s)>0. Thus the open critical strip is
a genuine regular parameter domain, including the central parameter.

Spatial C-infinity and the literal Maass equation follow through positive
dilation, actual second derivatives, and the finite oldform list. Native
Gamma0(N) invariance is extended from the initial series by the analytic
identity principle for the numerator. No spectral completeness, quotient
resolution, scattering unitarity, or removal of a residue pole is asserted.
-/

namespace ImbalancedChen.Part3.AllLevelContinuedMaass20261026a

noncomputable section

open Set Filter Topology Complex
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.FiniteCompletedOldformSpatial20261026a
open ImbalancedChen.Part3.ContinuedFourierNonconstantMaass
open ImbalancedChen.Part3.ContinuedFourierSpatialContDiffTwo
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a

private def listValue (T : List (ℕ+ × ℂ)) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (T.map (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum

private theorem listValue_raise (p : PrimeIndex) (T : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    listValue (T.map (fun t => (primePNat p * t.1, t.2))) s z =
      listValue T s (pnatDilate (primePNat p) z) := by
  induction T with
  | nil => simp [listValue]
  | cons t T ih =>
      simp only [listValue, List.map_cons, List.sum_cons, pnatDilate_mul] at ih ⊢
      rw [ih]

private theorem listValue_scale (a : ℂ) (T : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    listValue (T.map (fun t => (t.1, a * t.2))) s z = a * listValue T s z := by
  induction T with
  | nil => simp [listValue]
  | cons t T ih =>
      simp only [listValue, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

private theorem listValue_oldform_cons (p : PrimeIndex) (L : List PrimeIndex)
    (s : ℂ) (z : UpperHalfPlane) :
    listValue (oldformTerms (p :: L) s) s z =
      if p.1 ∣ primeProduct L then
        listValue (oldformTerms L s) s (pnatDilate (primePNat p) z)
      else listValue (oldformTerms L s) s (pnatDilate (primePNat p) z) -
        (p.1 : ℂ) ^ (-s) * listValue (oldformTerms L s) s z := by
  unfold oldformTerms
  split_ifs
  · exact listValue_raise p _ s z
  · rw [show listValue
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z =
          listValue ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) s z +
            listValue ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z by
        simp only [listValue, List.map_append, List.sum_append]]
    rw [listValue_raise, listValue_scale]
    ring

private theorem fixedBasePower_analyticAt (a : ℂ) (ha : a ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => a ^ w) s := by
  have h : AnalyticAt ℂ (fun w : ℂ => Complex.exp (w * Complex.log a)) s :=
    (analyticAt_id.mul_const (Complex.log a)).cexp
  convert h using 1
  funext w
  simp only [Complex.cpow_def_of_ne_zero ha, mul_comm]

theorem oldformNormalization_analyticAt (L : List PrimeIndex) (s : ℂ) :
    AnalyticAt ℂ (oldformNormalization L) s := by
  induction L with
  | nil => exact analyticAt_const
  | cons p L ih =>
      have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
      have hp := fixedBasePower_analyticAt (p.1 : ℂ) hp0 s
      have hn : AnalyticAt ℂ (fun w : ℂ => (p.1 : ℂ) ^ (-w)) s :=
        (fixedBasePower_analyticAt (p.1 : ℂ) hp0 (-s)).comp analyticAt_id.neg
      by_cases hd : p.1 ∣ primeProduct L
      · simpa only [oldformNormalization, if_pos hd] using hp.mul ih
      · simpa only [oldformNormalization, if_neg hd] using (hp.sub hn).mul ih

private theorem listValue_oldform_analyticAt (L : List PrimeIndex)
    (z : UpperHalfPlane) (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    AnalyticAt ℂ (fun w => listValue (oldformTerms L w) w z) s := by
  induction L generalizing z with
  | nil =>
      simpa only [oldformTerms, listValue, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, one_mul, add_zero, pnatDilate_one] using
        completedActualEisenstein_analyticOnNhd z s (by simpa using And.intro hs0 hs1)
  | cons p L ih =>
      have hp0 : (p.1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.2.ne_zero
      have hn : AnalyticAt ℂ (fun w : ℂ => (p.1 : ℂ) ^ (-w)) s :=
        (fixedBasePower_analyticAt (p.1 : ℂ) hp0 (-s)).comp analyticAt_id.neg
      by_cases hd : p.1 ∣ primeProduct L
      · simpa only [listValue_oldform_cons, if_pos hd] using ih (pnatDilate (primePNat p) z)
      · simpa only [listValue_oldform_cons, if_neg hd] using
          (ih (pnatDilate (primePNat p) z)).sub (hn.mul (ih z))

theorem completedOldformNumerator_analyticOnNhd (N : ℕ) (z : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => completedOldformNumerator N s z) ({0, 1} : Set ℂ)ᶜ := by
  intro s hs
  have hs' : s ≠ 0 ∧ s ≠ 1 := by simpa using hs
  exact listValue_oldform_analyticAt (canonicalPrimeList N) z s hs'.1 hs'.2

/-- Exact finite Euler denominator and the completed residue exceptions remain visible. -/
def completedRegularDomain (N : ℕ) : Set ℂ :=
  {s | s ≠ 0 ∧ s ≠ 1 ∧ oldformNormalization (canonicalPrimeList N) s ≠ 0}

theorem completedLevelOldform_analyticOnNhd (N : ℕ) (z : UpperHalfPlane) :
    AnalyticOnNhd ℂ (fun s => completedLevelOldform N s z) (completedRegularDomain N) := by
  intro s hs
  exact (completedOldformNumerator_analyticOnNhd N z s
    (by simpa using And.intro hs.1 hs.2.1)).div
      (oldformNormalization_analyticAt (canonicalPrimeList N) s) hs.2.2

/-- The whole open critical strip is a regular domain for the COMPLETED continuation. -/
theorem criticalStrip_subset_completedRegularDomain (N : ℕ) :
    {s : ℂ | 0 < s.re ∧ s.re < 1} ⊆ completedRegularDomain N := by
  intro s hs
  refine ⟨?_, ?_, oldformNormalization_ne_zero_of_re_pos _ s hs.1⟩
  · intro h
    subst s
    simpa using hs.1
  · intro h
    subst s
    simpa using hs.2

theorem criticalParameter_mem_completedRegularDomain (N : ℕ) (t : ℝ) :
    criticalParameter t ∈ completedRegularDomain N := by
  apply criticalStrip_subset_completedRegularDomain N
  rw [criticalParameter_re]
  norm_num

/-- In particular every point of the critical line has a genuine analytic
parameter neighborhood, including its central point. -/
theorem completedLevelOldform_analyticAt_critical (N : ℕ) (t : ℝ) (z : UpperHalfPlane) :
    AnalyticAt ℂ (fun s => completedLevelOldform N s z) (criticalParameter t) :=
  completedLevelOldform_analyticOnNhd N z _ (criticalParameter_mem_completedRegularDomain N t)

private theorem poleExcluded_isPreconnected : IsPreconnected (({0, 1} : Set ℂ)ᶜ) := by
  have hc : ({0, 1} : Set ℂ).Countable := (Set.finite_pair 0 1).countable
  have hr : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  exact (Set.Countable.isConnected_compl_of_one_lt_rank hr hc).isPreconnected

/-- Native congruence-group automorphy of the numerator is a conclusion of
the initial actual series and the analytic identity principle. -/
theorem completedOldformNumerator_Gamma0_invariant (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    completedOldformNumerator N s ((gamma : SL(2, ℤ)) • z) =
      completedOldformNumerator N s z := by
  have he : (fun w => completedOldformNumerator N w ((gamma : SL(2, ℤ)) • z))
      =ᶠ[𝓝 (2 : ℂ)] (fun w => completedOldformNumerator N w z) := by
    have hhalf : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hhalf] with w hw
    rw [completedOldformNumerator_eq_initial N hN w hw,
      completedOldformNumerator_eq_initial N hN w hw,
      levelPrimitiveComplexEisenstein_Gamma0_invariant N w hw gamma z]
  have htwo : (2 : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by norm_num
  have hall := (completedOldformNumerator_analyticOnNhd N ((gamma : SL(2, ℤ)) • z))
    .eqOn_of_preconnected_of_eventuallyEq (completedOldformNumerator_analyticOnNhd N z)
      poleExcluded_isPreconnected htwo he
  exact hall (by simpa using And.intro hs0 hs1)

theorem completedLevelOldform_Gamma0_invariant (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s ∈ completedRegularDomain N)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    completedLevelOldform N s ((gamma : SL(2, ℤ)) • z) = completedLevelOldform N s z := by
  unfold completedLevelOldform
  rw [completedOldformNumerator_Gamma0_invariant N hN s hs.1 hs.2.1 gamma z]

/-- A genuine two-variable positive-height chart of the shared native continuation. -/
def completedLevelChart (N : ℕ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  completedTermsChart (oldformTerms (canonicalPrimeList N) s) s p /
    oldformNormalization (canonicalPrimeList N) s

theorem completedLevelChart_eq_native (N : ℕ) (s : ℂ) (z : UpperHalfPlane) :
    completedLevelChart N s (z.re, z.im) = completedLevelOldform N s z := by
  rw [completedLevelChart, completedTermsChart_eq_native]
  rfl

theorem completedLevelChart_smooth (N : ℕ) (s : ℂ) : SpatialSmooth (completedLevelChart N s) :=
  (completedTermsChart_smooth (oldformTerms (canonicalPrimeList N) s) s).div_const _

theorem completedLevelChart_maass (N : ℕ) (s : ℂ) (hs : s ∈ completedRegularDomain N)
    (x y : ℝ) (hy : 0 < y) :
    maassLaplacian (completedLevelChart N s) x y =
      s * (1 - s) * completedLevelChart N s (x, y) := by
  have he : completedLevelChart N s = fun p =>
      (oldformNormalization (canonicalPrimeList N) s)⁻¹ *
        completedTermsChart (oldformTerms (canonicalPrimeList N) s) s p := by
    funext p
    simp only [completedLevelChart, div_eq_mul_inv, mul_comm]
  rw [he, maassLaplacian_const_mul,
    completedTermsChart_maass _ s hs.1 hs.2.1 x y hy]
  ring

theorem completedLevelOldform_maass (N : ℕ) (s : ℂ) (hs : s ∈ completedRegularDomain N)
    (z : UpperHalfPlane) :
    maassLaplacian (completedLevelChart N s) z.re z.im =
      s * (1 - s) * completedLevelOldform N s z := by
  rw [completedLevelChart_maass N s hs z.re z.im z.im_pos,
    completedLevelChart_eq_native]

/-- Spatial smoothness of the actual native function in a global real chart. -/
theorem completedLevelOldform_logHeight_smooth (N : ℕ) (s : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => completedLevelOldform N s
      (ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic.horizontalPoint
        (Real.exp p.2) (Real.exp_pos p.2) p.1)) := by
  have hm : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1, Real.exp p.2)) := by fun_prop
  have h : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => completedLevelChart N s (p.1, Real.exp p.2)) univ :=
    (completedLevelChart_smooth N s).comp hm.contDiffOn (fun p hp => Real.exp_pos p.2)
  have he : (fun p : ℝ × ℝ => completedLevelOldform N s
      (ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic.horizontalPoint
        (Real.exp p.2) (Real.exp_pos p.2) p.1)) =
      (fun p : ℝ × ℝ => completedLevelChart N s (p.1, Real.exp p.2)) := by
    funext p
    exact (completedLevelChart_eq_native N s _).symm
  rw [he]
  exact contDiffOn_univ.mp h

/-- The genuine analytic-limit central constant is retained by every dilation. -/
theorem completedLevelOldform_maass_center (N : ℕ) (z : UpperHalfPlane) :
    maassLaplacian (completedLevelChart N (1 / 2)) z.re z.im =
      (1 / 4 : ℂ) * completedLevelOldform N (1 / 2) z := by
  have hs : (1 / 2 : ℂ) ∈ completedRegularDomain N :=
    criticalStrip_subset_completedRegularDomain N (by norm_num)
  convert completedLevelOldform_maass N (1 / 2) hs z using 1 <;> norm_num

theorem completedLevelOldform_maass_critical (N : ℕ) (t : ℝ) (z : UpperHalfPlane) :
    maassLaplacian (completedLevelChart N (criticalParameter t)) z.re z.im =
      ((1 / 4 : ℝ) + t ^ 2 : ℂ) * completedLevelOldform N (criticalParameter t) z := by
  have he : criticalParameter t * (1 - criticalParameter t) =
      ((1 / 4 : ℝ) + t ^ 2 : ℂ) := by
    unfold criticalParameter
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [completedLevelOldform_maass N _ (criticalParameter_mem_completedRegularDomain N t), he]

/-- Uncompleted normalization is restricted to its actual nonzero completion
factor. This does not claim to remove the pole or zero of that scalar. -/
def physicalRegularDomain (N : ℕ) : Set ℂ :=
  {s | s ∈ completedRegularDomain N ∧ completionFactor s ≠ 0}

def continuedLevelEisenstein (N : ℕ) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  completedLevelOldform N s z / completionFactor s

theorem completionFactor_ne_zero_initial (s : ℂ) (hs : 1 < s.re) :
    completionFactor s ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero
      (Complex.cpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  · apply riemannZeta_ne_zero_of_one_lt_re
    simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
    linarith

theorem continuedLevelEisenstein_eq_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (z : UpperHalfPlane) :
    continuedLevelEisenstein N s z = levelPrimitiveComplexEisenstein N s z := by
  rw [continuedLevelEisenstein, completedLevelOldform_eq_initial N hN s hs z]
  exact mul_div_cancel_left₀ _ (completionFactor_ne_zero_initial s hs)

theorem continuedLevelEisenstein_Gamma0_invariant (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s ∈ physicalRegularDomain N)
    (gamma : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    continuedLevelEisenstein N s ((gamma : SL(2, ℤ)) • z) = continuedLevelEisenstein N s z := by
  unfold continuedLevelEisenstein
  rw [completedLevelOldform_Gamma0_invariant N hN s hs.1 gamma z]

theorem continuedLevelEisenstein_logHeight_smooth (N : ℕ) (s : ℂ)
    (hs : s ∈ physicalRegularDomain N) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => continuedLevelEisenstein N s
      (ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic.horizontalPoint
        (Real.exp p.2) (Real.exp_pos p.2) p.1)) :=
  (completedLevelOldform_logHeight_smooth N s).div_const _

theorem continuedLevelEisenstein_maass (N : ℕ) (s : ℂ) (hs : s ∈ physicalRegularDomain N)
    (z : UpperHalfPlane) :
    maassLaplacian (fun p => completedLevelChart N s p / completionFactor s) z.re z.im =
      s * (1 - s) * continuedLevelEisenstein N s z := by
  have he : (fun p => completedLevelChart N s p / completionFactor s) =
      (fun p => (completionFactor s)⁻¹ * completedLevelChart N s p) := by
    funext p
    simp only [div_eq_mul_inv, mul_comm]
  rw [he, maassLaplacian_const_mul, completedLevelOldform_maass N s hs.1 z]
  simp only [continuedLevelEisenstein, div_eq_mul_inv]
  ring

end

end ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
