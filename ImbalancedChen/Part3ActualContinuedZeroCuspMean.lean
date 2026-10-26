import ImbalancedChen.Part3CompletedEisensteinIntegerMean
import ImbalancedChen.Part3AllLevelContinuedMaass

/-!
The genuine unit-period zero Fourier integral at the literal Fricke cusp
equals the computed finite reflected constant. Every complementary oldform
index is a positive integer, so the actual full-level K-series mean theorem
applies term by term. This retains the completed central value at s=1/2.
No zero-mode formula or scattering coefficient is a premise.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.
-/

noncomputable section
open Set Complex
open scoped UpperHalfPlane MatrixGroups BigOperators
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.LevelOldformFricke20261026a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.LevelPrimitiveComplexEisenstein
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a

namespace ImbalancedChen.Part3.ActualContinuedZeroCuspMean20261026a

theorem reflected_term_continuous (N : ℕ) (hN : 0 < N) (s : ℂ)
    (t : ℕ+ × ℂ) (ht : (t.1 : ℕ) ∣ N) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => t.2 *
      completedActualEisenstein s (reflectedDilation N hN t.1 (horizontalPoint y hy x))) := by
  simp_rw [reflectedDilation_eq_integer N hN t.1 ht]
  exact continuous_const.mul (completed_integer_dilation_continuous s
    (complementaryIndex N hN t.1 ht) y hy)

theorem reflected_term_mean (N : ℕ) (hN : 0 < N) (s : ℂ)
    (t : ℕ+ × ℂ) (ht : (t.1 : ℕ) ∣ N) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, t.2 *
      completedActualEisenstein s (reflectedDilation N hN t.1 (horizontalPoint y hy x))) =
        t.2 * completedConstant (((N : ℝ) / (t.1 : ℝ)) * y) s := by
  simp_rw [reflectedDilation_eq_integer N hN t.1 ht]
  rw [intervalIntegral.integral_const_mul,
    completed_integer_dilation_mean s (complementaryIndex N hN t.1 ht) y hy,
    complementaryIndex_real]

theorem reflected_list_continuous (N : ℕ) (hN : 0 < N) (s : ℂ)
    (T : List (ℕ+ × ℂ)) (hT : ∀ t ∈ T, (t.1 : ℕ) ∣ N) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => (T.map (fun t => t.2 *
      completedActualEisenstein s (reflectedDilation N hN t.1 (horizontalPoint y hy x)))).sum) := by
  induction T generalizing hT with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons t T ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (reflected_term_continuous N hN s t (hT t (by simp)) y hy).add
        (ih (fun w hw => hT w (List.mem_cons_of_mem _ hw)))

theorem reflected_list_mean (N : ℕ) (hN : 0 < N) (s : ℂ)
    (T : List (ℕ+ × ℂ)) (hT : ∀ t ∈ T, (t.1 : ℕ) ∣ N) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, (T.map (fun t => t.2 *
      completedActualEisenstein s (reflectedDilation N hN t.1 (horizontalPoint y hy x)))).sum) =
      (T.map (fun t => t.2 * completedConstant (((N : ℝ) / (t.1 : ℝ)) * y) s)).sum := by
  induction T generalizing hT with
  | nil => simp
  | cons t T ih =>
      have ht : (t.1 : ℕ) ∣ N := hT t (by simp)
      have hTail : ∀ w ∈ T, (w.1 : ℕ) ∣ N := fun w hw => hT w (List.mem_cons_of_mem _ hw)
      simp only [List.map_cons, List.sum_cons]
      rw [intervalIntegral.integral_add
        ((reflected_term_continuous N hN s t ht y hy).intervalIntegrable 0 1)
        ((reflected_list_continuous N hN s T hTail y hy).intervalIntegrable 0 1),
        reflected_term_mean N hN s t ht y hy, ih hTail]

/-- Physical zero-cusp mean of the actual completed continuation in its
regular domain. The domain includes the ENTIRE critical line. -/
theorem completed_zeroCusp_mean (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s ∈ completedRegularDomain N) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      completedLevelOldform N s (frickeSL N hN • horizontalPoint y hy x)) =
        completedReflectedConstant N s y := by
  simp_rw [completedLevelOldform_fricke N hN s hs.1 hs.2.1]
  unfold reflectedCompletedLevel reflectedCompletedNumerator completedReflectedConstant
  rw [intervalIntegral.integral_div,
    reflected_list_mean N hN s _ (canonical_oldform_index_dvd N hN s) y hy]

theorem completed_zeroCusp_trace_continuous (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : s ∈ completedRegularDomain N) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ =>
      completedLevelOldform N s (frickeSL N hN • horizontalPoint y hy x)) := by
  simp_rw [completedLevelOldform_fricke N hN s hs.1 hs.2.1]
  exact (reflected_list_continuous N hN s _
    (canonical_oldform_index_dvd N hN s) y hy).div_const _

/-- Exact Euler expression for the genuine zero-cusp Fourier integral;
the central parameter is excluded ONLY from this raw two-Lambda display. -/
theorem completed_zeroCusp_mean_eq_euler (N : ℕ) (hN : 1 < N)
    (s : ℂ) (hs : s ∈ completedRegularDomain N) (hhalf : s ≠ 1 / 2)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, completedLevelOldform N s
      (frickeSL N (lt_trans Nat.zero_lt_one hN) • horizontalPoint y hy x)) =
      completedRiemannZeta (2 * s - 1) * (y : ℂ) ^ (1 - s) *
        ((N : ℂ) ^ (-s) * ∏ p ∈ (canonicalPrimeList N).toFinset,
          ((1 - (p.1 : ℂ) ^ (1 - 2 * s)) / (1 - (p.1 : ℂ) ^ (-2 * s)))) := by
  rw [completed_zeroCusp_mean N (lt_trans Nat.zero_lt_one hN) s hs y hy,
    completedReflectedConstant_eq_euler N hN s hhalf y hy]

/-- The center retains its actual completed removable value, with no
division by a totalized completed-zeta or Gamma factor. -/
theorem completed_zeroCusp_mean_critical (N : ℕ) (hN : 0 < N) (t : ℝ)
    (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, completedLevelOldform N (criticalParameter t)
      (frickeSL N hN • horizontalPoint y hy x)) =
      completedReflectedConstant N (criticalParameter t) y :=
  completed_zeroCusp_mean N hN _ (criticalParameter_mem_completedRegularDomain N t) y hy

private theorem initial_mem_regular (N : ℕ) (s : ℂ) (hs : 1 < s.re) :
    s ∈ completedRegularDomain N := by
  refine ⟨?_, ?_, normalization_ne_zero _ s hs⟩
  · intro h; subst s; norm_num at hs
  · intro h; subst s; norm_num at hs

private theorem completionFactor_initial_ne_zero (s : ℂ) (hs : 1 < s.re) :
    completionFactor s ≠ 0 := by
  unfold completionFactor
  refine mul_ne_zero (mul_ne_zero
    (Complex.cpow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Complex.Gamma_ne_zero_of_re_pos (by linarith))) ?_
  apply riemannZeta_ne_zero_of_one_lt_re
  simp
  linarith

/-- Identification with the actual original GammaInfinity\Gamma0 series,
not a formal coefficient. Division is confined to its genuine Re(s)>1 domain. -/
theorem actualParabolic_zeroCusp_mean_initial (N : ℕ) (hN : 0 < N)
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1,
      actualComplexParabolicEisenstein N s (frickeSL N hN • horizontalPoint y hy x)) =
        completedReflectedConstant N s y / completionFactor s := by
  have hmean := completed_zeroCusp_mean N hN s (initial_mem_regular N s hs) y hy
  simp_rw [completedLevelOldform_eq_initial N hN s hs,
    ← actualComplexParabolicEisenstein_eq_half_pair_sum N s hs] at hmean
  rw [intervalIntegral.integral_const_mul] at hmean
  apply (eq_div_iff (completionFactor_initial_ne_zero s hs)).mpr
  simpa only [mul_comm] using hmean

end ImbalancedChen.Part3.ActualContinuedZeroCuspMean20261026a
