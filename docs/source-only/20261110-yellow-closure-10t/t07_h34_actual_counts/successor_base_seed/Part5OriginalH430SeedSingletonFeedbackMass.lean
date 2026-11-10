import ImbalancedChen.Part5OriginalH430SeedPairFeedbackMass

/-! The three actual seed singleton windows with their inherited Buchstab
lower consequence at the parameters of the original feedback certificate. -/
namespace ImbalancedChen.Part5OriginalH430SeedSingletonFeedbackMass
noncomputable section
open Set Real MeasureTheory Finset
open P2OriginalBankChildPrimeMass P2OriginalBankThetaMassLimits
open P2OriginalHalfOpenProfileCarrier P2OriginalCompactScaledPrimeMass
open P2OriginalCompactThetaMass P2OriginalPhysicalOldProfileMass
open P2EnhancedSeedSingletonPrimitive (S profile uStar cap singletonLogKernel seedLower literal_bounds
  profile_gt_two profile_short_support_iff)
open P2EnhancedSeedActualFeedbackAssembly (singletonCoefficient)
open scoped Classical BigOperators

def clippedLog (u : ℝ) : ℝ := log S-log (max 1 (min S (profile u-1)))
def singleTest (x : Coord 1) : ℝ := residualSingle x*clippedLog (x 0)
def singleMass (N : ℕ) (L : ℝ) (d : ℕ) (j : Fin 3) : ℝ :=
  trueSingleTest N L d (singleDomain uStar (cap j)) singleTest

private theorem clipped_continuous : Continuous clippedLog := by
  unfold clippedLog
  apply continuous_const.sub
  apply Continuous.log
  · unfold P2EnhancedSeedSingletonPrimitive.profile; fun_prop
  · exact fun x => (zero_lt_one.trans_le (le_max_left _ _)).ne'

private theorem test_bound (x : Coord 1) : |singleTest x|≤20 := by
  let c := max 1 (min S (profile (x 0)-1))
  have hc : 1≤c := le_max_left _ _
  have hc' : c≤S := max_le (by norm_num [S]) (min_le_left _ _)
  have hc0 := zero_lt_one.trans_le hc
  have h1 := log_le_log hc0 hc'
  have h2 := log_nonneg hc
  have h3 : log S≤2 := (log_le_sub_one_of_pos (by norm_num [S])).trans (by norm_num [S])
  change |residualSingle x*(log S-log c)|≤20
  rw [abs_of_nonneg (mul_nonneg (residualSingle_bounds x).1 (sub_nonneg.mpr h1))]
  have h := mul_le_mul (residualSingle_bounds x).2 (show log S-log c≤2 by linarith)
    (sub_nonneg.mpr h1) (by norm_num : (0:ℝ)≤10)
  linarith only [h]

theorem clipped_eq {u : ℝ} (hu : uStar≤u) (hv : u≤(5/11:ℝ)) :
    clippedLog u=log (S/(profile u-1)) := by
  have h2 := profile_gt_two hv
  have hS := (profile_short_support_iff u).mpr hu
  rw [clippedLog,min_eq_right (by linarith),max_eq_right (by linarith),
    log_div (by norm_num [S]) (by linarith)]

theorem prime_singleton_feedback {Lmin Lmax ε : ℝ} (hm : 0<Lmin) (hM : Lmin≤Lmax)
    (he : 0<ε) (j : Fin 3) :
    ∃ T : ℕ, ∀ N : ℕ,T≤N → ∀ L∈Icc Lmin Lmax,∀ d : ℕ,
      |singleMass N L d j-singletonCoefficient j|<ε := by
  have hhi := (literal_bounds j).2.2.2.1.trans (literal_bounds j).2.2.2.2.le
  have hcont : Continuous singleTest :=
    residualSingle_continuous.mul (clipped_continuous.comp (continuous_apply 0))
  obtain ⟨Tp,hp⟩ := compact_uniform_scaled_affine hm hM (by norm_num : (0:ℝ)≤20)
    (half_pos he) singleForms (singleBounds uStar (cap j)) singleForms_ne
    (by rw [←single_as_affine]; exact single_in_cube (by norm_num [uStar]) hhi)
    singleTest hcont test_bound
  obtain ⟨Ta,ha⟩ := compact_multiplier_error (k:=1) hm hM (by norm_num : (0:ℝ)≤40) (half_pos he)
  have hk : (∫ x in singleDomain uStar (cap j),singleTest x*∏ i,1/x i)=singletonCoefficient j := by
    unfold singletonCoefficient
    rw [integral_Icc_eq_integral_Ioo,←single_integral_coordinates]
    apply setIntegral_congr_fun
    · rw [single_as_affine]; exact measurableSet_primeAffineGateRegion _ _
    · intro x hx
      have h := clipped_eq hx.1.le (hx.2.le.trans (literal_bounds j).2.2.2.1)
      dsimp only [singleTest,singletonLogKernel]
      rw [h]
      calc
        _ = log (S/(profile (x 0)-1))*(residualSingle x * ∏ i,1/x i) := by ring
        _ = _ := by rw [single_kernel hhi hx]; ring
  refine ⟨max Tp Ta,?_⟩
  intro N hN L hL d
  have h := hp N ((le_max_left _ _).trans hN) L hL
  rw [←single_as_affine,hk] at h
  obtain ⟨hA,hE⟩ := ha N ((le_max_right _ _).trans hN) L hL
  have hlocal := trueSingleTest_error d (singleDomain uStar (cap j)) singleTest
    (by norm_num : (0:ℝ)≤20) test_bound hA
  norm_num at hlocal
  have htri := abs_sub_le (singleMass N L d j) (scaledPrimeSum N L (singleDomain uStar (cap j)) singleTest)
    (singletonCoefficient j)
  unfold singleMass at htri ⊢
  linarith only [htri,hlocal,h,hE]

end
end ImbalancedChen.Part5OriginalH430SeedSingletonFeedbackMass
