import ImbalancedChen.P4AOriginalSavedSixthIntegral
import ImbalancedChen.ActualPrimeIcoCellTestFunctions

/-! Each source rectangle owns its exact half-open faces in the target-deleted
prime sum. The physical 6-dimensional integral is the limit of this fixed
pre-N source, including all negative corner contributions in its Q80 floor. -/
namespace ImbalancedChen.P4AOriginalSavedSixthPrimeMean
noncomputable section
open Set Filter MeasureTheory
open scoped Classical BigOperators Topology
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthPlanes
open P4AOriginalSavedSixthBank (lo facts)
open P4AOriginalSavedSixthIntegral
open Certificates.P2OriginalSixthElevenLogSemantics (Physical)

abbrev cube := logPrimeBox (fun _ : Fin 6 => (1/50:ℝ)) (fun _ => (1/5:ℝ))
abbrev primes (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 6 => (1/50:ℝ)) (fun _ => (1/5:ℝ))
def profile (i : Row) (t : Physical) := rowTest i t * ∏ j,t j
def test (i : Row) := (box i).indicator (profile i)
def combined (t : Physical) := ∑ i : Row,test i t
def primeSum (N : ℕ) := actualPrimeBoxTestSum N
  (fun _ : Fin 6 => (1/50:ℝ)) (fun _ => (1/5:ℝ)) combined

theorem ordered6 (i : Row) {t : Physical} (ht : t∈box i) : StrictAnti t := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  have ha := (mem_logPrimeBox.mp ht j.succ).2
  have hb := (mem_logPrimeBox.mp ht j.castSucc).1
  have hc : lift (upperQ i) j.succ ≤ lift (lowerQ i) j.castSucc := by
    have h : (lo i j.succ:ℝ)+1 ≤ (lo i j.castSucc:ℝ) := by exact_mod_cast (facts i).order j
    simpa [lift,upperQ,lowerQ,lo] using div_le_div_of_nonneg_right h (by norm_num : (0:ℝ)≤400)
  exact ha.trans_le (hc.trans hb)

theorem bounds (i : Row) {t : Physical} (ht : t∈box i) (j : Fin 6) :
    1/50 ≤ t j ∧ t j < 39/200 := by
  have h0 : t j ≤ t 0 := (ordered6 i ht).antitone (Fin.zero_le j)
  have hx : t 0 < lift (upperQ i) 0 := (mem_logPrimeBox.mp ht 0).2
  have htop : lift (upperQ i) 0 ≤ 39/200 := by
    have hh : (lo i 0:ℝ)+1 ≤ 78 := by exact_mod_cast (facts i).right
    have h : ((lo i 0:ℝ)+1)/400 ≤ 39/200 :=
      (div_le_iff₀ (by norm_num : (0:ℝ)<400)).mpr (by linarith only [hh])
    simpa [lift,upperQ,lo] using h
  have hlow : (1/50:ℝ) ≤ lift (lowerQ i) j := by exact_mod_cast low i j
  exact ⟨hlow.trans (mem_logPrimeBox.mp ht j).1,h0.trans_lt (hx.trans_le htop)⟩

theorem cube_subset (i : Row) : box i ⊆ cube := by
  intro t ht
  exact mem_logPrimeBox.mpr (fun j => ⟨(bounds i ht j).1,
    (bounds i ht j).2.trans (by norm_num)⟩)

theorem continuous_profile (i : Row) : Continuous (profile i) := by
  apply Continuous.mul
  · exact continuous_const.mul (continuous_const.max
      (P4AOriginalSavedSixthCornerIntegral.continuous_gap i (grid i)))
  · exact continuous_finsetProd _ (fun j _ => continuous_apply j)

theorem profile_density (i : Row) {t : Physical} (ht : t∈box i) :
    profile i t*(∏ j,1/t j) = rowTest i t := by
  have hne (j : Fin 6) : t j ≠ 0 :=
    ((by norm_num : (0:ℝ)<1/50).trans_le (bounds i ht j).1).ne'
  simp [profile,mul_assoc,← Finset.prod_mul_distrib,hne]

theorem test_nonneg (i : Row) (t : Physical) : 0 ≤ test i t := by
  by_cases ht : t∈box i
  · rw [test,Set.indicator_of_mem ht]
    exact mul_nonneg (mul_nonneg (by exact_mod_cast (pref_pos i).le) (le_max_left _ _))
      (Finset.prod_nonneg fun j _ => (by norm_num : (0:ℝ)≤1/50).trans (bounds i ht j).1)
  · simp [test,ht]

theorem combined_eq (i : Row) {t : Physical} (ht : t∈box i) : combined t = profile i t := by
  rw [combined,Finset.sum_eq_single i,test,Set.indicator_of_mem ht]
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hj => Set.disjoint_left.mp (box_disjoint hji) hj ht) _
  · simp

theorem positive_owner {t : Physical} (h : combined t ≠ 0) :
    ∃ i : Row,t∈box i ∧ P4AOriginalSavedSixthArchive.oldUpper i t <
      P4AOriginalSavedSixthArchive.endpoint i t := by
  obtain ⟨i,hi⟩ : ∃ i : Row,test i t ≠ 0 := by
    by_contra! hz; exact h (by simp [combined,hz])
  have ht : t∈box i := by by_contra hn; exact hi (Set.indicator_of_notMem hn _)
  refine ⟨i,ht,?_⟩
  by_contra! hn
  exact hi (by simp [test,ht,profile,rowTest,P4AOriginalSavedSixthCornerIntegral.gap,
    max_eq_left (sub_nonpos.mpr hn)])

theorem row_limit (i : Row) : Tendsto (fun N : ℕ => actualPrimeBoxTestSum N
    (fun _ : Fin 6 => (1/50:ℝ)) (fun _ => (1/5:ℝ)) (test i)) atTop (𝓝 (rowIntegral i)) := by
  let L : Fin 0 → Physical →L[ℝ] ℝ := Fin.elim0
  let c : Fin 0 → ℝ := Fin.elim0
  have h := tendsto_actualPrimeBoxTestSum_cube_affineSandwich (by norm_num : (0:ℝ)<1/50)
    (by norm_num : (1/50:ℝ)<1/5) (primeIcoBoxGateForms L)
    (primeIcoBoxGateBounds (lift (lowerQ i)) (lift (upperQ i)) c)
    (primeIcoBoxGateForms_ne_zero L (fun j => Fin.elim0 j))
    (box i) (measurableSet_logPrimeBox _ _)
    (fun t ht => by
      have hh := ((mem_primeIcoBoxStrictGateRegion _ _ L c t).mp ht).1
      exact mem_logPrimeBox.mpr (fun j => ⟨(hh j).1.le,(hh j).2⟩))
    (fun t ht => by
      simp only [primeIcoBoxGateForms,primeIcoBoxGateBounds,Fin.forall_fin_add,Fin.append_left,
        Fin.append_right,neg_apply,ContinuousLinearMap.proj_apply,neg_le_neg_iff]
      exact ⟨fun j => (mem_logPrimeBox.mp ht j).1,fun j => (mem_logPrimeBox.mp ht j).2.le,
        fun j => Fin.elim0 j⟩)
    (profile i) (continuous_profile i).continuousOn
  have hh : (∫ t in cube ∩ box i,profile i t*∏ j,1/t j) = rowIntegral i := by
    rw [inter_eq_right.mpr (cube_subset i),rowIntegral]
    exact setIntegral_congr_fun (measurableSet_logPrimeBox _ _) (fun _ ht => profile_density i ht)
  simpa only [test,hh] using h

theorem prime_limit : Tendsto primeSum atTop (𝓝 (∑ i : Row,rowIntegral i)) := by
  have h (N : ℕ) : primeSum N = ∑ i : Row,actualPrimeBoxTestSum N
      (fun _ : Fin 6 => (1/50:ℝ)) (fun _ => (1/5:ℝ)) (test i) := by
    unfold primeSum actualPrimeBoxTestSum combined
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
  rw [funext h]
  exact tendsto_finsetSum _ (fun i _ => row_limit i)

theorem eventually_slot (epsilon : ℝ) (he : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop,currentUpperEighteenGains 3-epsilon < primeSum N :=
  prime_limit.eventually (lt_mem_nhds (by rw [slot_four]; linarith only [original_floor_le_sum,he]))

end
end ImbalancedChen.P4AOriginalSavedSixthPrimeMean
