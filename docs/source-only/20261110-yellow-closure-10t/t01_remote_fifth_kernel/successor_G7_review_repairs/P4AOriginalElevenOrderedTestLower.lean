import ImbalancedChen.P4AOriginalElevenOrderedLocal
import ImbalancedChen.P2OriginalSixthInnerPrimeTests

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
One bound holds for EVERY prime-box word on the actual corrected tree.
Positive continuous tests are paid on their derived old owners; all
remaining admitted words use the GLOBAL closed-window lower error.
No word outside a compact trim is discarded from the signed source.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedTestLower
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthMomentRow (cutoff)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open P2OriginalSixthInnerPrimeRamp (ramp ramp_off_trim ramp_on_comparison_ties)
open P2OriginalSixthInnerPrimeTests (test profile test_bounds)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalElevenActualCommonHistory (bank)
open P4AOriginalElevenOwnCaps (comparisonTies unique_original_source)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalElevenPrimeOccurrence (pre_log pre_length)

theorem sourceCell_injective : Function.Injective sourceCell := by decide

theorem test_nonzero_source (r : ℕ) (i : Fin 11) {t : Fin 6→ℝ} (ht : test r i t≠0) :
    t∈trim i (width r) ∧ t∉comparisonTies := by
  have hr := (mul_ne_zero_iff.mp ht).2
  exact ⟨by intro hh; exact hr (ramp_off_trim r i hh),
    by intro hh; exact hr (ramp_on_comparison_ties r i hh)⟩

theorem test_sum_eq_single (r : ℕ) (i : Fin 11) {t : Fin 6→ℝ} (ht : test r i t≠0) :
    (∑ j : Fin 11,test r j t)=test r i t := by
  obtain ⟨htrim,htie⟩ := test_nonzero_source r i ht
  have hc := trim_subset_source i (width_pos r) htrim
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_contra hj
    obtain ⟨hjtrim,_⟩ := test_nonzero_source r j hj
    have hcj := trim_subset_source j (width_pos r) hjtrim
    exact hji (sourceCell_injective (unique_original_source i hc htie (sourceCell j) hcj))
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The target threshold is uniform before the resolution, early/late
cutoffs, policy data and tuple. The e/q schedule is shared by all eleven
original sources. The displayed term is on the UPDATED admitted set. -/
theorem exists_ordered_G7_test_lower (r : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∃ n0 : ℕ,∀ n≥n0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/100 → omega≤a → ∀ N≥N0,Even N →
    ∀ p∈actualPrimeBoxTuples N (fun _ : Fin 6 => cutoff) (fun _ => mu),
      (∑ i : Fin 11,test r i (actualPrimeTupleLog N p))≤
        (if p∈P4AOriginalOrderedSixthSigned.admitted n (bank e q a) omega N N
            (P4AOriginalFull87RawChronology.cutoff N)
          then P4AOriginalOrderedSixthSigned.tupleResidual 1 n (bank e q a) omega N N p else 0)+
        (8*width n/cutoff^2+eta) := by
  obtain ⟨NP,hNP,n0,hP⟩ := P4AOriginalElevenActualSummandLower.exists_original_G7_actual_summand_lower
    (width r) eta (width_pos r) heta
  obtain ⟨NG,hNG,hG⟩ := P4AOriginalElevenOrderedChangedSupport.exists_whole_ordered_G7_negative_error eta heta
  obtain ⟨eH,heH,hH⟩ := P4AOriginalElevenActualCommonHistory.exists_original_G7_common_history (width r) (width_pos r)
  refine ⟨max NP NG,hNP.trans (le_max_left _ _),n0,?_⟩
  intro n hn
  have hwpos : 0≤width n := (width_pos n).le
  obtain ⟨eP,heP,hPE⟩ := hP n hn
  refine ⟨min eP eH,lt_min heP heH,?_⟩
  intro e he hee
  obtain ⟨qP,hqP,hPQ⟩ := hPE e he (hee.trans_le (min_le_left _ _))
  obtain ⟨qH,hqH,hHQ⟩ := hH e he (hee.trans_le (min_le_right _ _))
  refine ⟨max qP qH,hqP.trans_le (le_max_left _ _),?_⟩
  intro q hq a omega ha hwa N hN hev p hp
  have hNP := (le_max_left NP NG).trans hN
  have hNG := (le_max_right NP NG).trans hN
  have hqP' := (le_max_left qP qH).trans hq
  have hqH' := (le_max_right qP qH).trans hq
  have hN1 : 1<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast hN1
  have heR : 0≤(e:ℝ) := by exact_mod_cast he.le
  have hE : 0≤8*width n/cutoff^2+eta := by positivity
  obtain ⟨hpri,hbox⟩ := (mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp
  have hpos (j) := (hpri j).1.pos
  by_cases hsome : ∃ i : Fin 11,test r i (actualPrimeTupleLog N p)≠0
  · obtain ⟨i,hi⟩ := hsome
    obtain ⟨htrim,htie⟩ := test_nonzero_source r i hi
    have hprepos : ∀ x∈pre p,0<x := by
      intro x hx
      simp only [pre,List.mem_reverse,List.mem_ofFn] at hx
      obtain ⟨j,rfl⟩ := hx
      exact hpos j
    have hh := hHQ q hqH' a ha (N:ℝ) hNr (pre p) (pre_length p) hprepos i
      (by simpa only [pre_log] using htrim)
    have hc := trim_subset_source i (width_pos r) htrim
    have hadm := P4AOriginalElevenOrderedLocal.admitted_on_derived_owner n heR hN1 hwa p hp hc hh
    have hres := P4AOriginalElevenOrderedLocal.residual_on_derived_owner n heR hNr.le hwa p hh
    have hpcap : (p 5:ℝ)≤N := by
      rw [← actualPrimeTupleLog_rpow hN1 p hpos 5]
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
        (((mem_logPrimeBox.mp hbox 5).2).le.trans (by norm_num [mu] : mu≤1))
    have hpaid := hPQ q hqP' a ha N hNP hev N p (fun j => (hpri j).1) hpcap i htrim htie
    rw [test_sum_eq_single r i hi,if_pos hadm,hres]
    have hprofile := P2OriginalSixthInnerPrimeTests.profile_eq_on_source hc
    have htbound := (test_bounds r i (actualPrimeTupleLog N p)).2
    rw [hprofile] at htbound
    linarith
  · have hzero : (∑ i : Fin 11,test r i (actualPrimeTupleLog N p))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_contra hi
      exact hsome ⟨i,hi⟩
    rw [hzero]
    split_ifs with hadm
    · have hg := hG N hNG hev n (bank e q a) omega N (P4AOriginalFull87RawChronology.cutoff N) p hadm
      have hw : 0≤8*width n/cutoff^2 := by positivity
      linarith
    · exact hE

end
end ImbalancedChen.P4AOriginalElevenOrderedTestLower
