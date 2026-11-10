import ImbalancedChen.P4AOriginalElevenOrderedChangedSupport
import ImbalancedChen.P4AOriginalOrderedFifthOwner
import ImbalancedChen.P4AOriginalElevenActualSummandLower

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Only words whose actual old historical owner has been DERIVED are moved
to that same owner in the updated whole-third policy. T05's per-word
admitted equivalence retains the whole actual common prime carrier.
This is not an equality between two complete raw policy differences.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedLocal
noncomputable section
open VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthMomentRow (cutoff)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open P4AOriginalElevenActualCommonHistory (bank ActualHistory)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalElevenPrimeOccurrence (pre_log pre_length)

theorem stage_caps_on_derived_owner (n : ℕ) {e : ℚ} {q : ℕ} {a omega N : ℝ}
    (he : 0≤(e:ℝ)) (hN : 1≤N) (hwa : omega≤a) {h : List ℕ} {i : Fin 11}
    (hh : ActualHistory e q a N h i) :
    P4AOriginalOrderedSixthStages.orderedLevel 1 n (bank e q a) omega N h=
        P4AOriginalSavedSixthStage.level n (bank e q a) N h ∧
    P4AOriginalOrderedSixthStages.orderedLevel 2 n (bank e q a) omega N h=
        P4AOriginalElevenSixthStage.level n (bank e q a) N h := by
  have hs : P1ThirdFallbackSupport.frozenSupported (bank e q a).e (bank e q a).chi
      (bank e q a).m (bank e q a).omega N h := hh.2.1
  have h1 := P4AOriginalOrderedSixthStages.level_on_owner 1 n (bank e q a) omega N he hN hwa h hs
  have h2 := P4AOriginalOrderedSixthStages.level_on_owner 2 n (bank e q a) omega N he hN hwa h hs
  rw [P4AOriginalOrderedSixthStages.prior_saved] at h1
  rw [P4AOriginalOrderedSixthStages.prior_later 0,
    P4AOriginalLaterSixthStages.level_zero] at h2
  exact ⟨h1,h2⟩

theorem residual_on_derived_owner (n : ℕ) {e : ℚ} {q : ℕ} {a omega : ℝ} {N cap : ℕ}
    (he : 0≤(e:ℝ)) (hN : 1≤(N:ℝ)) (hwa : omega≤a) (p : Fin 6→ℕ) {i : Fin 11}
    (hh : ActualHistory e q a (N:ℝ) (pre p) i) :
    P4AOriginalOrderedSixthSigned.tupleResidual 1 n (bank e q a) omega N cap p=
      P4AOriginalElevenRankSixSigned.tupleResidual n (bank e q a) N cap p := by
  obtain ⟨h1,h2⟩ := stage_caps_on_derived_owner n he hN hwa hh
  unfold P4AOriginalOrderedSixthSigned.tupleResidual P4AOriginalElevenRankSixSigned.tupleResidual
  rw [h1,h2]

/-- Every original prime-box word on a derived G7 trim is genuinely
admitted by the updated fifth tree at the original N/19-96 carrier.
The early activation a and later cutoff omega remain separate. -/
theorem admitted_on_derived_owner (n : ℕ) {e : ℚ} {q : ℕ} {a omega : ℝ} {N : ℕ}
    (he : 0≤(e:ℝ)) (hN : 1<N) (hwa : omega≤a) (p : Fin 6→ℕ)
    (hp : p∈actualPrimeBoxTuples N (fun _ : Fin 6 => cutoff) (fun _ => mu))
    {i : Fin 11} (hc : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell
      (sourceCell i) (actualPrimeTupleLog N p))
    (hh : ActualHistory e q a (N:ℝ) (pre p) i) :
    p∈P4AOriginalOrderedSixthSigned.admitted n (bank e q a) omega N N
      (P4AOriginalFull87RawChronology.cutoff N) := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  obtain ⟨hpri,hbox⟩ := (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp
  have hpos (j) := (hpri j).1.pos
  have hword := P4AOriginalElevenPrimeOccurrence.selected_of_actual_history n he hN p
    (fun j => (hpri j).1) hc hh
  have hzcap : P4AOriginalFull87RawChronology.cutoff N≤(N:ℝ) := by
    simpa only [P4AOriginalFull87RawChronology.cutoff,Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (19/96:ℝ)≤1)
  have hupper (j : Fin 6) : (p j:ℝ)<P4AOriginalFull87RawChronology.cutoff N := by
    rw [← actualPrimeTupleLog_rpow hN p hpos j]
    apply Real.rpow_lt_rpow_of_exponent_lt hNr
    exact ((mem_logPrimeBox.mp hbox j).2).trans (by norm_num [mu])
  have hold : p∈P4AOriginalSavedSixthSigned.admitted n (bank e q a) N N
      (P4AOriginalFull87RawChronology.cutoff N) := by
    apply (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 6 _ N N 0 _ hzcap p).mpr
    exact ⟨P4AOriginalElevenPrimeOccurrence.source_prime_strictAnti hN p hpos hc,
      fun j => ⟨(hpri j).1,(hpri j).2,Nat.cast_nonneg _,hupper j⟩,hword⟩
  exact (P4AOriginalOrderedFifthOwner.admitted_iff_on_owner n (bank e q a) he hNr.le hwa p hh.2.1).mpr hold

end
end ImbalancedChen.P4AOriginalElevenOrderedLocal
