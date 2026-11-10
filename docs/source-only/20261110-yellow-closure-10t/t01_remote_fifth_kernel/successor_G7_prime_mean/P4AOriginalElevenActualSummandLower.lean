import ImbalancedChen.P4AOriginalElevenProfileQuantization
import ImbalancedChen.P4AOriginalSixthClosedQuotients

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The literal same-node ordinary residual difference is bounded below by
the ORIGINAL G7 rational profile, with two explicit paid errors: the
unchanged cap quantizer and the existing actual-density approximation.
This is uniform before the tuple and both actual varying stage caps.
The full admitted sum, prime integral and outside-trim error remain separate.
-/
namespace ImbalancedChen.P4AOriginalElevenActualSummandLower
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open P4AOriginalElevenActualCommonHistory (bank)
open P4AOriginalElevenOwnCaps (comparisonTies)
open P2OriginalSixthMomentRow (cutoff)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalElevenPrimeOccurrence (pre_log pre_length)
open P4AOriginalElevenRankSixSigned (tupleResidual)
open P4AOriginalFull87HistoryCore (width)
open Certificates.P2OriginalSixthElevenLogSemantics (S6 oldCap newCap)

theorem exists_original_G7_actual_summand_lower (delta eta : ℝ)
    (hdelta : 0<delta) (heta : 0<eta) :
    ∃ N0 : ℕ, 2≤N0 ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∃ e0 : ℝ, 0<e0 ∧
    ∀ e : ℚ, 0<e → (e:ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
    ∀ a : ℝ, a≤1/100 → ∀ N : ℕ, N0≤N → Even N → ∀ cap : ℕ,
    ∀ p : Fin 6 → ℕ, (∀ j,(p j).Prime) → (p 5:ℝ)≤cap → ∀ i : Fin 11,
    actualPrimeTupleLog N p∈trim i delta → actualPrimeTupleLog N p∉comparisonTies →
      primeBoxInitialSavingProfile (oldCap (sourceCell i) (actualPrimeTupleLog N p))
          (newCap (sourceCell i) (actualPrimeTupleLog N p)) (actualPrimeTupleLog N p)-
        (8*width n/cutoff^2+eta)≤tupleResidual n (bank e q a) N cap p := by
  obtain ⟨N0,hN0,hbound⟩ := P4AOriginalSixthClosedQuotients.difference_close eta heta
  obtain ⟨n0,hU⟩ := P4AOriginalElevenOwnCaps.exists_original_G7_own_caps delta hdelta
  refine ⟨N0,hN0,n0,?_⟩
  intro n hn
  obtain ⟨e0,he0,hE⟩ := hU n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha N hN hEven cap p hp hcap i ht hties
  have hN1 : 1<N := by omega
  have hNR : (1:ℝ)<N := by exact_mod_cast hN1
  have hpos : ∀ j,0<p j := fun j => (hp j).pos
  have hprepos : ∀ x∈pre p,0<x := by
    intro x hx
    simp only [pre,List.mem_reverse,List.mem_ofFn] at hx
    obtain ⟨j,rfl⟩ := hx
    exact hpos j
  have ht' : primeHistoryLogCoordinates (N:ℝ) 6 (pre p)∈trim i delta := by
    simpa only [pre_log] using ht
  have hties' : primeHistoryLogCoordinates (N:ℝ) 6 (pre p)∉comparisonTies := by
    simpa only [pre_log] using hties
  obtain ⟨heq,hPR,hgain,hres,hnew,hupper⟩ :=
    hQ q hq a ha (N:ℝ) hNR (pre p) (pre_length p) hprepos i ht' hties'
  simp only [pre_log] at heq hPR hgain hres hnew hupper
  let P := P4AOriginalSavedSixthStage.level n (bank e q a) (N:ℝ) (pre p)
  let M := P4AOriginalElevenSixthStage.level n (bank e q a) (N:ℝ) (pre p)
  let t := actualPrimeTupleLog N p
  have hc := trim_subset_source i hdelta ht
  have hPM : P≤M := P4AOriginalElevenSixthStage.saved_le_level n (bank e q a) (N:ℝ) (pre p)
  have hround := P4AOriginalElevenProfileQuantization.original_profile_rounded_lower
    n hc hres hPR hPM heq
  have hhi : t 5≤P4AOriginalSixthClosedQuotients.high := by
    have hh := hc.oldCutoff.le
    change t 5≤1/5
    linarith
  have hcapNat : p 5≤cap := by exact_mod_cast hcap
  have herr := hbound N hN hEven p hpos P M hc.compactCutoff.le hhi
    hres.le hPM hnew.le cap hcapNat
  have hP0 : 0<P-S6 t := hc.rpos.trans hres
  have hM0 : 0<M-S6 t := hP0.trans_le (sub_le_sub_right hPM _)
  rw [← P4AOriginalElevenProfileQuantization.profile_eq_reciprocals hP0.ne' hM0.ne'] at herr
  have hlo := (abs_lt.mp herr).1
  change _≤actualPrimeTupleInitialSaving N cap P M p
  linarith

end
end ImbalancedChen.P4AOriginalElevenActualSummandLower
