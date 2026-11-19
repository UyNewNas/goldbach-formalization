import ImbalancedChen.P4AOriginalElevenRankSixSigned
import ImbalancedChen.P4AOriginalSixthTupleReverse

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Every original G7 prime tuple on the derived compact schedule passes the
actual causal first/third/fifth decisions of the SAME enriched fifth tree.
The generic reverse-join proof is reused; no87 admissibility or G4 source
geometry is substituted. This is actual occurrence, not a numerical mean.
-/
namespace ImbalancedChen.P4AOriginalElevenPrimeOccurrence
noncomputable section
open Set Filter VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open P4AOriginalElevenActualCommonHistory (bank root ActualHistory)
open P4AOriginalSavedSixthSigned (pre)
open P5OriginalCommonRefinedConstructor (originalSeed)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell)

theorem pre_list (p : Fin 6 → ℕ) : pre p=[p 5,p 4,p 3,p 2,p 1,p 0] := by
  simp [pre,List.ofFn_succ]
theorem pre_length (p : Fin 6 → ℕ) : (pre p).length=6 := by simp [pre]
theorem pre_log (N : ℕ) (p : Fin 6 → ℕ) : primeHistoryLogCoordinates (N:ℝ) 6 (pre p)=actualPrimeTupleLog N p := by
  funext j
  fin_cases j <;> simp [pre_list,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]

theorem source_strictAnti {c : Certificates.P2OriginalSixthElevenLogSemantics.Cell}
    {t : Fin 6 → ℝ} (hc : PhysicalCell c t) : StrictAnti t := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  fin_cases j
  · exact hc.order.2.2.2.2
  · exact hc.order.2.2.2.1
  · exact hc.order.2.2.1
  · exact hc.order.2.1
  · exact hc.order.1

theorem source_prime_strictAnti {N : ℕ} (hN : 1<N) (p : Fin 6 → ℕ) (hp : ∀ j,0<p j)
    {c : Certificates.P2OriginalSixthElevenLogSemantics.Cell}
    (hc : PhysicalCell c (actualPrimeTupleLog N p)) : StrictAnti p := by
  intro j k hjk
  have h := Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ)<N by exact_mod_cast hN)
    (source_strictAnti hc hjk)
  rw [actualPrimeTupleLog_rpow hN p hp,actualPrimeTupleLog_rpow hN p hp] at h
  exact_mod_cast h

theorem selected_of_actual_history (n : ℕ) {e : ℚ} {q : ℕ} {a : ℝ} (he : 0≤(e:ℝ))
    {N : ℕ} (hN : 1<N) (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime) {i : Fin 11}
    (hc : PhysicalCell (sourceCell i) (actualPrimeTupleLog N p))
    (hh : ActualHistory e q a (N:ℝ) (pre p) i) :
    FirstExitValidSelection (P4AOriginalFull87DataPolicy.fifthPolicy n (bank e q a) (N:ℝ)) [] true (List.ofFn p) := by
  let d := bank e q a
  let L := root d (N:ℝ) (pre p)
  have h5 := P4AOriginalElevenAcceptedCaps.actual_level5_bounds n (pre_length p)
    (by simpa only [pre_log] using hc) hh
  have hini := P4AOriginalElevenActualCommonHistory.actual_history_initial_upper he hh
  rcases hh with ⟨hstop,hsup,hseed,hfirst,hthird,hfifth,hres,hLE,hER⟩
  have ho := source_prime_strictAnti hN p (fun j => (hp j).pos) hc
  have hs : HistoricalThirdCoarse.firstStop (e:ℝ) d.m (N:ℝ) [p 0] := by
    simpa [pre_list,rosserAncestor] using hstop
  have hseed3 : originalSeed d (N:ℝ) [p 2,p 1,p 0]=L := by
    rw [show L=originalSeed d (N:ℝ) (pre p) from hseed]
    simp [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,pre_list,rosserAncestor]
  have hlow : L≤P4AOriginalFull87DataPolicy.level5Exponent n d (N:ℝ) [p 4,p 3,p 2,p 1,p 0] := by
    simpa [pre_list,rosserAncestor] using h5.1
  rw [pre_log] at hfirst hthird hfifth
  exact P4AOriginalSixthTupleReverse.from_own_root n d hN p hp ho L hs hseed3 hini.le
    hfirst hthird hfifth hlow

/-- The schedule has no occurrence or source-licence premise. It derives
the actual word and Accepted cap for every original prime tuple on a trim.
The prime-limit and saving-payment estimate are deliberately separate. -/
theorem exists_original_G7_prime_occurrences (delta : ℝ) (hdelta : 0<delta) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0≤n → ∃ e0 : ℝ, 0<e0 ∧
    ∀ e : ℚ, 0<e → (e:ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
    ∀ a : ℝ, a≤1/100 → ∀ N : ℕ, 1<N → ∀ p : Fin 6 → ℕ, (∀ j,(p j).Prime) →
    ∀ i : Fin 11, actualPrimeTupleLog N p∈trim i delta →
      FirstExitValidSelection (P4AOriginalFull87DataPolicy.fifthPolicy n (bank e q a) (N:ℝ)) [] true (List.ofFn p) ∧
      P4AOriginalFull87DataPolicy.Accepted n (bank e q a) (N:ℝ) (pre p) (.eleven (sourceCell i)) := by
  obtain ⟨n0,hn0⟩ := P4AOriginalElevenAcceptedCaps.exists_joined_G7_history_and_caps delta hdelta
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨e0,he0,hE⟩ := hn0 n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha N hN p hp i ht
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hpos : ∀ x∈pre p,0<x := by
    intro x hx
    simp only [pre,List.mem_reverse,List.mem_ofFn] at hx
    obtain ⟨j,rfl⟩ := hx
    exact (hp j).pos
  have ht' : primeHistoryLogCoordinates (N:ℝ) 6 (pre p)∈trim i delta := by simpa only [pre_log] using ht
  obtain ⟨hh,hacc,_⟩ := hQ q hq a ha (N:ℝ) hNr (pre p) (pre_length p) hpos i ht'
  have hc := trim_subset_source i hdelta ht
  exact ⟨selected_of_actual_history n (by exact_mod_cast he.le) hN p hp hc hh,hacc⟩

end
end ImbalancedChen.P4AOriginalElevenPrimeOccurrence
