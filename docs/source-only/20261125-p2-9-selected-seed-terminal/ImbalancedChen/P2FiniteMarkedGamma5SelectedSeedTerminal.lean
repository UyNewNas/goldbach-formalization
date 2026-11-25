import ImbalancedChen.P2FiniteMarkedGamma5SelectedItinerary
import ImbalancedChen.Part5OriginalH430SeedHistoryMass
import ImbalancedChen.Part5OriginalH430EmittedNativeQueries

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedSeedTerminal
noncomputable section
open Finset
open P2Selected430CausalOccurrenceExporter
open P5OriginalFeedbackTableKernels
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430ClosedOwner
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open Part5OriginalH430EmittedNativeQueries Part5OriginalH430JointQueryEnclosure
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2FiniteMarkedGamma5SelectedItinerary
open scoped Classical BigOperators

/-- Fixed finite atom decision for scalar reads; specified-cell reads
keep their own stored index, including on a closed knot. -/
def terminalTest (r : Request) (atAtom : FloorAtom → Prop) : Prop :=
  match r.mode with
  | .cell i => 0 < floorValue (iterate 0 r.node.upper) i
  | .scalar => ∃ b : FloorAtom, atAtom b ∧
      0 < floorValue (iterate 0 r.node.upper) (atomOwner (iterate 0 r.node.upper) b)

theorem terminalTest_iff (r : Request) :
    terminalTest r (fun b => r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b) ↔
      0 < requestValue (iterate 0) r := by
  cases hm : r.mode with
  | cell i => simp [terminalTest,requestValue,hm]
  | scalar =>
    simp only [terminalTest,hm]
    constructor
    · rintro ⟨b,hb,hpos⟩
      simpa only [requestValue,hm,tableFunction_at_atom _ hb,atomOwner_value] using hpos
    · intro hpos
      have hex : ∃ b : FloorAtom, r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b := by
        by_contra h
        have hn : resolve 0 r = none := by simp [resolve,hm,h]
        exact (ne_of_gt hpos) (resolve_none_value hn)
      obtain ⟨b,hb⟩ := hex
      refine ⟨b,hb,?_⟩
      simpa only [requestValue,hm,tableFunction_at_atom _ hb,atomOwner_value] using hpos

/-- A literal path reaches a positive seed position exactly when all 430
actual edge tests succeed and its final request reads a positive entry. -/
theorem fixed_path_seed_iff (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (es : List (Edge N)) :
    (∃ l ∈ seedPositions N n k t p, (levelOccurrence l).path = es) ↔
      es.length = 430 ∧ accepts (rootQ N n k t p) 430 (rootRequest N n k t p) es ∧
      0 < requestValue (iterate 0) (replay (rootRequest N n k t p) es) := by
  constructor
  · rintro ⟨l,hl,he⟩
    obtain ⟨ho,hr⟩ := levelOccurrence_source l
    obtain ⟨hc,hlen,hstate⟩ := history_facts ho
    have hp0 := (mem_filter.mp hl).2
    rw [he] at hc hlen hstate
    exact ⟨by omega,(accepts_iff_chosen _ _ _ _).mpr hc,by simpa only [← hstate] using hp0⟩
  · rintro ⟨hlen,hacc,hpos⟩
    let o := finish 430 (rootRequest N n k t p) es
    have ho : o ∈ rootHistory N n k t p := (finish_mem_iff _ _ _ _).mpr hacc
    have hr : o.remaining = 0 := by simp [o,finish,hlen]
    have hm : o ∈ levelRequests N n k t p 0 := by
      exact List.mem_filter.mpr ⟨ho,by simp [hr]⟩
    obtain ⟨l,hle⟩ := List.mem_iff_get.mp hm
    have hx : levelOccurrence l = o := hle
    exact ⟨l,mem_filter.mpr ⟨mem_univ _,by simpa only [hx] using hpos⟩,by rw [hx]; rfl⟩

/-- Same selection on the native labelled coordinates. The hypothesis
on the path is reconstructed internally before the emitted-query theorem
is used. The root prime and the native pair order are unchanged. -/
theorem fixed_path_native_seed_iff {N n p : ℕ} {k : Root} {t : ℝ}
    (mesh : ℕ) (es : List (Edge N)) (hN : 1 < N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) :
    (∃ l ∈ seedPositions N n k t p, (levelOccurrence l).path = es) ↔
      es.length = 430 ∧ accepts (rootQ N n k t p) 430 (rootRequest N n k t p) es ∧
      terminalTest (replay (rootRequest N n k t p) es) (fun b =>
        tuple p es ∈ nativeQuery n mesh k t (shapes es)
          (!(replay (rootRequest N n k t p) es).node.upper) b) := by
  rw [fixed_path_seed_iff]
  apply and_congr_right
  intro hlen
  apply and_congr_right
  intro hacc
  let o := finish 430 (rootRequest N n k t p) es
  have ho : o ∈ rootHistory N n k t p := (finish_mem_iff _ _ _ _).mpr hacc
  let r := replay (rootRequest N n k t p) es
  have hpred : (fun b => tuple p es ∈ nativeQuery n mesh k t (shapes es) (!r.node.upper) b) =
      (fun b => r.node.physical.argument ∈ tableAtomSet (!r.node.upper) b) := by
    funext b
    apply propext
    exact emitted_query_iff mesh (!r.node.upper) b hN ht ht' hn hp hb ho
  change 0 < requestValue (iterate 0) r ↔ terminalTest r _
  rw [hpred]
  exact (terminalTest_iff r).symm

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedSeedTerminal
