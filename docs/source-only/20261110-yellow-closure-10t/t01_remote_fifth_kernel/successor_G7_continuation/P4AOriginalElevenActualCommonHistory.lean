import ImbalancedChen.P4AOriginalElevenHistoricalMesh
import ImbalancedChen.P4AOriginalElevenSixthStage
import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual enriched old+new fifth union, original475q-1 coarse mesh and
original Gamma lookup realize the G7 whole-first/third/fifth histories.
The conclusion predicate below is derived from the compact source; it is
not added to OriginalData and is not a new Licence field. The source's
sixth-coordinate cutoff excludes G4 only: new fifth rows are retained.
-/
namespace ImbalancedChen.P4AOriginalElevenActualCommonHistory
noncomputable section
open Set Filter VariableEnvelope
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalElevenHistoricalMesh (Physical firstThree source_ordered exists_original_G7_historical_mesh)
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthCompactTrim (trim trim_subset_source)
open Certificates.P2OriginalSixthElevenLogSemantics (R0 H3 H5 S6 oldCap PhysicalCell)

abbrev bank := P4AOriginalNewFifthUnion.data
def root (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := lambda3 d N (rosserAncestor 4 pre)

def ActualHistory (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ) (i : Fin 11) : Prop :=
  let d := bank e q a
  let t := primeHistoryLogCoordinates N 6 pre
  HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N (rosserAncestor 1 pre) ∧
  P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre) ∧
  root d N pre=originalSeed d N pre ∧
  3*t 0<root d N pre ∧ H3 t<root d N pre ∧ H5 t<root d N pre ∧
  t 5<root d N pre-S6 t ∧
  root d N pre≤actualParent5 d N pre ∧ actualParent5 d N pre≤oldCap (sourceCell i) t

theorem firstThree_ancestor (N : ℝ) (pre : List ℕ) (hlen : pre.length=6) :
    firstThree (primeHistoryLogCoordinates N 6 pre)=
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) := by
  funext j
  exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 3≤6) j).symm

theorem original_mesh_above (m0 q : ℕ) (hq : m0+1≤q) (e : ℚ) (a : ℝ) :
    m0≤(bank e q a).m := by
  change m0≤P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q
  unfold P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh
  omega

theorem original_third_active (a N : ℝ) (hN : 1<N) (ha : a≤1/100)
    (pre : List ℕ) (hlen : pre.length=6) (hp : ∀ p∈pre,0<p)
    (i : Fin 11) (hc : PhysicalCell (sourceCell i) (primeHistoryLogCoordinates N 6 pre)) :
    HistoricalThirdCoarse.active a N (rosserAncestor 3 pre) := by
  have hlen3 : (rosserAncestor 3 pre).length=3 := by simp [hlen]
  have hp3 : ∀ p∈rosserAncestor 3 pre,0<p := fun p hh => hp p (List.mem_of_mem_drop hh)
  refine ⟨hlen3,?_⟩
  rw [← rpow_primeHistoryLogCoordinates N hN hlen3 hp3 (2:Fin 3)]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  rw [← firstThree_ancestor N pre hlen]
  have hcut := hc.compactCutoff
  have h54 := hc.order.1
  have h43 := hc.order.2.1
  have h32 := hc.order.2.2.1
  change a≤primeHistoryLogCoordinates N 6 pre 2
  linarith

theorem actual_root_eq_seed (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length=6)
    (i : Fin 11) (hc : PhysicalCell (sourceCell i) (primeHistoryLogCoordinates N 6 pre)) :
    root d N pre=originalSeed d N pre := by
  have h := P4AOriginalElevenFifthComparison.actual_third_eq_supported_original d N pre hlen (sourceCell i) hc
  simpa only [root,originalSeed,P1OriginalVariableFourthContinuation.seedExponent] using h

theorem root_le_actual_fifth (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    root d N pre≤actualParent5 d N pre := by
  have h := lambda3_le_exponent5 d N (rosserAncestor 5 pre)
  rw [lambda3_ancestor d N 5 (by decide),← lambda3_ancestor d N 4 (by decide) pre] at h
  exact h

/-- One genuine pre-N schedule, for all original G7 compact points and
all positive labelled histories. Supported ancestor, whole first stop,
all three strict old cube margins and actual union fifth bounds are
CONCLUSIONS. No87-source/admissibility result occurs in this proof. -/
theorem exists_original_G7_common_history (delta : ℝ) (hdelta : 0<delta) :
    ∃ e0 : ℝ, 0<e0 ∧ ∀ e : ℚ, 0<e → (e:ℝ)<e0 →
    ∃ q0 : ℕ, 0<q0 ∧ ∀ q : ℕ, q0≤q →
    ∀ a : ℝ, a≤1/100 → ∀ N : ℝ, 1<N →
    ∀ pre : List ℕ, pre.length=6 → (∀ p∈pre,0<p) →
    ∀ i : Fin 11, primeHistoryLogCoordinates N 6 pre∈trim i delta →
      ActualHistory e q a N pre i := by
  obtain ⟨e0,he0,hmesh⟩ := exists_original_G7_historical_mesh delta hdelta
  refine ⟨e0,he0,?_⟩
  intro e he hee
  have heR : (0:ℝ)<e := by exact_mod_cast he
  obtain ⟨m0,hm0⟩ := hmesh (e:ℝ) heR hee ((e:ℝ)/20) (by positivity) (by linarith)
  refine ⟨m0+1,by omega,?_⟩
  intro q hq a ha N hN pre hlen hp i ht
  let d := bank e q a
  let t := primeHistoryLogCoordinates N 6 pre
  have hc := trim_subset_source i hdelta ht
  have hdm : m0≤d.m := original_mesh_above m0 q hq e a
  obtain ⟨j,hj,hjt,hfirst,hh3,hh5,hres,hlo,hup⟩ := hm0 d.m hdm i t ht
  have hj' : j∈HistoricalThirdCoarse.cells (d.e:ℝ) d.chi d.m := hj
  have hsup : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre) := by
    refine ⟨original_third_active a N hN ha pre hlen hp i hc,j,hj',?_⟩
    rw [← firstThree_ancestor N pre hlen]
    exact hjt
  have hseed := actual_root_eq_seed d N pre hlen i hc
  have hlookup : root d N pre=HistoricalThirdCoarse.exponent (e:ℝ) ((e:ℝ)/20) d.m (firstThree t) := by
    rw [hseed,originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hsup,← firstThree_ancestor N pre hlen]
  have hstop : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m N (rosserAncestor 1 pre) := by
    have h0 := mem_logPrimeMeshCell.mp hjt (0:Fin 3)
    have hco : primeHistoryLogCoordinates N 1 (rosserAncestor 1 pre) 0=firstThree t 0 :=
      primeHistoryLogCoordinates_ancestor N hlen (by decide : 1≤6) (0:Fin 1)
    refine ⟨j 0,?_,?_,?_⟩
    · simpa only [hco,logPrimeMeshLo] using h0.1
    · simpa only [hco,logPrimeMeshHi] using h0.2
    · have hs := ((HistoricalThirdCoarse.mem_cells _ _ _ _).mp hj').2.2.2.2.1
      simpa [HistoricalThirdCoarse.box,qLogPrimeMeshHi] using hs
  refine ⟨hstop,hsup,hseed,?_,?_,?_,?_,root_le_actual_fifth d N pre,?_⟩
  · rw [hlookup]; exact hfirst
  · rw [hlookup]; exact hh3
  · rw [hlookup]; exact hh5
  · rw [hlookup]; exact hres
  · exact P4AOriginalElevenFifthComparison.supported_fifth_le_comparison d N he.le pre hlen (sourceCell i) hc hsup

/-- The later physical cutoff may be chosen below the early activation
parameter; equality with that parameter is never assumed. This preserves
the real wholly ordered old owner in the updated full policy. -/
theorem late_policy_on_original_owner {e : ℚ} {q : ℕ} {a omega N : ℝ}
    (he : 0≤e) (hN : 1≤N) (hwa : omega≤a) {pre : List ℕ} {i : Fin 11}
    (hh : ActualHistory e q a N pre i) (delta : ℝ) (n : ℕ) (pos : Bool) :
    P4AOriginalOrderedThirdFullPolicy.policy delta n (bank e q a) omega N pos pre =
      P4AOriginalFull87DataPolicy.policy delta n (bank e q a) N pos pre := by
  apply P4AOriginalOrderedThirdFullPolicy.policy_on_old_owner
    (by exact_mod_cast he) hN hwa
  exact hh.2.1

/-- The actual coarse owner also supplies the initial-cap upper bound
needed for reverse tuple selection; it is not a supplied history field. -/
theorem actual_history_initial_upper {e : ℚ} {q : ℕ} {a N : ℝ} {pre : List ℕ} {i : Fin 11}
    (he : 0≤(e:ℝ)) (hh : ActualHistory e q a N pre i) :
    root (bank e q a) N pre<HistoricalThirdCoarse.initial (e:ℝ) := by
  let d := bank e q a
  have hsup := hh.2.1
  have hseed := hh.2.2.1
  obtain ⟨hact,j,hj,ht⟩ := hsup
  have hs := (HistoricalThirdCoarse.mem_cells _ _ _ _).mp hj
  have hsupport : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre) :=
    ⟨hact,j,hj,ht⟩
  rw [hseed,originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hsupport,
    HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
  exact HistoricalThirdCoarse.levelExponent_lt_initial _ _ he hs.1 hs.2.1

end
end ImbalancedChen.P4AOriginalElevenActualCommonHistory
