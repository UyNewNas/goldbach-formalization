import ImbalancedChen.P4AOriginalFull87GammaApproximation
import ImbalancedChen.P4AOriginalFull87HistoryCore
import ImbalancedChen.P2OriginalSaving16HistoricalMesh

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Uniform original joint-cell coverage and four actual historical margins on
the ALL87 retained source. This is a proof about the original finite mesh
and its actual Gamma lookup, not about an arbitrary cap approximation.
The scale is fixed before N and before every prime tuple. The actual source
predicate stays unchanged; a common compact history carrier is exhausted.
-/
namespace ImbalancedChen.P4AOriginalFull87CommonHistoricalMesh
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope HistoricalThirdCoarse
open P4AOriginalFull87SourceDictionary P4AOriginalFull87HistoryCore
open P4AOriginalFull87GammaApproximation
open P2OriginalSaving16HistoricalMesh
  (firstThree firstThree_ancestor mesh_box_width mesh_box_lower_nonneg
   actual_firstStop_of_joint_cell)

/-- Original joint mesh membership supplies the actual coordinate lookup.
No supported-third, history comparison, current-parent or frontier premise
is present. All original87 branches use ONE resolution threshold. -/
theorem exists_common_actual_mesh (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧
      ∀ e : ℝ, 0 < e → e < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ e / 10 →
      ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ c : Cell, ∀ t : Point,
      Source c t → t ∈ core delta →
        ∃ j ∈ HistoricalThirdCoarse.cells e chi m,
          firstThree t ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
          (∀ h : Fin 4, oldHistory t h < exponent e chi m (firstThree t)) ∧
          thirdValue t - ((9 / 2 : ℝ) * chi + 2 * e) ≤
            exponent e chi m (firstThree t) ∧
          exponent e chi m (firstThree t) ≤ thirdValue t := by
  refine ⟨min delta (3 / 256) / 20, by positivity, ?_⟩
  intro e he he0 chi hchi hchie
  have hed : 20 * e < delta := by
    have hh := min_le_left delta (3 / 256 : ℝ)
    linarith
  have heg : 20 * e < (3 / 256 : ℝ) := by
    have hh := min_le_right delta (3 / 256 : ℝ)
    linarith
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hchi))
  refine ⟨m0, ?_⟩
  intro m hm c t hs ht
  obtain ⟨hmu, h01, h12, hhist⟩ := core_margins ht
  obtain ⟨hlo, hup, _⟩ := (mem_core delta t).mp ht
  have ho := P4AOriginalFull87SourceDictionary.source_ordered hs
  have hbox : firstThree t ∈ logPrimeBox
      (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro k
    change 0 ≤ t ⟨k.val, by omega⟩ ∧ t ⟨k.val, by omega⟩ < (19 / 96 : ℝ)
    exact ⟨hlo _, (hup _).trans_lt (by norm_num [mu])⟩
  obtain ⟨j, hjt⟩ := exists_logPrimeMeshCell 0 (19 / 96) m hbox
  have hb := inBox_of_cell hjt
  change (box m j).InBox (t 0) (t 1) (t 2) at hb
  have hw : ((box m j).width : ℝ) ≤ chi := by
    rw [mesh_box_width]
    exact (hm0 m hm).le
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have hfull : ((box m j).ux : ℝ) ≤ mu - 4 * e := by
    linarith [hb.1]
  have hj : j ∈ HistoricalThirdCoarse.cells e chi m := by
    apply (mem_cells e chi m j).mpr
    refine ⟨RationalBox.wellFormed_of_inBox hb, mesh_box_lower_nonneg m j,
      ?_, ?_, ?_, hw⟩
    · have hh : ((box m j).uz : ℝ) ≤ (box m j).ly := by
        linarith [hb.2.2.2.1, hb.2.2.2.2.1]
      exact_mod_cast hh
    · have hh : ((box m j).uy : ℝ) ≤ (box m j).lx := by
        linarith [hb.2.1, hb.2.2.1]
      exact_mod_cast hh
    · have hh : mu ≤ extendedFirstStop := by norm_num [mu, extendedFirstStop]
      linarith
  have hsmall : e + 7 * chi ≤ 3 / 256 := by linarith
  have hg := P4AOriginalFull87GammaApproximation.actual_gamma_sandwich
    he.le ho hb hw hfull hsmall
  refine ⟨j, hj, hjt, ?_⟩
  rw [exponent_on_cell e chi m _ j hj hjt]
  refine ⟨?_, hg.1, hg.2⟩
  intro h
  have hh := hhist h
  change delta ≤ six (t 0) (t 1) (t 2) - oldHistory t h at hh
  linarith [hg.1]

/-- The original rough activation, with equality retained at the cutoff.
Positivity is supplied by the actual prime tuple (or any positive labels),
not by already-selected-frontier membership. -/
theorem actual_third_active (omega N : ℝ) (hN : 1 < N)
    (homega : omega ≤ 1 / 100) (pre : List ℕ) (hlen : pre.length = 8)
    (hpos : ∀ p ∈ pre, 0 < p) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    active omega N (rosserAncestor 3 pre) := by
  have hlen3 : (rosserAncestor 3 pre).length = 3 := by simp [hlen]
  have hpos3 : ∀ p ∈ rosserAncestor 3 pre, 0 < p := by
    intro p hp
    exact hpos p (List.mem_of_mem_drop hp)
  refine ⟨hlen3, ?_⟩
  rw [← rpow_primeHistoryLogCoordinates N hN hlen3 hpos3 (2 : Fin 3)]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  rw [firstThree_ancestor N pre hlen]
  exact homega.trans (P4AOriginalFull87SourceDictionary.source_basic hs).2.1.le

end
end ImbalancedChen.P4AOriginalFull87CommonHistoricalMesh
