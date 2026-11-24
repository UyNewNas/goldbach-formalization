import ImbalancedChen.P2OriginalSixthCompactTrim
import ImbalancedChen.P4AOriginalFull87GammaApproximation
import ImbalancedChen.P2OriginalSaving16HistoricalMesh
import ImbalancedChen.P4AOriginalElevenFifthComparison

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Actual HistoricalThirdCoarse Gamma lookup on every ORIGINAL G7 compact
trim. Only the arbitrary3D-box Gamma theorem is reused from the existing
file named Full87; no87-source or rank8 admissibility is used. One mesh
threshold works for all eleven original6D trims, before N or any tuple.
-/
namespace ImbalancedChen.P4AOriginalElevenHistoricalMesh
noncomputable section
open Set Filter MeasureTheory VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthCompactTrim (trim trim_margins trim_subset_source)
open P4AOriginalFull87GammaApproximation (side_widths actual_gamma_sandwich)
open P2OriginalSaving16HistoricalMesh (mesh_box_width mesh_box_lower_nonneg)
open HistoricalThirdCoarse (box cells exponent exponent_on_cell mem_cells inBox_of_cell)
open Certificates.P2OriginalSixthElevenLogSemantics (PhysicalCell R0 H3 H5 S6)
abbrev Physical := Fin 6 → ℝ
abbrev SourceCell := Certificates.P2OriginalSixthElevenLogSemantics.Cell

def firstThree (t : Physical) : Fin 3 → ℝ := fun j => t (j.castLE (by decide))

theorem source_ordered {c : SourceCell} {t : Physical} (hc : PhysicalCell c t) :
    Ordered (t 0) (t 1) (t 2) :=
  ⟨(hc.coordinates_pos 2).le,hc.order.2.2.2.1.le,hc.order.2.2.2.2.le,hc.largest.le⟩

/-- The old FIRST-THREE source is R0 for every G7 family, including
pair17/pair12 whose raw fifth comparison is strictly larger. -/
theorem source_six_eq_R0 {c : SourceCell} {t : Physical} (hc : PhysicalCell c t) :
    six (t 0) (t 1) (t 2)=R0 t := by
  have htents := hc.third_envelope.2.1
  simp_rw [P4AOriginalElevenFifthComparison.tent_eq_v] at htents
  have h1 := htents 1 (by decide)
  have h3 := htents 3 (by decide)
  have h7 := htents 7 (by decide)
  have h5 := htents 5 (by decide)
  have h6 := htents 6 (by decide)
  norm_num [Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,
    Certificates.P2OriginalSixthElevenLogSemantics.bit,Fin.sum_univ_succ] at h1 h3 h7 h5 h6
  have hB : B (t 2) ≤ R0 t := by
    have he : B (t 2)=Certificates.P2OriginalSixthElevenLogSemantics.W t := by
      dsimp [B,cap,Certificates.P2OriginalSixthElevenLogSemantics.W]
      ring
    rw [he]
    exact hc.oldW
  apply le_antisymm (max_le h1 (max_le h3 (max_le h7 (max_le hB (max_le h5 h6)))))
  have he : v (t 0)=R0 t := by rw [v_eq_A hc.largest.le]; rfl
  rw [← he]
  exact le_max_left _ _

theorem source_whole_first_margin {c : SourceCell} {t : Physical} (hc : PhysicalCell c t) :
    3/256 ≤ R0 t-3*t 0 := by
  have hh := hc.largest.le
  dsimp [R0,Certificates.P2OriginalSixthElevenLogSemantics.mu] at hh ⊢
  linarith

/-- Wholly ordered closed coarse owner, closed upper-endpoint first stop,
and actual buffered Gamma margins are CONCLUSIONS from the original trim.
No supported ancestor, assumed approximation or history licence is input. -/
theorem exists_original_G7_historical_mesh (delta : ℝ) (hdelta : 0<delta) :
    ∃ e0 : ℝ, 0<e0 ∧ ∀ e : ℝ, 0<e → e<e0 →
    ∀ chi : ℝ, 0<chi → chi≤e/10 → ∃ m0 : ℕ, ∀ m : ℕ, m0≤m →
    ∀ i : Fin 11, ∀ t : Physical, t∈trim i delta →
      ∃ j ∈ cells e chi m, firstThree t∈logPrimeMeshCell 0 (19/96) m j ∧
        3*t 0<exponent e chi m (firstThree t) ∧
        H3 t<exponent e chi m (firstThree t) ∧
        H5 t<exponent e chi m (firstThree t) ∧
        t 5<exponent e chi m (firstThree t)-S6 t ∧
        R0 t-((9/2:ℝ)*chi+2*e)≤exponent e chi m (firstThree t) ∧
        exponent e chi m (firstThree t)≤R0 t := by
  refine ⟨min delta (3/256)/20,by positivity,?_⟩
  intro e he he0 chi hchi hchie
  have hed : 20*e<delta := by have hh := min_le_left delta (3/256:ℝ); linarith
  have heg : 20*e<(3/256:ℝ) := by have hh := min_le_right delta (3/256:ℝ); linarith
  obtain ⟨m0,hm0⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19/96)).eventually (gt_mem_nhds hchi))
  refine ⟨m0,?_⟩
  intro m hm i t ht
  have hc := trim_subset_source i hdelta ht
  have ho := source_ordered hc
  obtain ⟨hmu,h01,h12,hh3,hh5,hres⟩ := trim_margins ht
  change delta≤mu-t 0 at hmu
  have ht1 : t 1≤t 0 := hc.order.2.2.2.2.le
  have ht2 : t 2≤t 0 := hc.order.2.2.2.1.le.trans ht1
  have hamb : firstThree t∈logPrimeBox (fun _ : Fin 3 => (0:ℝ)) (fun _ => (19/96:ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro k
    fin_cases k
    · exact ⟨(hc.coordinates_pos 0).le,hc.largest.trans_lt (by norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu])⟩
    · exact ⟨(hc.coordinates_pos 1).le,ht1.trans_lt (hc.largest.trans_lt (by norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu]))⟩
    · exact ⟨(hc.coordinates_pos 2).le,ht2.trans_lt (hc.largest.trans_lt (by norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu]))⟩
  obtain ⟨j,hjt⟩ := exists_logPrimeMeshCell 0 (19/96) m hamb
  have hb := inBox_of_cell hjt
  change (box m j).InBox (t 0) (t 1) (t 2) at hb
  have hw : ((box m j).width:ℝ)≤chi := by rw [mesh_box_width]; exact (hm0 m hm).le
  obtain ⟨hx,hy,hz⟩ := side_widths hw
  have hfull : ((box m j).ux:ℝ)≤mu-4*e := by linarith [hb.1]
  have hj : j∈cells e chi m := by
    apply (mem_cells e chi m j).mpr
    refine ⟨RationalBox.wellFormed_of_inBox hb,mesh_box_lower_nonneg m j,?_,?_,?_,hw⟩
    · have hh : ((box m j).uz:ℝ)≤(box m j).ly := by
        linarith [hb.2.2.2.1,hb.2.2.2.2.1]
      exact_mod_cast hh
    · have hh : ((box m j).uy:ℝ)≤(box m j).lx := by linarith [hb.2.1,hb.2.2.1]
      exact_mod_cast hh
    · have hh : mu≤extendedFirstStop := by norm_num [mu,extendedFirstStop]
      linarith
  have hsmall : e+7*chi≤3/256 := by linarith
  have hg := actual_gamma_sandwich he.le ho hb hw hfull hsmall
  rw [source_six_eq_R0 hc] at hg
  refine ⟨j,hj,hjt,?_⟩
  rw [exponent_on_cell e chi m _ j hj hjt]
  have herr : ((9/2:ℝ)*chi+2*e)<delta := by linarith
  have herr' : ((9/2:ℝ)*chi+2*e)<3/256 := by linarith
  have hfirst := source_whole_first_margin hc
  exact ⟨by linarith [hg.1],by linarith [hg.1],by linarith [hg.1],
    by linarith [hg.1],hg.1,hg.2⟩

end
end ImbalancedChen.P4AOriginalElevenHistoricalMesh
