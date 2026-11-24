import ImbalancedChen.P1OriginalFourthUniformRowMargins
import ImbalancedChen.P4AOriginalFull87GammaApproximation
import ImbalancedChen.P2OriginalSaving16HistoricalMesh
import ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
import ImbalancedChen.AffinePrimeGates

/-! SOURCE_ONLY / UNCOMPILED.
The complete original fourth bank has ONE pre-N historical mesh on every
positive interior trim. The actual gated Gamma and actual firstStop are
retained. Original numerical rectangles are not constant-cap labels.
-/
namespace ImbalancedChen.P1OriginalFourthCommonHistoricalMesh
noncomputable section
open scoped Classical Topology
open Set Filter MeasureTheory VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission P1OriginalFourthUniformRowMargins
open P4AOriginalFull87GammaApproximation
open P2OriginalSaving16HistoricalMesh (mesh_box_width mesh_box_lower_nonneg)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

def prefix3 (t : Point) : Fin 3 → ℝ := fun i => t i.castSucc

def trimmedBox (r : ProducerRow) (delta : ℝ) : Set Point :=
  {t | ∀ i, (r.lower i : ℝ) + delta ≤ t i ∧ t i ≤ (r.upper i : ℝ) - delta}

theorem trimmedBox_subset (r : ProducerRow) {delta : ℝ} (hd : 0 ≤ delta) :
    trimmedBox r delta ⊆ r.box := by
  intro t ht
  exact ⟨fun i => by linarith [(ht i).1], fun i => by linarith [(ht i).2]⟩

theorem trimmedBox_adjacent (r : ProducerRow) (hr : r ∈ originalRows4)
    (delta : ℝ) (t : Point) (ht : t ∈ trimmedBox r delta) (i : Fin 3) :
    t i.succ + 2 * delta ≤ t i.castSucc := by
  have ho := (originalRows4_geometry r hr).2.2.2.1 i
  have hR : (r.upper i.succ : ℝ) ≤ (r.lower i.castSucc : ℝ) := by
    have hh : (r.hi i.succ : ℝ) ≤ (r.lo i.castSucc : ℝ) := by exact_mod_cast ho
    simpa only [ProducerRow.upper, ProducerRow.lower, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat] using div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 204800)
  linarith [(ht i.succ).2, (ht i.castSucc).1]

theorem trimmedBox_strictAnti (r : ProducerRow) (hr : r ∈ originalRows4)
    {delta : ℝ} (hd : 0 < delta) (t : Point) (ht : t ∈ trimmedBox r delta) :
    StrictAnti t := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  linarith [trimmedBox_adjacent r hr delta t ht i]

/-- Positive trims exhaust the actual open row box. No positive part of
the interior is replaced by a smaller fixed numerical box.
-/
theorem exists_positive_trim_iff (r : ProducerRow) (t : Point) :
    (∃ delta : ℝ, 0 < delta ∧ t ∈ trimmedBox r delta) ↔
      ∀ i, (r.lower i : ℝ) < t i ∧ t i < (r.upper i : ℝ) := by
  constructor
  · rintro ⟨delta,hd,ht⟩ i
    exact ⟨by linarith [(ht i).1],by linarith [(ht i).2]⟩
  · intro ht
    let f : Fin 4 × Bool → ℝ := fun x =>
      if x.2 then (r.upper x.1 : ℝ)-t x.1 else t x.1-(r.lower x.1 : ℝ)
    let d : ℝ := (Finset.univ : Finset (Fin 4 × Bool)).inf'
      (show (Finset.univ : Finset (Fin 4 × Bool)).Nonempty from ⟨(0,false),Finset.mem_univ _⟩) f
    have hd : 0 < d := by
      apply (Finset.lt_inf'_iff _).mpr
      intro x _
      cases hx : x.2 <;> simp [f,hx] <;> linarith [(ht x.1).1,(ht x.1).2]
    have hL (i : Fin 4) : d ≤ t i-(r.lower i : ℝ) := by
      simpa [f] using
        (Finset.inf'_le f (Finset.mem_univ (i,false)))
    have hU (i : Fin 4) : d ≤ (r.upper i : ℝ)-t i := by
      simpa [f] using
        (Finset.inf'_le f (Finset.mem_univ (i,true)))
    exact ⟨d,hd,fun i => ⟨by linarith [hL i],by linarith [hU i]⟩⟩

/-- The omitted original row boundary consists of actual coordinate
walls and has zero volume. This reuses the existing affine-wall theorem.
-/
theorem ae_box_has_positive_trim (r : ProducerRow) :
    ∀ᵐ t ∂volume, t ∈ r.box → ∃ delta : ℝ, 0 < delta ∧ t ∈ trimmedBox r delta := by
  have hproj (i : Fin 4) : (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) h
    norm_num at hh
  have hl := ae_primeAffineGate_no_wall
    (fun i : Fin 4 => (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ))
    (fun i => (r.lower i : ℝ)) hproj
  have hu := ae_primeAffineGate_no_wall
    (fun i : Fin 4 => (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ))
    (fun i => (r.upper i : ℝ)) hproj
  filter_upwards [hl,hu] with t hl hu
  intro ht
  apply (exists_positive_trim_iff r t).mpr
  intro i
  constructor
  · rcases lt_or_eq_of_le (ht.1 i) with h | h
    · exact h
    · exact False.elim (hl i h.symm)
  · rcases lt_or_eq_of_le (ht.2 i) with h | h
    · exact h
    · exact False.elim (hu i h)

def commonE0 (delta : ℝ) : ℝ :=
  min delta (min commonMargin (min (3 / 256) (1 / 3200))) / 100

theorem commonE0_pos {delta : ℝ} (hd : 0 < delta) : 0 < commonE0 delta := by
  unfold commonE0
  exact div_pos (lt_min hd (lt_min commonMargin_pos (by norm_num))) (by norm_num)

theorem commonE0_bounds {delta e : ℝ} (he : e < commonE0 delta) :
    100 * e < delta ∧ 100 * e < commonMargin ∧
      100 * e < 3 / 256 ∧ 100 * e < 1 / 3200 := by
  have hm := min_le_left delta (min commonMargin (min (3 / 256 : ℝ) (1 / 3200)))
  have hM := (min_le_right delta (min commonMargin (min (3 / 256 : ℝ) (1 / 3200)))).trans
    (min_le_left commonMargin (min (3 / 256 : ℝ) (1 / 3200)))
  have hg := (min_le_right delta (min commonMargin (min (3 / 256 : ℝ) (1 / 3200)))).trans
    ((min_le_right commonMargin (min (3 / 256 : ℝ) (1 / 3200))).trans (min_le_left _ _))
  have ht := (min_le_right delta (min commonMargin (min (3 / 256 : ℝ) (1 / 3200)))).trans
    ((min_le_right commonMargin (min (3 / 256 : ℝ) (1 / 3200))).trans (min_le_right _ _))
  unfold commonE0 at he
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Uniform over ALL original rows, and every point of their positive
interior trims. Resolution is selected before the target and tuple.
The first and third own-cube margins are conclusions, not admissions.
-/
theorem exists_common_actual_mesh (delta : ℝ) (hd : 0 < delta)
    (e : ℝ) (he : 0 < e) (he0 : e < commonE0 delta)
    (chi : ℝ) (hchi : 0 < chi) (hchie : chi ≤ e / 20) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ r ∈ originalRows4, ∀ t : Point,
      t ∈ trimmedBox r delta →
      ∃ j ∈ cells e chi m,
        prefix3 t ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
        3 * t 0 < exponent e chi m (prefix3 t) ∧
        oldCube.eval t < exponent e chi m (prefix3 t) ∧
        oldCap t - ((9 / 2 : ℝ) * chi + 2 * e) ≤ exponent e chi m (prefix3 t) ∧
        exponent e chi m (prefix3 t) ≤ oldCap t := by
  obtain ⟨hed, heM, heg, het⟩ := commonE0_bounds he0
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hchi))
  refine ⟨m0, ?_⟩
  intro m hm r hr t ht
  have htbox := trimmedBox_subset r hd.le ht
  have ho := (r.ordered (originalRows4_geometry r hr) t htbox).1
  have htop : t 0 ≤ (39 / 200 : ℝ) := by
    have h := (originalRows4_geometry r hr).2.2.2.2.2.1
    have hR : (r.upper 0 : ℝ) ≤ (39 / 200 : ℝ) := by exact_mod_cast h
    exact (htbox.2 0).trans hR
  have hbox : prefix3 t ∈ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro k
    change 0 ≤ t k.castSucc ∧ t k.castSucc < (19 / 96 : ℝ)
    fin_cases k <;> dsimp <;> constructor <;> linarith [ho.1, ho.2.1, ho.2.2.1]
  obtain ⟨j, hjt⟩ := exists_logPrimeMeshCell 0 (19 / 96) m hbox
  have hb := inBox_of_cell hjt
  change (box m j).InBox (t 0) (t 1) (t 2) at hb
  have hw : ((box m j).width : ℝ) ≤ chi := by
    rw [mesh_box_width]
    exact (hm0 m hm).le
  obtain ⟨hx, hy, hz⟩ := P4AOriginalFull87GammaApproximation.side_widths hw
  have hfull : ((box m j).ux : ℝ) ≤ mu - 4 * e := by
    change ((box m j).ux : ℝ) ≤ (25 / 128 : ℝ) - 4 * e
    linarith [hb.1]
  have hj : j ∈ cells e chi m := by
    apply (mem_cells e chi m j).mpr
    refine ⟨RationalBox.wellFormed_of_inBox hb, mesh_box_lower_nonneg m j, ?_, ?_, ?_, hw⟩
    · have hgap := trimmedBox_adjacent r hr delta t ht 1
      have hh : ((box m j).uz : ℝ) ≤ (box m j).ly := by
        linarith [hb.2.2.2.1, hb.2.2.2.2.1]
      exact_mod_cast hh
    · have hgap := trimmedBox_adjacent r hr delta t ht 0
      have hh : ((box m j).uy : ℝ) ≤ (box m j).lx := by
        linarith [hb.2.1, hb.2.2.1]
      exact_mod_cast hh
    · have hh : mu ≤ extendedFirstStop := by norm_num [mu, extendedFirstStop]
      linarith
  have hg := P4AOriginalFull87GammaApproximation.actual_gamma_sandwich
    he.le ho hb hw hfull (by linarith : e + 7 * chi ≤ 3 / 256)
  have hcube := cube_gap r hr t htbox
  have hfirst := first_cube_margin e chi (box m j) he (by linarith)
    (by linarith) hw hb ((mem_cells e chi m j).mp hj).2.2.2.2.1
  refine ⟨j, hj, hjt, ?_⟩
  rw [exponent_on_cell e chi m _ j hj hjt]
  change oldCube.eval t + commonMargin ≤ six (t 0) (t 1) (t 2) at hcube
  exact ⟨hfirst, by linarith [hg.1], hg.1, hg.2⟩

/-- The actual common constructor uses m=475*q-1. Any requested lower
resolution thresholds are compatible with the SAME original mesh proof.
-/
theorem exists_common_actual_refined_mesh (delta : ℝ) (hd : 0 < delta)
    (e : ℝ) (he : 0 < e) (he0 : e < commonE0 delta)
    (chi : ℝ) (hchi : 0 < chi) (hchie : chi ≤ e / 20) (mMin qMin : ℕ) :
    ∃ q0 : ℕ, qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      mMin ≤ refinedMesh q ∧ ∀ r ∈ originalRows4, ∀ t : Point,
      t ∈ trimmedBox r delta →
      ∃ j ∈ cells e chi (refinedMesh q),
        prefix3 t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j ∧
        3 * t 0 < exponent e chi (refinedMesh q) (prefix3 t) ∧
        oldCube.eval t < exponent e chi (refinedMesh q) (prefix3 t) ∧
        oldCap t - ((9 / 2 : ℝ) * chi + 2 * e) ≤ exponent e chi (refinedMesh q) (prefix3 t) ∧
        exponent e chi (refinedMesh q) (prefix3 t) ≤ oldCap t := by
  obtain ⟨m0, hm0⟩ := exists_common_actual_mesh delta hd e he he0 chi hchi hchie
  refine ⟨max qMin (max (mMin + 1) (m0 + 1)), le_max_left _ _, ?_⟩
  intro q hq
  have hm : mMin ≤ refinedMesh q := by unfold refinedMesh; omega
  have h0 : m0 ≤ refinedMesh q := by unfold refinedMesh; omega
  exact ⟨hm, hm0 _ h0⟩

end
end ImbalancedChen.P1OriginalFourthCommonHistoricalMesh
