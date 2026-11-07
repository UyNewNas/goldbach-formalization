import ImbalancedChen.P2OriginalSaving16TrimmedHistory
import ImbalancedChen.HistoricalThirdFallbackSupportP1
import ImbalancedChen.PrimeHistoryLogCoordinates

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The J cap mesh is not substituted for HistoricalThirdCoarse.rawLevel.
Here the ACTUAL old Gamma lookup is realized on all fourteen positive
trims. Its pair23 gate, selected joint-cell support, firstStop and four
strict histories are proved from the real source. No supported-third or
current-parent estimate is a premise. Old fallback and equality branches
outside this retained source keep their existing definitions.
-/
namespace ImbalancedChen.P2OriginalSaving16HistoricalMesh
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter VariableEnvelope HistoricalThirdCoarse
open P2OriginalAscendingEighthCapDictionary
open P2OriginalFourteenCausalHistoryMesh
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory

def firstThree (t : Point) : Fin 3 → ℝ := fun i => t ⟨i.val, by omega⟩

theorem source_ordered {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : Ordered (t 0) (t 1) (t 2) :=
  ⟨(h.coordinate_pos 2).le, (h.order (by decide : (1 : Fin 8) < 2)).le,
    (h.order (by decide : (0 : Fin 8) < 1)).le, h.largest.le⟩

theorem source_pair23_tent {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : v (t 1 + t 2) = R t := by
  rw [v_eq_min, min_eq_right h.old_descending.le]
  rfl

/-- This is the original nonleading-pair support margin, not an assumed
licence for the newly proposed scalar mesh. -/
theorem source_pair23_margin {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : 3 / 256 ≤ R t - (2 * t 0 + t 1 + t 2) := by
  have hbase : v (t 0) ≤ R t := by
    simpa [subsetSum] using old_tents_below_R planes t h.old_planes {0}
      (by simp [oldMasks])
  have hm := yz_gate_margin (source_ordered h)
    (hbase.trans_eq (source_pair23_tent h).symm)
  rw [source_pair23_tent h] at hm
  exact hm

private theorem side_widths {b : RationalBox} {chi : ℝ}
    (hw : (b.width : ℝ) ≤ chi) :
    (b.ux : ℝ) - b.lx ≤ chi ∧ (b.uy : ℝ) - b.ly ≤ chi ∧
      (b.uz : ℝ) - b.lz ≤ chi := by
  have hx : (b.ux : ℝ) - b.lx ≤ b.width := by exact_mod_cast b.coordinate_widths_le.1
  have hy : (b.uy : ℝ) - b.ly ≤ b.width := by exact_mod_cast b.coordinate_widths_le.2.1
  have hz : (b.uz : ℝ) - b.lz ≤ b.width := by exact_mod_cast b.coordinate_widths_le.2.2
  exact ⟨hx.trans hw, hy.trans hw, hz.trans hw⟩

/-- Actual whole-box yzGap survives a 7*chi endpoint debit. -/
theorem actual_pair23_box_gate {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (b : RationalBox) (e chi : ℝ)
    (hb : b.InBox (t 0) (t 1) (t 2)) (hw : (b.width : ℝ) ≤ chi)
    (hsmall : e + 7 * chi ≤ 3 / 256) : e ≤ yzGap b := by
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have hchi : 0 ≤ chi := (show (0 : ℝ) ≤ b.width by exact_mod_cast b.width_nonneg).trans hw
  have hA : R t ≤ A (t 1 + t 2) := h.old_descending.le
  have hC : R t = C (t 1 + t 2) := rfl
  have hv : R t - 3 * chi ≤ v ((b.uy : ℝ) + b.uz) := by
    rw [v_eq_min]
    apply le_min
    · dsimp [A] at hA ⊢
      linarith [hb.2.2.2.1, hb.2.2.2.2.2]
    · dsimp [C] at hC ⊢
      linarith [hb.2.2.1, hb.2.2.2.2.1]
  have hm := source_pair23_margin h
  dsimp [yzGap]
  linarith [hb.1, hb.2.2.1, hb.2.2.2.2.1]

/-- The old lookup itself approximates R, with its real 2e buffer. All
other original branches remain inside fullGamma and may still win. -/
theorem actual_gamma_sandwich {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) (b : RationalBox) (e chi : ℝ) (he : 0 ≤ e)
    (hb : b.InBox (t 0) (t 1) (t 2)) (hw : (b.width : ℝ) ≤ chi)
    (hfull : (b.ux : ℝ) ≤ mu - 4 * e)
    (hsmall : e + 7 * chi ≤ 3 / 256) :
    R t - (3 * chi + 2 * e) ≤ levelExponent e b ∧ levelExponent e b ≤ R t := by
  have hgate := actual_pair23_box_gate h b e chi hb hw hsmall
  have hq : qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ gamma e b := by
    rw [gamma, if_pos hfull]
    simp only [fullGamma, if_pos hgate]
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_right _ _))))
  have herr := rationalInterval_v_error
    (l := b.ly + b.lz) (u := b.uy + b.uz) (x := t 1 + t 2)
    (by push_cast; linarith [hb.2.2.1, hb.2.2.2.2.1])
    (by push_cast; linarith [hb.2.2.2.1, hb.2.2.2.2.2])
  rw [source_pair23_tent h] at herr
  push_cast at herr
  have hqr : (qVLo (b.ly + b.lz) (b.uy + b.uz) : ℝ) ≤ gamma e b := by
    exact_mod_cast hq
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have hup := gamma_le_endpoint e b he hb (source_ordered h).1
    (source_ordered h).2.1 (source_ordered h).2.2.1
  rw [endpoint, if_pos h.largest.le, h.originalThird_eq] at hup
  dsimp [levelExponent]
  constructor <;> linarith

theorem mesh_box_width (m : ℕ) (j : HistoricalThirdCoarse.Cell m) :
    ((box m j).width : ℝ) = logPrimeMeshStep 0 (19 / 96) m := by
  have hside (i : Fin 3) :
      qLogPrimeMeshHi 0 (19 / 96) m j i - qLogPrimeMeshLo 0 (19 / 96) m j i =
        (19 / 96 : ℚ) / (m + 1 : ℚ) := by
    simp only [qLogPrimeMeshHi, qLogPrimeMeshLo, qLogPrimeMeshPoint]
    push_cast
    ring
  have hp : (0 : ℚ) ≤ (19 / 96 : ℚ) / (m + 1 : ℚ) := by positivity
  simp only [RationalBox.width, box, hside, max_self, max_eq_right hp]
  simp [logPrimeMeshStep]

theorem mesh_box_lower_nonneg (m : ℕ) (j : HistoricalThirdCoarse.Cell m) :
    0 ≤ (box m j).lz := by
  dsimp [box, qLogPrimeMeshLo, qLogPrimeMeshPoint]
  positivity

/-- The additional margins needed by the original joint-cell selector.
J already proves the final historyGap positive on the actual source. -/
def realizationSlack (t : Point) : ℝ :=
  min (mu - t 0) (min (t 0 - t 1) (min (t 1 - t 2) (historyGap t)))

theorem realizationSlack_continuous : Continuous realizationSlack := by
  unfold realizationSlack
  exact (continuous_const.sub (continuous_apply 0)).min
    (((continuous_apply 0).sub (continuous_apply 1)).min
      (((continuous_apply 1).sub (continuous_apply 2)).min historyGap_continuous))

theorem realizationSlack_pos {planes : Finset (Fin 6) → Bool} {t : Point}
    (h : CellGuard planes t) : 0 < realizationSlack t := by
  exact lt_min (sub_pos.mpr h.largest)
    (lt_min (sub_pos.mpr (h.order (by decide : (0 : Fin 8) < 1)))
      (lt_min (sub_pos.mpr (h.order (by decide : (1 : Fin 8) < 2))) (historyGap_pos h)))

/-- One ORIGINAL historical mesh works for the whole actual14 trim, for
every sufficiently small buffer. m is fixed before N and every child.
No support, first-stop or desired history comparison is an input. -/
theorem exists_actual_historical_mesh (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℝ, 0 < e → e < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ e / 10 →
      ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m → ∀ t ∈ trimmedRegion delta,
        ∃ j ∈ cells e chi m,
          firstThree t ∈ logPrimeMeshCell 0 (19 / 96) m j ∧
          3 * t 0 < exponent e chi m (firstThree t) ∧
          oddCube t 2 < exponent e chi m (firstThree t) ∧
          oddCube t 4 < exponent e chi m (firstThree t) ∧
          oddCube t 6 < exponent e chi m (firstThree t) ∧
          R t - (3 * chi + 2 * e) ≤ exponent e chi m (firstThree t) ∧
          exponent e chi m (firstThree t) ≤ R t := by
  have hpos : ∀ t ∈ trimmedRegion delta, 0 < realizationSlack t := by
    intro t ht
    obtain ⟨i, hi, hc⟩ := region_selectedFamilyGuard
      (trimmedRegion_subset_region delta hdelta ht)
    exact realizationSlack_pos hc
  obtain ⟨a, ha, hfloor⟩ := (isCompact_trimmedRegion delta).exists_forall_le'
    realizationSlack_continuous.continuousOn hpos
  refine ⟨min a (3 / 256) / 20, by positivity, ?_⟩
  intro e he he0 chi hchi hchie
  have hea : 20 * e < a := by
    have hm := min_le_left a (3 / 256 : ℝ)
    linarith
  have hec : 20 * e < (3 / 256 : ℝ) := by
    have hm := min_le_right a (3 / 256 : ℝ)
    linarith
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hchi))
  refine ⟨m0, ?_⟩
  intro m hm t ht
  obtain ⟨i, hi, hc⟩ := region_selectedFamilyGuard
    (trimmedRegion_subset_region delta hdelta ht)
  have hslack := hfloor t ht
  change a ≤ min (mu - t 0) (min (t 0 - t 1) (min (t 1 - t 2) (historyGap t))) at hslack
  obtain ⟨hmu, h01, h12, hgap⟩ :=
    (show a ≤ mu - t 0 ∧ a ≤ t 0 - t 1 ∧ a ≤ t 1 - t 2 ∧ a ≤ historyGap t by
      simpa only [le_min_iff] using hslack)
  have hbox : firstThree t ∈ logPrimeBox (fun _ => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
    apply mem_logPrimeBox.mpr
    intro k
    have hkpos := hc.coordinate_pos (⟨k.val, by omega⟩ : Fin 8)
    have hkle : t ⟨k.val, by omega⟩ ≤ t 0 := by
      by_cases hk : k = 0
      · subst k; exact le_rfl
      · exact (hc.order (by have := k.isLt; omega)).le
    refine ⟨hkpos.le, ?_⟩
    change t ⟨k.val, by omega⟩ < _
    have hlargest := hc.largest
    dsimp [mu] at hlargest
    linarith
  obtain ⟨j, hjt⟩ := exists_logPrimeMeshCell 0 (19 / 96) m hbox
  have hb := inBox_of_cell hjt
  change (box m j).InBox (t 0) (t 1) (t 2) at hb
  have hw : ((box m j).width : ℝ) ≤ chi := by
    rw [mesh_box_width]
    exact (hm0 m hm).le
  obtain ⟨hx, hy, hz⟩ := side_widths hw
  have hfull : ((box m j).ux : ℝ) ≤ mu - 4 * e := by
    linarith [hb.1]
  have hj : j ∈ cells e chi m := by
    apply (mem_cells e chi m j).2
    refine ⟨RationalBox.wellFormed_of_inBox hb, mesh_box_lower_nonneg m j, ?_, ?_, ?_, hw⟩
    · have hh : ((box m j).uz : ℝ) ≤ (box m j).ly := by
        linarith [hb.2.2.2.1, hb.2.2.2.2.1]
      exact_mod_cast hh
    · have hh : ((box m j).uy : ℝ) ≤ (box m j).lx := by
        linarith [hb.2.1, hb.2.2.1]
      exact_mod_cast hh
    · have hstop : mu ≤ extendedFirstStop := by norm_num [mu, extendedFirstStop]
      linarith
  have hg := actual_gamma_sandwich hc (box m j) e chi he.le hb hw hfull (by linarith)
  have hhist : historyCeiling t < levelExponent e (box m j) := by
    dsimp [historyGap] at hgap
    linarith [hg.1]
  have hh := max_lt_iff.mp hhist
  have hh' := max_lt_iff.mp hh.2
  refine ⟨j, hj, hjt, ?_⟩
  rw [exponent_on_cell e chi m _ j hj hjt]
  exact ⟨hh.1, hh'.1, (max_lt_iff.mp hh'.2).1, (max_lt_iff.mp hh'.2).2, hg⟩

theorem firstThree_ancestor (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8) :
    primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) =
      firstThree (primeHistoryLogCoordinates N 8 pre) := by
  funext i
  exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) i

/-- The literal rough activation is supplied on this source whenever
omega is at most its original strict third cutoff. -/
theorem actual_third_active (omega N : ℝ) (hN : 1 < N) (homega : omega ≤ 1 / 100)
    (pre : List ℕ) (hlen : pre.length = 8) (hpos : ∀ p ∈ pre, 0 < p)
    {planes : Finset (Fin 6) → Bool}
    (hc : CellGuard planes (primeHistoryLogCoordinates N 8 pre)) :
    active omega N (rosserAncestor 3 pre) := by
  have hlen3 : (rosserAncestor 3 pre).length = 3 := by simp [hlen]
  have hpos3 : ∀ p ∈ rosserAncestor 3 pre, 0 < p := by
    intro p hp
    exact hpos p (List.mem_of_mem_drop hp)
  refine ⟨hlen3, ?_⟩
  rw [← rpow_primeHistoryLogCoordinates N hN hlen3 hpos3 (2 : Fin 3)]
  apply Real.rpow_le_rpow_of_exponent_le hN.le
  rw [firstThree_ancestor N pre hlen]
  exact homega.trans hc.third_activation.le

/-- Joint-cell membership proves the ORIGINAL upper-endpoint firstStop;
the merely pointwise first-cube inequality is not substituted for it. -/
theorem actual_firstStop_of_joint_cell (e chi N : ℝ) (m : ℕ)
    (pre : List ℕ) (hlen : pre.length = 8) (j : HistoricalThirdCoarse.Cell m)
    (hj : j ∈ cells e chi m)
    (ht : firstThree (primeHistoryLogCoordinates N 8 pre) ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    firstStop e m N (rosserAncestor 1 pre) := by
  have h0 := mem_logPrimeMeshCell.mp ht (0 : Fin 3)
  have hcoord := primeHistoryLogCoordinates_ancestor N hlen (by decide : 1 ≤ 8) (0 : Fin 1)
  have hs := ((mem_cells e chi m j).mp hj).2.2.2.2.1
  refine ⟨j 0, ?_, ?_, ?_⟩
  · simpa [firstThree, logPrimeMeshLo, hcoord] using h0.1
  · simpa [firstThree, logPrimeMeshHi, hcoord] using h0.2
  · simpa [box, qLogPrimeMeshHi] using hs

end
end ImbalancedChen.P2OriginalSaving16HistoricalMesh
