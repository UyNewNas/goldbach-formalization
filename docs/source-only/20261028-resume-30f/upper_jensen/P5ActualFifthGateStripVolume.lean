import ImbalancedChen.P5ActualFifthGateStripLocalization
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Five-dimensional coordinate Fubini for the ACTUAL fifth-mask gate rows.
Every allowed tent-minus-gate row has a coefficient of magnitude >=1/2
when the selected mask is nonempty. The empty mask has no pointwise
support core and is handled as such, not treated as a proper half wall.
-/
namespace ImbalancedChen.P5ActualFifthGateStripVolume
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1HistoricalFifthIndexedOwnerArchive P5ActualFifthGateStripLocalization

theorem actual_gap_half_coordinate (I : Finset (Fin 5)) (hI : I.Nonempty)
    (side : Bool) (g : Gate) (hg : gateAllowed I g = true) :
    ∃ k : Fin 5, (1 / 2 : ℝ) ≤ |((actualGap I (side, g)).coefficient k : ℝ)| := by
  cases g with
  | half =>
      obtain ⟨k, hk⟩ := hI
      refine ⟨k, ?_⟩
      cases side <;> norm_num [actualGap, tentPlane, gateAffine, halfGate,
        Affine5.sub, Affine5.add, constantAffine, indicatorAffine, hk]
  | full j =>
      refine ⟨j, ?_⟩
      by_cases hj : j ∈ I <;> cases side <;>
        norm_num [actualGap, tentPlane, gateAffine, fullGate, Affine5.sub,
          Affine5.add, constantAffine, indicatorAffine, hj]
  | selected j =>
      have hj : j ∉ I := of_decide_eq_true hg
      refine ⟨j, ?_⟩
      cases side <;> norm_num [actualGap, tentPlane, gateAffine, selectedGate,
        Affine5.sub, Affine5.add, constantAffine, indicatorAffine, hj]

private def unitBase : Set (Fin 4 → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)

private def cylinder (center : (Fin 4 → ℝ) → ℝ) (radius : ℝ) : Set (ℝ × (Fin 4 → ℝ)) :=
  {q | q.2 ∈ unitBase ∧ q.1 ∈ Icc (center q.2 - radius) (center q.2 + radius)}

private theorem cylinder_measurable (center : (Fin 4 → ℝ) → ℝ)
    (hc : Continuous center) (radius : ℝ) : MeasurableSet (cylinder center radius) := by
  have hbase : MeasurableSet unitBase := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  exact (hbase.preimage measurable_snd).inter
    ((measurableSet_le ((hc.comp continuous_snd).sub continuous_const).measurable
      measurable_fst).inter
      (measurableSet_le measurable_fst ((hc.comp continuous_snd).add continuous_const).measurable))

private theorem cylinder_volume (center : (Fin 4 → ℝ) → ℝ)
    (hc : Continuous center) (radius : ℝ) :
    volume (cylinder center radius) = ENNReal.ofReal (2 * radius) := by
  have hbase : MeasurableSet unitBase := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hb : volume unitBase = 1 := by simp [unitBase, volume_pi_pi, Real.volume_Icc]
  have hfiber (y : Fin 4 → ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) =
        unitBase.indicator (fun _ => ENNReal.ofReal (2 * radius)) y := by
    by_cases hy : y ∈ unitBase
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) =
          Icc (center y - radius) (center y + radius) := by ext x; simp [cylinder, hy]
      rw [heq, indicator_of_mem hy, Real.volume_Icc]
      congr 1
      ring
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) = ∅ := by ext x; simp [cylinder, hy]
      rw [heq, measure_empty, indicator_of_notMem hy]
  change (volume.prod volume) (cylinder center radius) = _
  rw [Measure.prod_apply_symm (cylinder_measurable center hc radius)]
  simp_rw [hfiber]
  rw [lintegral_indicator hbase]
  simp only [lintegral_const, Measure.restrict_apply_univ, hb, mul_one]

private def rest (a : Affine5) (j : Fin 5) (y : Fin 4 → ℝ) : ℝ :=
  (a.constant : ℝ) + ∑ k : Fin 4, (a.coefficient (j.succAbove k) : ℝ) * y k

private def center (a : Affine5) (j : Fin 5) (y : Fin 4 → ℝ) : ℝ :=
  -rest a j y / (a.coefficient j : ℝ)

private theorem eval_split (a : Affine5) (j : Fin 5) (t : Fin 5 → ℝ) :
    a.eval t = (a.coefficient j : ℝ) * t j + rest a j (fun k => t (j.succAbove k)) := by
  unfold Affine5.eval rest
  rw [Fin.sum_univ_succAbove _ j]
  ring

/-- Applied below only to the actual original tent-minus-gate bank. -/
theorem affine_half_gap_strip_volume (a : Affine5) (j : Fin 5) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hgap : (1 / 2 : ℝ) ≤ |(a.coefficient j : ℝ)|) :
    volume (unitCube ∩ {t | |a.eval t| ≤ delta}) ≤ ENNReal.ofReal (4 * delta) := by
  have hc : (a.coefficient j : ℝ) ≠ 0 :=
    abs_pos.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hgap)
  let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) j
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 5 => ℝ) j
  have hcenter : Continuous (center a j) := by unfold center rest; fun_prop
  have hsub : unitCube ∩ {t | |a.eval t| ≤ delta} ⊆ E ⁻¹' cylinder (center a j) (2 * delta) := by
    intro t ht
    have hfactor : a.eval t = (a.coefficient j : ℝ) *
        (t j - center a j (fun k => t (j.succAbove k))) := by
      rw [eval_split a j t]
      unfold center
      field_simp [hc]
      <;> ring
    have hprod : |(a.coefficient j : ℝ)| *
        |t j - center a j (fun k => t (j.succAbove k))| ≤ delta := by
      simpa only [hfactor, abs_mul] using ht.2
    have hdist : |t j - center a j (fun k => t (j.succAbove k))| ≤ 2 * delta := by
      have hmul := mul_le_mul_of_nonneg_right hgap
        (abs_nonneg (t j - center a j (fun k => t (j.succAbove k))))
      nlinarith only [hmul, hprod]
    change (t j, fun k => t (j.succAbove k)) ∈ cylinder (center a j) (2 * delta)
    refine ⟨fun k _ => ht.1 (j.succAbove k) (mem_univ _), ?_⟩
    have hd := abs_le.mp hdist
    exact ⟨by linarith only [hd.1], by linarith only [hd.2]⟩
  calc
    volume (unitCube ∩ {t | |a.eval t| ≤ delta}) ≤
        volume (E ⁻¹' cylinder (center a j) (2 * delta)) := measure_mono hsub
    _ = volume (cylinder (center a j) (2 * delta)) := by
      rw [← Measure.map_apply E.measurable (cylinder_measurable _ hcenter _)]
      exact congrArg (fun mu => mu (cylinder (center a j) (2 * delta))) hmp.map_eq
    _ = ENNReal.ofReal (4 * delta) := by rw [cylinder_volume _ hcenter]; congr 1; ring

theorem actual_gate_row_strip_volume (I : Finset (Fin 5)) (hI : I.Nonempty)
    (side : Bool) (g : Gate) (hg : gateAllowed I g = true) (delta : ℝ) (hd : 0 ≤ delta) :
    volume (unitCube ∩ {t | |(actualGap I (side, g)).eval t| ≤ delta}) ≤
      ENNReal.ofReal (4 * delta) := by
  obtain ⟨j, hj⟩ := actual_gap_half_coordinate I hI side g hg
  exact affine_half_gap_strip_volume _ j delta hd hj

/-- No owner/mesh count multiplies the bound: these are the fixed22
original affine gate pieces for the SAME saved source mask. -/
theorem actualGateStrips_volume (I : Finset (Fin 5)) (hI : I.Nonempty)
    (delta : ℝ) (hd : 0 ≤ delta) :
    volume (actualGateStrips I delta) ≤ ENNReal.ofReal (88 * delta) := by
  have hcard : Fintype.card Gate = 11 := by decide
  have heq : actualGateStrips I delta = ⋃ p : Bool × Gate,
      if gateAllowed I p.2 = true then unitCube ∩ {t | |(actualGap I p).eval t| ≤ delta} else ∅ := by
    ext t
    constructor
    · rintro ⟨ht, p, hp, hs⟩
      have hg : gateAllowed I p.2 = true := (Finset.mem_filter.mp hp).2
      exact mem_iUnion.mpr ⟨p, by simpa only [if_pos hg] using And.intro ht hs⟩
    · intro ht
      obtain ⟨p, hp⟩ := mem_iUnion.mp ht
      by_cases hg : gateAllowed I p.2 = true
      · rw [if_pos hg] at hp
        exact ⟨hp.1, p, by simp [gateRows, hg], hp.2⟩
      · rw [if_neg hg] at hp
        exact hp.elim
  have hp (p : Bool × Gate) :
      volume (if gateAllowed I p.2 = true then
        unitCube ∩ {t | |(actualGap I p).eval t| ≤ delta} else ∅) ≤ ENNReal.ofReal (4 * delta) := by
    by_cases hg : gateAllowed I p.2 = true
    · simpa only [if_pos hg] using actual_gate_row_strip_volume I hI p.1 p.2 hg delta hd
    · simp only [if_neg hg, measure_empty, zero_le]
  rw [heq]
  calc
    _ ≤ ∑ p : Bool × Gate, volume (if gateAllowed I p.2 = true then
        unitCube ∩ {t | |(actualGap I p).eval t| ≤ delta} else ∅) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _p : Bool × Gate, ENNReal.ofReal (4 * delta) := Finset.sum_le_sum (fun p _ => hp p)
    _ = (22 : ℝ≥0∞) * ENNReal.ofReal (4 * delta) := by simp [hcard, nsmul_eq_mul]
    _ = ENNReal.ofReal ((22 : ℝ) * (4 * delta)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 22)]
      norm_num
    _ = ENNReal.ofReal (88 * delta) := by congr 1; ring

theorem pointwiseSupport_empty_mask : pointwiseSupport (∅ : Finset (Fin 5)) = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have hh := ht .half rfl
  norm_num [candidate, envelope, gateAffine, halfGate_eval] at hh

/-- The actual support core has a true O(e+meshStep) volume rate for
EVERY archived source index, including empty/degenerate saved masks. -/
theorem rejectedSupportCore_volume (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) :
    volume (rejectedSupportCore i e q chi omega) ≤
      ENNReal.ofReal (88 * (2 * (e : ℝ) + 32 *
        (P1OriginalFifthQuantitativeGateRefinement.meshStepQ (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q) : ℝ))) := by
  by_cases hI : (maskSlots 5 (archiveRow i).mask.toNat).Nonempty
  · exact (measure_mono (rejectedSupportCore_subset_actual_strips i e he q chi omega)).trans
      (actualGateStrips_volume _ hI _ (by positivity))
  · have hz : maskSlots 5 (archiveRow i).mask.toNat = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hcore : rejectedSupportCore i e q chi omega = ∅ := by
      simp only [rejectedSupportCore, hz, pointwiseSupport_empty_mask, inter_empty]
    rw [hcore, measure_empty]
    exact zero_le _

end
end ImbalancedChen.P5ActualFifthGateStripVolume
