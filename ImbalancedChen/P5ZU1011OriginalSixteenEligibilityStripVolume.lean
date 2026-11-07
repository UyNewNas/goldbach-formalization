import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityGridCompleteness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Quantitative volume of the actual original16 eligibility strips

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual rational margin coefficients lie on the eighth-integer lattice.
Properness of the SAME original eligibility wall therefore gives a real
coordinate coefficient of absolute value at least 1/8. Fubini in that
coordinate encloses each strip by a fiber interval of length 16*delta.

There are 16*11*2 possible policy/gate/side indices. Restricting to the
actual Required predicate only decreases their union. Thus its volume in
the unit four-cube is at most 5632*delta. The preceding actual uncertain
box containment gives volume at most 135168*meshWidth, and its genuine
prime-harmonic reciprocal density pays the further explicit factor
(5000/417)^4 on the original cube.

No volume, boundary-mass, coefficient-gap, or cell-bound premise is used
as a supplier. No H248 knot strips or stored endpoint checks are involved.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityStripVolume

noncomputable section

open Set MeasureTheory BoxCertificates EligibilityGridCertificates U11Integral
open P2OriginalFourthCapProducerInterface
open scoped BigOperators

/-- This exact gap is the eighth-lattice fact specialized to the actual
finite circuit, not an assumed nonzero-coordinate estimate. -/
theorem coefficient_zero_or_eighth (p : Policy) (left : Bool) (g : Gate) (i : Fin 4) :
    (margin p left g).coefficient i = 0 ∨
      (1 / 8 : ℝ) ≤ |((margin p left g).coefficient i : ℝ)| := by
  cases g <;> by_cases hp : p.val < 15 <;> cases left <;>
    simp [margin, capPiece, halfPiece, fullSquarePiece, selectedSquarePiece,
      wExtraPiece, wXSlack, Affine.sub, hp] <;>
    split_ifs <;> norm_num

theorem exists_eighth_coordinate (p : Policy) (left : Bool) (g : Gate) (hg : Required p g) :
    ∃ i : Fin 4, (1 / 8 : ℝ) ≤ |((margin p left g).coefficient i : ℝ)| := by
  have hex : ∃ i : Fin 4, (margin p left g).coefficient i ≠ 0 := by
    by_contra hn
    have hz (i : Fin 4) : (margin p left g).coefficient i = 0 :=
      not_ne_iff.mp ((not_exists.mp hn) i)
    have hconst (v : LogFour) :
        (margin p left g).eval v = ((margin p left g).constant : ℝ) := by
      simp [Affine.eval, hz]
    have hzero := margin_eq_actual_wall p left g hg (0 : LogFour)
    rw [hconst] at hzero
    simp only [map_zero] at hzero
    apply actual_wall_ne_zero p left g hg
    ext v
    have hv := margin_eq_actual_wall p left g hg v
    rw [hconst] at hv
    simp only [ContinuousLinearMap.zero_apply]
    linarith only [hzero, hv]
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, (coefficient_zero_or_eighth p left g i).resolve_left hi⟩

def unitCube : Set LogFour := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)
def unitBase : Set (Fin 3 → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) 1)

private def cylinder (center : (Fin 3 → ℝ) → ℝ) (radius : ℝ) : Set (ℝ × (Fin 3 → ℝ)) :=
  {q | q.2 ∈ unitBase ∧ q.1 ∈ Icc (center q.2 - radius) (center q.2 + radius)}

private theorem cylinder_measurable (center : (Fin 3 → ℝ) → ℝ)
    (hc : Continuous center) (radius : ℝ) : MeasurableSet (cylinder center radius) := by
  have hbase : MeasurableSet unitBase := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  exact (hbase.preimage measurable_snd).inter
    ((measurableSet_le ((hc.comp continuous_snd).sub continuous_const).measurable
      measurable_fst).inter
      (measurableSet_le measurable_fst ((hc.comp continuous_snd).add continuous_const).measurable))

private theorem cylinder_volume (center : (Fin 3 → ℝ) → ℝ)
    (hc : Continuous center) (radius : ℝ) :
    volume (cylinder center radius) = ENNReal.ofReal (2 * radius) := by
  have hbase : MeasurableSet unitBase := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hvolbase : volume unitBase = 1 := by
    simp [unitBase, volume_pi_pi, Real.volume_Icc]
  have hfiber (y : Fin 3 → ℝ) :
      volume ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) =
        unitBase.indicator (fun _ => ENNReal.ofReal (2 * radius)) y := by
    by_cases hy : y ∈ unitBase
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) =
          Icc (center y - radius) (center y + radius) := by
        ext x
        simp [cylinder, hy]
      rw [heq, indicator_of_mem hy, Real.volume_Icc]
      congr 1
      ring
    · have heq : ((fun x : ℝ => (x, y)) ⁻¹' cylinder center radius) = ∅ := by
        ext x
        simp [cylinder, hy]
      rw [heq, measure_empty, indicator_of_notMem hy]
  change (volume.prod volume) (cylinder center radius) = _
  rw [Measure.prod_apply_symm (cylinder_measurable center hc radius)]
  simp_rw [hfiber]
  rw [lintegral_indicator hbase]
  simp only [lintegral_const, Measure.restrict_apply_univ, hvolbase, mul_one]

private def rest (a : Affine) (j : Fin 4) (y : Fin 3 → ℝ) : ℝ :=
  (a.constant : ℝ) + ∑ k : Fin 3, (a.coefficient (j.succAbove k) : ℝ) * y k

private def center (a : Affine) (j : Fin 4) (y : Fin 3 → ℝ) : ℝ :=
  -rest a j y / (a.coefficient j : ℝ)

private theorem eval_split (a : Affine) (j : Fin 4) (v : LogFour) :
    a.eval v = (a.coefficient j : ℝ) * v j + rest a j (fun k => v (j.succAbove k)) := by
  unfold Affine.eval rest
  rw [Fin.sum_univ_succAbove _ j]
  ring

/-- Coordinate Fubini with the derived 1/8 coefficient gap. This helper
is used only with actual original margins in the public strip theorem. -/
private theorem affine_strip_volume (a : Affine) (j : Fin 4) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hgap : (1 / 8 : ℝ) ≤ |(a.coefficient j : ℝ)|) :
    volume (unitCube ∩ {v | |a.eval v| ≤ delta}) ≤ ENNReal.ofReal (16 * delta) := by
  have hc : (a.coefficient j : ℝ) ≠ 0 := by
    have hp : 0 < |(a.coefficient j : ℝ)| := lt_of_lt_of_le (by norm_num) hgap
    exact abs_pos.mp hp
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) j
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) j
  have hcenter : Continuous (center a j) := by unfold center rest; fun_prop
  have hsub : unitCube ∩ {v | |a.eval v| ≤ delta} ⊆
      e ⁻¹' cylinder (center a j) (8 * delta) := by
    intro v hv
    have hfactor : a.eval v = (a.coefficient j : ℝ) *
        (v j - center a j (fun k => v (j.succAbove k))) := by
      rw [eval_split a j v]
      unfold center
      field_simp [hc]
      <;> ring
    have hprod : |(a.coefficient j : ℝ)| *
        |v j - center a j (fun k => v (j.succAbove k))| ≤ delta := by
      simpa only [hfactor, abs_mul] using hv.2
    have hdist : |v j - center a j (fun k => v (j.succAbove k))| ≤ 8 * delta := by
      have hmul := mul_le_mul_of_nonneg_right hgap
        (abs_nonneg (v j - center a j (fun k => v (j.succAbove k))))
      nlinarith only [hmul, hprod]
    change (v j, fun k => v (j.succAbove k)) ∈ cylinder (center a j) (8 * delta)
    refine ⟨?_, ?_⟩
    · intro k hk
      exact hv.1 (j.succAbove k) (Set.mem_univ _)
    · have hd := abs_le.mp hdist
      exact ⟨by linarith only [hd.1], by linarith only [hd.2]⟩
  calc
    volume (unitCube ∩ {v | |a.eval v| ≤ delta}) ≤
        volume (e ⁻¹' cylinder (center a j) (8 * delta)) := measure_mono hsub
    _ = volume (cylinder (center a j) (8 * delta)) := by
      rw [← Measure.map_apply e.measurable (cylinder_measurable _ hcenter _)]
      exact congrArg (fun mu => mu (cylinder (center a j) (8 * delta))) hmp.map_eq
    _ = ENNReal.ofReal (16 * delta) := by
      rw [cylinder_volume _ hcenter]
      congr 1
      ring

def strip (p : Policy) (left : Bool) (g : Gate) (delta : ℝ) : Set LogFour :=
  unitCube ∩ {v | |(margin p left g).eval v| ≤ delta}

theorem required_strip_is_actual_wall (p : Policy) (left : Bool) (g : Gate)
    (hg : Required p g) (delta : ℝ) :
    strip p left g delta = unitCube ∩
      {v | |wall p left g v - wallOffset p left g| ≤ delta} := by
  ext v
  simp only [strip, mem_inter_iff, mem_setOf_eq, margin_eq_actual_wall p left g hg v]
  rw [abs_sub_comm]

theorem required_strip_volume (p : Policy) (left : Bool) (g : Gate)
    (hg : Required p g) (delta : ℝ) (hdelta : 0 ≤ delta) :
    volume (strip p left g delta) ≤ ENNReal.ofReal (16 * delta) := by
  obtain ⟨j, hj⟩ := exists_eighth_coordinate p left g hg
  exact affine_strip_volume _ j delta hdelta hj

abbrev StripIndex := Policy × Gate × Bool

def actualStripUnion (delta : ℝ) : Set LogFour :=
  ⋃ t : StripIndex, if Required t.1 t.2.1 then strip t.1 t.2.2 t.2.1 delta else ∅

theorem actualStripUnion_volume (delta : ℝ) (hdelta : 0 ≤ delta) :
    volume (actualStripUnion delta) ≤ ENNReal.ofReal (5632 * delta) := by
  have hcard : Fintype.card Gate = 11 := by decide
  have hbound (t : StripIndex) :
      volume (if Required t.1 t.2.1 then strip t.1 t.2.2 t.2.1 delta else ∅) ≤
        ENNReal.ofReal (16 * delta) := by
    by_cases hg : Required t.1 t.2.1
    · simpa only [if_pos hg] using required_strip_volume t.1 t.2.2 t.2.1 hg delta hdelta
    · simp only [if_neg hg, measure_empty, zero_le]
  calc
    volume (actualStripUnion delta) ≤ ∑ t : StripIndex,
        volume (if Required t.1 t.2.1 then strip t.1 t.2.2 t.2.1 delta else ∅) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ _t : StripIndex, ENNReal.ofReal (16 * delta) := Finset.sum_le_sum (fun t _ => hbound t)
    _ = (352 : ℝ≥0∞) * ENNReal.ofReal (16 * delta) := by
      simp [StripIndex, Policy, hcard, nsmul_eq_mul]
    _ = ENNReal.ofReal ((352 : ℝ) * (16 * delta)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 352)]
      norm_num
    _ = ENNReal.ofReal (5632 * delta) := by congr 1; ring

def originalCube : Set LogFour :=
  Set.univ.pi (fun _ => Icc (417 / 5000 : ℝ) (59 / 250 : ℝ))

theorem originalCube_subset_unitCube : originalCube ⊆ unitCube := by
  intro v hv i hi
  have h := hv i hi
  constructor <;> linarith only [h.1, h.2]

def boxUnion {I : Type*} (s : Finset I) (B : I → Box) : Set LogFour :=
  originalCube ∩ ⋃ i ∈ s, (B i).region

/-- Arbitrary overlaps are permitted; no disjoint-grid or scheduling
premise is needed to pay an uncertain region's actual geometric mass. -/
theorem undecided_boxUnion_subset_strips {I : Type*} (s : Finset I)
    (p : I → Policy) (B : I → Box) (h : ℝ)
    (hboxes : ∀ i ∈ s, WidthLe (B i) h ∧
      correlatedEligibleTest (p i) (B i) = false ∧
        correlatedIneligibleTest (p i) (B i) = false) :
    boxUnion s B ⊆ actualStripUnion (24 * h) := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.mp hv.2
  obtain ⟨g, hg, left, hproper, hstrip⟩ :=
    uncertain_box_in_actual_proper_strip (p i) (B i) h
      (hboxes i hi).1 (hboxes i hi).2.1 (hboxes i hi).2.2
  apply mem_iUnion.mpr
  refine ⟨(p i, g, left), ?_⟩
  simp only [if_pos hg]
  rw [required_strip_is_actual_wall _ _ _ hg]
  exact ⟨originalCube_subset_unitCube hv.1, hstrip v hvi⟩

theorem undecided_boxUnion_volume {I : Type*} (s : Finset I)
    (p : I → Policy) (B : I → Box) (h : ℝ) (hh : 0 ≤ h)
    (hboxes : ∀ i ∈ s, WidthLe (B i) h ∧
      correlatedEligibleTest (p i) (B i) = false ∧
        correlatedIneligibleTest (p i) (B i) = false) :
    volume (boxUnion s B) ≤ ENNReal.ofReal (135168 * h) := by
  have hsub := undecided_boxUnion_subset_strips s p B h hboxes
  have hvol := actualStripUnion_volume (24 * h) (mul_nonneg (by norm_num) hh)
  have heq : (5632 : ℝ) * (24 * h) = 135168 * h := by ring
  exact (measure_mono hsub).trans (heq ▸ hvol)

def harmonicWeight (v : LogFour) : ℝ := ∏ i : Fin 4, 1 / v i

theorem harmonicWeight_abs_le {v : LogFour} (hv : v ∈ originalCube) :
    |harmonicWeight v| ≤ (5000 / 417 : ℝ) ^ 4 := by
  have hpos (i : Fin 4) : 0 < v i :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 417 / 5000) (hv i (mem_univ _)).1
  have hnonneg : 0 ≤ harmonicWeight v :=
    Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (hpos i)).le)
  rw [abs_of_nonneg hnonneg]
  calc
    harmonicWeight v ≤ ∏ _i : Fin 4, (5000 / 417 : ℝ) := by
      apply Finset.prod_le_prod (fun i _ => (one_div_pos.mpr (hpos i)).le)
      intro i hi
      have h := one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 417 / 5000) (hv i (mem_univ _)).1
      norm_num at h
      exact h
    _ = (5000 / 417 : ℝ) ^ 4 := by simp

/-- The genuine original reciprocal prime-log density pays the same
uncertainty region, with an explicit constant independent of the mesh. -/
theorem undecided_boxUnion_harmonic_integral {I : Type*} (s : Finset I)
    (p : I → Policy) (B : I → Box) (h : ℝ) (hh : 0 ≤ h)
    (hboxes : ∀ i ∈ s, WidthLe (B i) h ∧
      correlatedEligibleTest (p i) (B i) = false ∧
        correlatedIneligibleTest (p i) (B i) = false) :
    |∫ v in boxUnion s B, harmonicWeight v| ≤
      ((5000 / 417 : ℝ) ^ 4 * 135168) * h := by
  have hvol := undecided_boxUnion_volume s p B h hh hboxes
  have hfinite : volume (boxUnion s B) < ∞ := hvol.trans_lt ENNReal.ofReal_lt_top
  have hreal : volume.real (boxUnion s B) ≤ 135168 * h := by
    have hR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    simpa only [Measure.real, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hh)] using hR
  have hn := norm_setIntegral_le_of_norm_le_const hfinite
    (fun v hv => by
      rw [Real.norm_eq_abs]
      exact harmonicWeight_abs_le hv.1)
  rw [Real.norm_eq_abs] at hn
  have hbound := hn.trans (mul_le_mul_of_nonneg_left hreal
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5000 / 417) 4))
  convert hbound using 1 <;> ring

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityStripVolume
