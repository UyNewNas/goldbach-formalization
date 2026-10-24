import ImbalancedChen.Part4ActualThirdOriginalClosedSplitAggregation
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Proposed installation: ImbalancedChen.P4AOriginalZeroLeafSuppliers.

Actual original zero-charge branches, using the literal compactRegion and
compactKernel. Closed cutoff and ordering equality cases are null faces,
not empty boxes. The imported coordinate_face_volume_zero is reused rather
than reproved. The old-cube kernel identity is also reused at equality.

The pointwise kernel lemma proves that an old argument <=2 forces BOTH
lower factors to vanish, using the actual cap <= original root. A new
argument <=2 alone does not imply zero correction and is not used as such.
Another branch proves zero correction when the actual envelope lies above
the original root, so the literal cap equals that root.

No integral-zero premise, alternate kernel/domain, final K premise, numeric
replay, finite-tree witness, arrays, query foundation or split propagation.
-/

namespace ImbalancedChen.P4AOriginalZeroLeafSuppliersSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdCompactPartitionSourceOnly

/-- Any subset of an actual coordinate face has zero actual kernel integral.
No measurability or integrability is imported from a numerical supplier. -/
theorem integral_compactKernel_eq_zero_of_coordinate_face {s : Set Point}
    (j : Fin 3) (q : ℝ) (hs : s ⊆ {t : Point | t j = q}) :
    (∫ t in s, compactKernel t) = 0 := by
  have hz : volume s = 0 := measure_mono_null hs (coordinate_face_volume_zero j q)
  change (∫ t, compactKernel t ∂volume.restrict s) = 0
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

/-- The closed endpoint b_z=1/100 leaves a null face, not an empty set. -/
theorem integral_eq_zero_of_box_below_cutoff {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hcut : b 2 ≤ (1 / 100 : ℝ)) :
    (∫ t in s, compactKernel t) = 0 := by
  apply integral_compactKernel_eq_zero_of_coordinate_face 2 (1 / 100)
  intro t ht
  have hc := hs ht
  exact le_antisymm ((hc.2.2 2).trans hcut) hc.1.2

/-- Likewise a_x=rho can leave the original outer coordinate face. -/
theorem integral_eq_zero_of_box_above_rho {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hrho : thirdPrefixRho ≤ a 0) :
    (∫ t in s, compactKernel t) = 0 := by
  apply integral_compactKernel_eq_zero_of_coordinate_face 0 thirdPrefixRho
  intro t ht
  have hc := hs ht
  exact le_antisymm hc.1.1.1.2.2.2.2 (hrho.trans (hc.2.1 0))

/-- If b_x<=a_y, ordering y<=x pins x to a_y, including equality. -/
theorem integral_eq_zero_of_box_xy_order {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hxy : b 0 ≤ a 1) :
    (∫ t in s, compactKernel t) = 0 := by
  apply integral_compactKernel_eq_zero_of_coordinate_face 0 (a 1)
  intro t ht
  have hc := hs ht
  have hyx : t 1 ≤ t 0 := hc.1.1.1.2.2.2.1
  exact le_antisymm ((hc.2.2 0).trans hxy) ((hc.2.1 1).trans hyx)

/-- If b_y<=a_z, ordering z<=y pins y to a_z, including equality. -/
theorem integral_eq_zero_of_box_yz_order {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hyz : b 1 ≤ a 2) :
    (∫ t in s, compactKernel t) = 0 := by
  apply integral_compactKernel_eq_zero_of_coordinate_face 1 (a 2)
  intro t ht
  have hc := hs ht
  have hzy : t 2 ≤ t 1 := hc.1.1.1.2.2.1
  exact le_antisymm ((hc.2.2 1).trans hyz) ((hc.2.1 2).trans hzy)

/-- A collapsed or reversed physical coordinate also has zero charge. -/
theorem integral_eq_zero_of_box_coordinate {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (j : Fin 3) (hj : b j ≤ a j) :
    (∫ t in s, compactKernel t) = 0 := by
  apply integral_compactKernel_eq_zero_of_coordinate_face j (a j)
  intro t ht
  have hc := hs ht
  exact le_antisymm ((hc.2.2 j).trans hj) (hc.2.1 j)

/-- The true old clamp branch: the actual cap bound makes the new argument
no larger than the old one, so both actual lower factors vanish. -/
theorem orderedKernel_eq_zero_of_old_argument_le_two {x y z : ℝ}
    (hz : 0 < z)
    (hold : (thirdPrefixTheta - x - y - z) / z ≤ 2) :
    actualExtendedThirdOrderedKernel 0 x y z = 0 := by
  have hcap : actualExtendedThirdBufferedCap 0 x y z ≤ thirdPrefixTheta := by
    simpa only [actualExtendedThirdBufferedCap, mul_zero, sub_zero] using
      thirdPrefixBufferedCap_le_root 0 (actualExtendedThirdEnvelope x y z)
  have hold' : thirdPrefixTheta - x - y - z ≤ 2 * z :=
    (div_le_iff₀ hz).mp hold
  have hnew : (actualExtendedThirdBufferedCap 0 x y z - x - y - z) / z ≤ 2 :=
    (div_le_iff₀ hz).mpr (by linarith)
  simp only [actualExtendedThirdOrderedKernel, mul_zero, sub_zero,
    actualExtendedThirdLowerFactor_of_le_two hold,
    actualExtendedThirdLowerFactor_of_le_two hnew, sub_self, mul_zero, zero_div]

/-- The original strict gated kernel returns zero at and beyond its old
cube gate, for arbitrary buffer and coordinates. -/
theorem gatedKernel_eq_zero_of_old_gate {e x y z : ℝ}
    (hgate : thirdPrefixTheta - 2 * e ≤ x + y + 3 * z) :
    actualExtendedThirdGatedKernel e x y z = 0 := by
  exact if_neg (not_lt.mpr hgate)

/-- A box entirely beyond the old gate can meet compactRegion on its old
cube face. The actual existing pointwise kernel theorem pays that face. -/
theorem integral_eq_zero_of_box_old_gate {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hgate : thirdPrefixTheta ≤ a 0 + a 1 + 3 * a 2) :
    (∫ t in s, compactKernel t) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have hc := hs ht
  have hz : 0 < t 2 := hc.1.1.1.1
  have hupper : t 0 + t 1 + 3 * t 2 ≤ thirdPrefixTheta := by
    simpa only [mul_zero, sub_zero] using hc.1.1.2
  have hx : a 0 ≤ t 0 := hc.2.1 0
  have hy : a 1 ≤ t 1 := hc.2.1 1
  have hzt : a 2 ≤ t 2 := hc.2.1 2
  have hface : t 0 + t 1 + 3 * t 2 = thirdPrefixTheta - 2 * (0 : ℝ) := by
    nlinarith
  exact actualExtendedThirdOrderedKernel_eq_zero_on_oldCube hz hface

/-- The same zero-charge conclusion from a local old-argument clamp bound,
with actual positivity obtained internally from the compact domain. -/
theorem integral_eq_zero_of_box_old_argument {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (hold : ∀ t ∈ Icc a b,
      (thirdPrefixTheta - t 0 - t 1 - t 2) / t 2 ≤ 2) :
    (∫ t in s, compactKernel t) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have hc := hs ht
  exact orderedKernel_eq_zero_of_old_argument_le_two hc.1.1.1.1 (hold t hc.2)

/-- Literal min-cap cancellation, rather than assuming any integral zero. -/
theorem orderedKernel_eq_zero_of_root_le_envelope {x y z : ℝ}
    (henv : thirdPrefixTheta ≤ actualExtendedThirdEnvelope x y z) :
    actualExtendedThirdOrderedKernel 0 x y z = 0 := by
  have hcap : actualExtendedThirdBufferedCap 0 x y z = thirdPrefixTheta := by
    simp only [actualExtendedThirdBufferedCap, thirdPrefixBufferedCap,
      mul_zero, sub_zero, min_eq_left henv]
  simp only [actualExtendedThirdOrderedKernel, mul_zero, sub_zero, hcap,
    sub_self, mul_zero, zero_div]

theorem integral_eq_zero_of_box_root_le_envelope {a b : Point}
    {s : Set Point} (hs : s ⊆ compactRegion ∩ Icc a b)
    (henv : ∀ t ∈ Icc a b,
      thirdPrefixTheta ≤ actualExtendedThirdEnvelope (t 0) (t 1) (t 2)) :
    (∫ t in s, compactKernel t) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  exact orderedKernel_eq_zero_of_root_le_envelope (henv t (hs ht).2)

/-- Direct binding to the real-estimate/integer-charge relation consumed by
the aggregation module. The hypotheses are actual geometric early returns;
none assumes the leaf integral vanishes. -/
theorem zero_charge_supplier_of_geometry {a b : Point} {s : Set Point}
    (hs : s ⊆ compactRegion ∩ Icc a b)
    (hbranch : b 2 ≤ (1 / 100 : ℝ) ∨ thirdPrefixRho ≤ a 0 ∨
      b 0 ≤ a 1 ∨ b 1 ≤ a 2 ∨ ∃ j : Fin 3, b j ≤ a j) :
    (∫ t in s, compactKernel t) ≤ (0 : ℝ) ∧
      (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / 2^80 := by
  have hz : (∫ t in s, compactKernel t) = 0 := by
    rcases hbranch with h | h | h | h | ⟨j, h⟩
    · exact integral_eq_zero_of_box_below_cutoff hs h
    · exact integral_eq_zero_of_box_above_rho hs h
    · exact integral_eq_zero_of_box_xy_order hs h
    · exact integral_eq_zero_of_box_yz_order hs h
    · exact integral_eq_zero_of_box_coordinate hs j h
  exact ⟨hz.le, by norm_num⟩

theorem zero_charge_supplier_of_old_gate {a b : Point} {s : Set Point}
    (hs : s ⊆ compactRegion ∩ Icc a b)
    (hgate : thirdPrefixTheta ≤ a 0 + a 1 + 3 * a 2) :
    (∫ t in s, compactKernel t) ≤ (0 : ℝ) ∧
      (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / 2^80 := by
  exact ⟨(integral_eq_zero_of_box_old_gate hs hgate).le, by norm_num⟩

theorem zero_charge_supplier_of_root_le_envelope {a b : Point} {s : Set Point}
    (hs : s ⊆ compactRegion ∩ Icc a b)
    (henv : ∀ t ∈ Icc a b,
      thirdPrefixTheta ≤ actualExtendedThirdEnvelope (t 0) (t 1) (t 2)) :
    (∫ t in s, compactKernel t) ≤ (0 : ℝ) ∧
      (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / 2^80 := by
  exact ⟨(integral_eq_zero_of_box_root_le_envelope hs henv).le, by norm_num⟩

end
end ImbalancedChen.P4AOriginalZeroLeafSuppliersSourceOnly
