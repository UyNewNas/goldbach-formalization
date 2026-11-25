import ImbalancedChen.P2OriginalCompactQ80Symmetry

/-!
SOURCE ONLY / UNCOMPILED. Literal final selection and Q80 rounding.

The two analytic inputs are upstream sub-obligations: the lower gap candidate
pointwise, and each selected Jensen mean candidate before mass rounding.
Neither input asserts the desired whole enclose interval. The actual four
pre-Jensen upper candidates, mass and all zero exits are invoked internally.
The parent-owned CompleteSoundness must instantiate both inputs.
-/
namespace ImbalancedChen.P2OriginalCompactQ80SelectionSourceOnly

noncomputable section
open Set MeasureTheory
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactQ80SymmetrySourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly

theorem lowerDifference_nonnegative (box : RawBox) : 0 ≤ lowerDifference box := by
  unfold lowerDifference
  split_ifs <;> omega

theorem lowerDifference_value_nonnegative (box : RawBox) :
    0 ≤ val (lowerDifference box) := by
  simpa only [val_zero] using val_mono (lowerDifference_nonnegative box)

theorem lowerDifference_eq_zero_of_boundary (box : RawBox) (hi : ¬ inside box) :
    lowerDifference box = 0 := by
  simp [lowerDifference,hi]

/-- Product rounding is applied after halving the integer mass. In particular
no parity of mass.lo or mass.hi is assumed. -/
theorem lower_integer_product (box : RawBox) (g : Geometry box)
    (hLower : ∀ t ∈ rootCell box, val (lowerDifference box) ≤
      actualExtendedThirdLowerFactor (newArgument t)-
        actualExtendedThirdLowerFactor (actualOldArgument t)) :
    val (lowerDifference box*(chargedMass box).lo/scale) ≤
      ∫ t in rootCell box,compactKernel t := by
  by_cases hi : inside box
  · have hmass := ((contains_iff _ _).1 (chargedMass_contains box g)).1
    calc
      val (lowerDifference box*(chargedMass box).lo/scale) ≤
          val (lowerDifference box)*val (chargedMass box).lo := floor_product _ _
      _ ≤ val (lowerDifference box)*realChargedMass box :=
        mul_le_mul_of_nonneg_left hmass (lowerDifference_value_nonnegative box)
      _ ≤ ∫ t in rootCell box,compactKernel t :=
        integral_lower_of_pointwise box g hi _ hLower
  · rw [lowerDifference_eq_zero_of_boundary box hi]
    simpa [val] using actual_integral_nonnegative box g

/-- The Jensen port concerns the selected candidate's unrounded weighted
integral mean. Its nonnegativity follows from the true nonnegative integral
and positive geometric mass; no extra successful source assertion is used. -/
theorem selected_jensen_nonnegative (box : RawBox) (g : Geometry box) (j : ℤ)
    (hj : (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    0 ≤ val j := by
  have hn := actual_integral_nonnegative box g
  have hm := realChargedMass_pos box g
  exact nonneg_of_mul_nonneg_left (hn.trans hj) hm

/-- Keep the literal optional Jensen minimum. Even an unsorted/empty
candidate option does not silently initialize the minimum at zero. -/
theorem upperDifference_integral_from_jensen (box : RawBox) (g : Geometry box)
    (hJensen : ∀ j : ℤ, inside box → jensenDifferenceUpper box = some j →
      (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    (∫ t in rootCell box,compactKernel t) ≤
      val (upperDifference box)*realChargedMass box := by
  have hb := upperBeforeJensen_integral box g
  by_cases hi : inside box
  · cases hj : jensenDifferenceUpper box with
    | none => simpa only [upperDifference,if_pos hi,hj] using hb
    | some j =>
        have hJ := hJensen j hi hj
        rcases le_total (upperBeforeJensen box) j with h | h
        · simpa only [upperDifference,if_pos hi,hj,min_eq_left h] using hb
        · simpa only [upperDifference,if_pos hi,hj,min_eq_right h] using hJ
  · simpa only [upperDifference,if_neg hi] using hb

theorem upperDifference_nonnegative_from_jensen (box : RawBox) (g : Geometry box)
    (hJensen : ∀ j : ℤ, inside box → jensenDifferenceUpper box = some j →
      (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    0 ≤ val (upperDifference box) :=
  selected_jensen_nonnegative box g _ (upperDifference_integral_from_jensen box g hJensen)

theorem upper_integer_product (box : RawBox) (g : Geometry box)
    (hJensen : ∀ j : ℤ, inside box → jensenDifferenceUpper box = some j →
      (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    (∫ t in rootCell box,compactKernel t) ≤
      val (up (upperDifference box*(chargedMass box).hi) scale) := by
  have hmass := ((contains_iff _ _).1 (chargedMass_contains box g)).2
  calc
    (∫ t in rootCell box,compactKernel t) ≤
        val (upperDifference box)*realChargedMass box :=
      upperDifference_integral_from_jensen box g hJensen
    _ ≤ val (upperDifference box)*val (chargedMass box).hi :=
      mul_le_mul_of_nonneg_left hmass (upperDifference_nonnegative_from_jensen box g hJensen)
    _ ≤ val (up (upperDifference box*(chargedMass box).hi) scale) := ceiling_product _ _

/-- Exact original source exits, candidate minima, symmetric-half mass and
final integer lower/upper products. This is a composition theorem, not a
claim that the two remaining analytic candidate ports have been discharged. -/
theorem enclose_contains_from_candidates (box : RawBox) (g : Geometry box)
    (hLower : ∀ t ∈ rootCell box, val (lowerDifference box) ≤
      actualExtendedThirdLowerFactor (newArgument t)-
        actualExtendedThirdLowerFactor (actualOldArgument t))
    (hJensen : ∀ j : ℤ, inside box → jensenDifferenceUpper box = some j →
      (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  by_cases ho : outside box
  · exact outside_enclose_contains_integral box ho
  by_cases hc : thetaInteger ≤ (phiRange box).lo
  · exact fullCap_enclose_contains_integral box g hc
  by_cases hz : upperBeforeJensen box = 0
  · exact zeroLoss_enclose_contains_integral box g hz
  have he : enclose box =
      ⟨lowerDifference box*(chargedMass box).lo/scale,
        up (upperDifference box*(chargedMass box).hi) scale⟩ := by
    simp only [enclose,enclosureResult,if_neg ho,if_neg hc,if_neg hz]
  rw [he]
  exact ⟨lower_integer_product box g hLower,upper_integer_product box g hJensen⟩

/-- All boundary branches, INCLUDING equal-interval square boundary cells,
are now closed without any Jensen or lower-candidate port. -/
theorem boundary_enclose_contains_integral (box : RawBox) (g : Geometry box)
    (hi : ¬ inside box) :
    val (enclose box).lower ≤ (∫ t in rootCell box,compactKernel t) ∧
      (∫ t in rootCell box,compactKernel t) ≤ val (enclose box).upper := by
  apply enclose_contains_from_candidates box g
  · intro t ht
    rw [lowerDifference_eq_zero_of_boundary box hi,val_zero]
    exact actual_gap_nonnegative box g ht
  · intro j hinside _
    exact (hi hinside).elim

/-- The producer's final order assertion is a consequence of analytic
candidate soundness. It is never assumed to prove the enclosure. -/
theorem enclose_integer_order_from_candidates (box : RawBox) (g : Geometry box)
    (hLower : ∀ t ∈ rootCell box, val (lowerDifference box) ≤
      actualExtendedThirdLowerFactor (newArgument t)-
        actualExtendedThirdLowerFactor (actualOldArgument t))
    (hJensen : ∀ j : ℤ, inside box → jensenDifferenceUpper box = some j →
      (∫ t in rootCell box,compactKernel t) ≤ val j*realChargedMass box) :
    0 ≤ (enclose box).lower ∧ (enclose box).lower ≤ (enclose box).upper := by
  have hn : 0 ≤ (enclose box).lower := by
    by_cases ho : outside box
    · simp only [enclose_outside box ho]; exact le_rfl
    by_cases hc : thetaInteger ≤ (phiRange box).lo
    · simp only [enclose_fullCap box hc]; exact le_rfl
    by_cases hz : upperBeforeJensen box = 0
    · simp only [enclose_zeroLoss box hz]; exact le_rfl
    change 0 ≤ (enclosureResult box).bounds.lower
    simp only [enclosureResult,if_neg ho,if_neg hc,if_neg hz]
    exact Int.ediv_nonneg
      (mul_nonneg (lowerDifference_nonnegative box) (chargedMass_lower_nonnegative box g))
      scale_pos.le
  have h := enclose_contains_from_candidates box g hLower hJensen
  have ho := (div_le_div_iff_of_pos_right scale_real_pos).1 (h.1.trans h.2)
  exact ⟨hn,by exact_mod_cast ho⟩

end
end ImbalancedChen.P2OriginalCompactQ80SelectionSourceOnly
