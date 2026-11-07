import ImbalancedChen.P2OriginalCompactQ80PhiBounds

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED.

Literal original lowerDifference. The raw pair is monotonicity plus the
actual max12 query theorem. The correlated pair uses the actual lower
factor's already proved concavity only where olo >= 2*z1. The old upper
argument and minimum increment are derived from phi_range's proved upper
endpoint, including all signed divisions and the original operand order.
No desired factor, leaf or integral estimate is assumed.
-/
namespace ImbalancedChen.P2OriginalCompactQ80PhiBoundsSourceOnly

noncomputable section
open Set
open Certificates.P2HistoricQ80DefectLookup
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly

def oldCeilingNumerator (box : RawBox) : ℤ :=
  (phiRange box).hi-box.1 0-box.1 1-box.1 2

def rawLower (box : RawBox) : ℤ :=
  max 0 ((point (thetaInteger-box.2 0-box.2 1-box.2 2) (box.2 2)).lo-
    (point (oldCeilingNumerator box) (box.1 2)).hi)

def pairedLowerNumerator (box : RawBox) : ℤ :=
  oldCeilingNumerator box*box.2 2+(thetaInteger-(phiRange box).hi)*box.1 2

def pairedLower (box : RawBox) : ℤ :=
  max 0 ((point (pairedLowerNumerator box) (box.1 2*box.2 2)).lo-
    (point (oldCeilingNumerator box) (box.1 2)).hi)

/-- Source `cap_hi` minus x0+y0 is positive wherever a point is queried.
The proof uses the already derived source residual and both true cap bounds;
this is not an extra source assertion or assumed phi estimate. -/
theorem upper_cap_residual_positive (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    0 < (phiRange box).hi-box.1 0-box.1 1 := by
  obtain ⟨hl,hh⟩ := phiRange_contains_actual_cap box g ht
  have hcR := (div_le_div_iff_of_pos_right denominator_real_pos).1 (hl.trans hh)
  have hc : (phiRange box).lo ≤ (phiRange box).hi := by exact_mod_cast hcR
  have hr := g.residual
  have hx := g.width 0
  have hy := g.width 1
  omega

/-- NEW's lower corner uses the positive residual before subtracting z.
The final numerator itself is allowed to have either sign. -/
theorem new_argument_ge_source_lower (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    ((thetaInteger-box.2 0-box.2 1-box.2 2 : ℤ) : ℝ)/(box.2 2 : ℝ) ≤
      newArgument t := by
  have hz : 0 < t 2 := (g.positive 2).trans_le (ht.2.1 2)
  have hz1 : (0 : ℝ) < box.2 2 := by
    exact_mod_cast (g.raw_positive 2).trans (g.width 2)
  have hn : 0 < thetaInteger-box.2 0-box.2 1 := by
    have hr := g.residual
    have hc := phiRange_lower_le_theta box
    omega
  have hN : 0 ≤ rawValue (thetaInteger-box.2 0-box.2 1) :=
    div_nonneg (by exact_mod_cast hn.le) denominator_real_pos.le
  have hnum : rawValue (thetaInteger-box.2 0-box.2 1) ≤
      thirdPrefixTheta-t 0-t 1 := by
    have hx := ht.2.2 0
    have hy := ht.2.2 1
    simp only [decode_eq_rawValue] at hx hy
    have he : rawValue (thetaInteger-box.2 0-box.2 1) =
        thirdPrefixTheta-rawValue (box.2 0)-rawValue (box.2 1) := by
      rw [←rawValue_theta]
      unfold rawValue
      push_cast
      ring
    rw [he]
    linarith only [hx,hy]
  have hfrac := (div_le_div_of_nonneg_left hN hz (ht.2.2 2)).trans
    (div_le_div_of_nonneg_right hnum hz.le)
  have heL : rawValue (thetaInteger-box.2 0-box.2 1)/decodeCoordinates box.2 2-1 =
      ((thetaInteger-box.2 0-box.2 1-box.2 2 : ℤ) : ℝ)/(box.2 2 : ℝ) := by
    rw [decode_eq_rawValue]
    unfold rawValue
    push_cast
    field_simp [denominator_real_pos.ne',hz1.ne'] <;> ring
  have heR : (thirdPrefixTheta-t 0-t 1)/t 2-1 = newArgument t := by
    unfold newArgument
    field_simp [hz.ne'] <;> ring
  rw [←heL,←heR]
  exact sub_le_sub_right hfrac 1

/-- OLD's upper corner is paid by the true phi upper endpoint. -/
theorem old_argument_le_source_ceiling (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    actualOldArgument t ≤ (oldCeilingNumerator box : ℝ)/(box.1 2 : ℝ) := by
  have hz : 0 < t 2 := (g.positive 2).trans_le (ht.2.1 2)
  have hz0 : (0 : ℝ) < box.1 2 := by exact_mod_cast g.raw_positive 2
  have hcap := cap_ceiling_on_actual_intersection box g ht
  have hN : 0 ≤ rawValue ((phiRange box).hi-box.1 0-box.1 1) :=
    div_nonneg (by exact_mod_cast (upper_cap_residual_positive box g ht).le)
      denominator_real_pos.le
  have hnum : actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1 ≤
      rawValue ((phiRange box).hi-box.1 0-box.1 1) := by
    have hx := ht.2.1 0
    have hy := ht.2.1 1
    simp only [decode_eq_rawValue] at hx hy
    have he : rawValue ((phiRange box).hi-box.1 0-box.1 1) =
        rawValue (phiRange box).hi-rawValue (box.1 0)-rawValue (box.1 1) := by
      unfold rawValue
      push_cast
      ring
    rw [he]
    linarith only [hcap,hx,hy]
  have hfrac := (div_le_div_of_nonneg_right hnum hz.le).trans
    (div_le_div_of_nonneg_left hN (g.positive 2) (ht.2.1 2))
  have heL : actualOldArgument t =
      (actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2)-t 0-t 1)/t 2-1 := by
    unfold actualOldArgument
    field_simp [hz.ne'] <;> ring
  have heR : rawValue ((phiRange box).hi-box.1 0-box.1 1)/decodeCoordinates box.1 2-1 =
      (oldCeilingNumerator box : ℝ)/(box.1 2 : ℝ) := by
    rw [decode_eq_rawValue]
    unfold rawValue oldCeilingNumerator
    push_cast
    field_simp [denominator_real_pos.ne',hz0.ne'] <;> ring
  rw [heL,←heR]
  exact sub_le_sub_right hfrac 1

/-- The smallest original increment is (Theta-cap_hi)/z1, with no
rounding moved inside or sign silently reversed. -/
theorem argument_gap_ge_source_delta (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    ((thetaInteger-(phiRange box).hi : ℤ) : ℝ)/(box.2 2 : ℝ) ≤
      newArgument t-actualOldArgument t := by
  have hz : 0 < t 2 := (g.positive 2).trans_le (ht.2.1 2)
  have hz1 : (0 : ℝ) < box.2 2 := by
    exact_mod_cast (g.raw_positive 2).trans (g.width 2)
  have hd : 0 ≤ thetaInteger-(phiRange box).hi :=
    sub_nonneg.mpr (phiRange_upper_le_theta box)
  have hN : 0 ≤ rawValue (thetaInteger-(phiRange box).hi) :=
    div_nonneg (by exact_mod_cast hd) denominator_real_pos.le
  have hnum : rawValue (thetaInteger-(phiRange box).hi) ≤
      thirdPrefixTheta-actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2) := by
    have he : rawValue (thetaInteger-(phiRange box).hi) =
        thirdPrefixTheta-rawValue (phiRange box).hi := by
      rw [←rawValue_theta]
      unfold rawValue
      push_cast
      ring
    rw [he]
    exact sub_le_sub_left (cap_ceiling_on_actual_intersection box g ht) _
  have hfrac := (div_le_div_of_nonneg_left hN hz (ht.2.2 2)).trans
    (div_le_div_of_nonneg_right hnum hz.le)
  have heL : rawValue (thetaInteger-(phiRange box).hi)/decodeCoordinates box.2 2 =
      ((thetaInteger-(phiRange box).hi : ℤ) : ℝ)/(box.2 2 : ℝ) := by
    rw [decode_eq_rawValue]
    unfold rawValue
    field_simp [denominator_real_pos.ne',hz1.ne']
  have heR : (thirdPrefixTheta-actualExtendedThirdBufferedCap 0 (t 0) (t 1) (t 2))/t 2 =
      newArgument t-actualOldArgument t := by
    unfold newArgument actualOldArgument
    ring
  rwa [heL,heR] at hfrac

theorem rawLower_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    val (rawLower box) ≤ actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) := by
  have hn := ((contains_iff _ _).1 (point_contains_actual
    (thetaInteger-box.2 0-box.2 1-box.2 2) (box.2 2)
    ((g.raw_positive 2).trans (g.width 2)))).1
  have ho := ((contains_iff _ _).1 (point_contains_actual
    (oldCeilingNumerator box) (box.1 2) (g.raw_positive 2))).2
  have hn' := hn.trans (monotone_actualExtendedThirdLowerFactor
    (new_argument_ge_source_lower box g ht))
  have ho' := (monotone_actualExtendedThirdLowerFactor
    (old_argument_le_source_ceiling box g ht)).trans ho
  rw [rawLower,val_max,val_zero,val_sub]
  exact max_le (actual_gap_nonnegative box g ht) (sub_le_sub hn' ho')

theorem pairedLower_query_argument (box : RawBox) (g : Geometry box) :
    (pairedLowerNumerator box : ℝ)/((box.1 2*box.2 2 : ℤ) : ℝ) =
      (oldCeilingNumerator box : ℝ)/(box.1 2 : ℝ)+
        ((thetaInteger-(phiRange box).hi : ℤ) : ℝ)/(box.2 2 : ℝ) := by
  have hz0 : (box.1 2 : ℝ) ≠ 0 := by exact_mod_cast (g.raw_positive 2).ne'
  have hz1 : (box.2 2 : ℝ) ≠ 0 := by
    exact_mod_cast ((g.raw_positive 2).trans (g.width 2)).ne'
  unfold pairedLowerNumerator
  push_cast
  field_simp [hz0,hz1] <;> ring

/-- Original correlated lower query: the literal threshold supplies the
concavity domain; the original cap upper supplies the minimum increment. -/
theorem pairedLower_pointwise (box : RawBox) (g : Geometry box)
    (hgate : 2*box.2 2 ≤ oldFloorNumerator box)
    {t : Point} (ht : t ∈ rootCell box) :
    val (pairedLower box) ≤ actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) := by
  let q : ℝ := (oldCeilingNumerator box : ℝ)/(box.1 2 : ℝ)
  let d : ℝ := ((thetaInteger-(phiRange box).hi : ℤ) : ℝ)/(box.2 2 : ℝ)
  have hz1 := (g.raw_positive 2).trans (g.width 2)
  have hz1R : (0 : ℝ) < box.2 2 := by exact_mod_cast hz1
  have hfloor : (2 : ℝ) ≤ (oldFloorNumerator box : ℝ)/(box.2 2 : ℝ) :=
    (le_div_iff₀ hz1R).2 (by exact_mod_cast hgate)
  have hold2 : 2 ≤ actualOldArgument t :=
    hfloor.trans (old_argument_ge_source_floor box g ht)
  have hold : actualOldArgument t ≤ q := old_argument_le_source_ceiling box g ht
  have hd : 0 ≤ d := div_nonneg
    (by exact_mod_cast sub_nonneg.mpr (phiRange_upper_le_theta box)) hz1R.le
  have hnew : actualOldArgument t+d ≤ newArgument t := by
    have h := argument_gap_ge_source_delta box g ht
    change d ≤ _ at h
    linarith only [h]
  have hanti := fixed_increment_antitone hold2 hold hd
  have hinc := sub_le_sub_right (monotone_actualExtendedThirdLowerFactor hnew)
    (actualExtendedThirdLowerFactor (actualOldArgument t))
  have hlo := ((contains_iff _ _).1 (point_contains_actual
    (pairedLowerNumerator box) (box.1 2*box.2 2) (mul_pos (g.raw_positive 2) hz1))).1
  have hhi := ((contains_iff _ _).1 (point_contains_actual
    (oldCeilingNumerator box) (box.1 2) (g.raw_positive 2))).2
  rw [pairedLower_query_argument box g] at hlo
  change _ ≤ actualExtendedThirdLowerFactor (q+d) at hlo
  change actualExtendedThirdLowerFactor q ≤ _ at hhi
  rw [pairedLower,val_max,val_zero,val_sub]
  exact max_le (actual_gap_nonnegative box g ht)
    ((sub_le_sub hlo hhi).trans (hanti.trans hinc))

theorem lowerDifference_source_formula (box : RawBox) :
    lowerDifference box =
      if inside box ∧ 2*box.2 2 ≤ oldFloorNumerator box then
        max (if inside box then rawLower box else 0) (pairedLower box)
      else if inside box then rawLower box else 0 := rfl

theorem lowerDifference_nonnegative (box : RawBox) : 0 ≤ lowerDifference box := by
  rw [lowerDifference_source_formula]
  split_ifs <;> simp only [rawLower,pairedLower] <;> omega

theorem lowerDifference_value_nonnegative (box : RawBox) : 0 ≤ val (lowerDifference box) := by
  simpa only [val_zero] using val_mono (lowerDifference_nonnegative box)

/-- Full literal original lowerDifference bound, including both inside
branches and the zero boundary branch. No internal estimate is a premise.
This pointwise theorem deliberately leaves the ordered/symmetric mass
integration to the independent selection companion. -/
theorem lowerDifference_pointwise (box : RawBox) (g : Geometry box)
    {t : Point} (ht : t ∈ rootCell box) :
    val (lowerDifference box) ≤ actualExtendedThirdLowerFactor (newArgument t)-
      actualExtendedThirdLowerFactor (actualOldArgument t) := by
  rw [lowerDifference_source_formula]
  by_cases hi : inside box
  · simp only [hi,true_and,if_true]
    by_cases hg : 2*box.2 2 ≤ oldFloorNumerator box
    · rw [if_pos hg,val_max]
      exact max_le (rawLower_pointwise box g ht) (pairedLower_pointwise box g hg ht)
    · rw [if_neg hg]
      exact rawLower_pointwise box g ht
  · simp only [hi,false_and,if_false,val_zero]
    exact actual_gap_nonnegative box g ht

end
end ImbalancedChen.P2OriginalCompactQ80PhiBoundsSourceOnly
