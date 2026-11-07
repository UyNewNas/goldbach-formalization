import ImbalancedChen.P4ASymmetricAboveMuSource
import ImbalancedChen.P4ASymmetricRange32RawOptionDispatch

/-! SOURCEONLY / UNCOMPILED / OPEN30.
Original first test x0>=M, including equality, selects fixed C(x). Only its
failure selects the below-mu B/six Range32 source dispatcher. Raw Option,
charged Option and box boundary suppression are separate concrete objects.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricAllMuDispatch

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdTriangleMomentsSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdSortedHalfIntegralSourceOnly
open OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ASymmetricFiniteDispatch
open OriginalThirdP4ASymmetricRawOptionOuterAssembly
open OriginalThirdP4ASymmetricRange32RawOptionDispatch
open OriginalThirdP4ASymmetricAboveMuSource
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open P4AOriginalMuSplitInvariantSourceOnly P4AOriginalSeedRange32InvariantSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalRange32MassCeil20261024zSourceOnly

local notation "D₀" => (48000*2^24:ℤ)

def allMuRawMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  if originalMuInteger ≤ x0 then aboveRawMeanOption table x0 x1 z0 z1 a b c d
  else rawMeanOption32 table x0 x1 z0 z1 a b c d

def allMuMeanCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  if originalMuInteger ≤ x0 then aboveMeanCost table x0 x1 z0 z1 a b c d
  else chargedMeanOption32 table x0 x1 z0 z1 a b c d

def allMuMassHi (x0 x1 z0 z1 : ℤ) : ℤ :=
  if originalMuInteger ≤ x0 then (literalSymmetricMass x0 x1 z0 z1).hi
  else (symmetricMass32 x0 x1 z0 z1).hi

def allMuCharge (x0 x1 z0 z1 high : ℤ) : ℤ :=
  up (high*allMuMassHi x0 x1 z0 z1) P160

theorem allMuCharge_above (x0 x1 z0 z1 high : ℤ) (h : originalMuInteger ≤ x0) :
    allMuCharge x0 x1 z0 z1 high = literalSymmetricUpper x0 x1 z0 z1 high := by
  simp only [allMuCharge,allMuMassHi,if_pos h,literalSymmetricUpper]

theorem allMuCharge_below (x0 x1 z0 z1 high : ℤ) (h : ¬originalMuInteger ≤ x0) :
    allMuCharge x0 x1 z0 z1 high = charge32 x0 x1 z0 z1 high := by
  simp only [allMuCharge,allMuMassHi,if_neg h,charge32]

/-- Equality M is above first; it never invokes the finite B/six selector. -/
theorem allMuRawMeanOption_at_mu (table : CheckedBlockTable) (x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    allMuRawMeanOption table originalMuInteger x1 z0 z1 a b c d =
      aboveRawMeanOption table originalMuInteger x1 z0 z1 a b c d := by
  simp only [allMuRawMeanOption,le_refl,if_true]

theorem allMuRawMeanOption_map (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    Option.map (allMuCharge x0 x1 z0 z1)
        (allMuRawMeanOption table x0 x1 z0 z1 a b c d) =
      allMuMeanCost table x0 x1 z0 z1 a b c d := by
  by_cases h : originalMuInteger ≤ x0
  · simp only [allMuRawMeanOption,allMuMeanCost,if_pos h]
    have he : allMuCharge x0 x1 z0 z1 = literalSymmetricUpper x0 x1 z0 z1 := by
      funext high
      exact allMuCharge_above x0 x1 z0 z1 high h
    rw [he]
    rfl
  · simp only [allMuRawMeanOption,allMuMeanCost,if_neg h]
    have he : allMuCharge x0 x1 z0 z1 = charge32 x0 x1 z0 z1 := by
      funext high
      exact allMuCharge_below x0 x1 z0 z1 high h
    rw [he]
    exact rawMeanOption32_map table x0 x1 z0 z1 a b c d

/-- Literal no-crossing gives exactly the needed physical branch, rather
than a caller's separate above/below analytic hypothesis. -/
theorem allMu_real_branch_guard (x0 x1 z0 z1 : ℤ) (a b : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1)) :
    if originalMuInteger ≤ x0 then VariableEnvelope.mu ≤ (a:ℝ)
    else (b:ℝ) ≤ VariableEnvelope.mu := by
  have h := original_cap_bounds_dispatch_guard (symmetricRaw x0 z0) (symmetricRaw x1 z1) hcross
  simpa [symmetricRaw,decodeCoordinates,coordinateDenominator,ha,hb] using h

/-- A concrete two-branch actual leaf theorem. The above supplier is fixed
C(x), the below supplier is the genuine B/six Range32 finite dispatcher.
No unit ratio, raw-log guard, factor query or leaf inequality is an input. -/
theorem allMu_cost_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcost : allMuMeanCost table x0 x1 z0 z1 a b c d=some cost) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤ value cost := by
  have hgMu := allMu_real_branch_guard x0 x1 z0 z1 a b ha hb hcross
  by_cases habove : originalMuInteger ≤ x0
  · rw [if_pos habove] at hgMu
    have hcst : aboveMeanCost table x0 x1 z0 z1 a b c d=some cost := by
      simpa only [allMuMeanCost,if_pos habove] using hcost
    exact above_cost_success_integer_upper table x0 x1 z0 z1 a b c d cost
      ha hb hc hd hg hgMu hr habove hcst
  · rw [if_neg habove] at hgMu
    have hcst : chargedMeanOption32 table x0 x1 z0 z1 a b c d=some cost := by
      simpa only [allMuMeanCost,if_neg habove] using hcost
    exact original_chargedMeanOption32_integer_upper table x0 x1 z0 z1 a b c d cost
      ha hb hc hd hg hgMu hcst

theorem allMu_raw_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (high : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hhigh : allMuRawMeanOption table x0 x1 z0 z1 a b c d=some high) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤
      value (allMuCharge x0 x1 z0 z1 high) := by
  have hcst : allMuMeanCost table x0 x1 z0 z1 a b c d=
      some (allMuCharge x0 x1 z0 z1 high) := by
    rw [← allMuRawMeanOption_map,hhigh]
    rfl
  exact allMu_cost_success_integer_upper table x0 x1 z0 z1 a b c d _
    ha hb hc hd hg hr hcross hcst

theorem allMuMassHi_nonneg (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1)) :
    0 ≤ allMuMassHi x0 x1 z0 z1 := by
  have hp := symmetric_positive hg
  have hmpos : 0 < prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) :=
    mul_pos (mul_pos (by norm_num) (triangleMass_pos hp.1 hg.width_xy))
      (div_pos (sub_pos.mpr hg.width_z) (mul_pos hp.2 (hp.2.trans hg.width_z)))
  have hgMu := allMu_real_branch_guard x0 x1 z0 z1 a b ha hb hcross
  by_cases habove : originalMuInteger ≤ x0
  · rw [if_pos habove] at hgMu
    have hm := (literal_symmetric_mass_encloses x0 x1 z0 z1 a b c d
      ha hb hc hd hg hgMu).2
    have hz : (0:ℤ) ≤ (literalSymmetricMass x0 x1 z0 z1).hi := by
      apply value_le_iff.mp
      simpa only [value_zero] using hmpos.le.trans hm
    simpa only [allMuMassHi,if_pos habove] using hz
  · rw [if_neg habove] at hgMu
    have hm := (symmetric_mass32_encloses x0 x1 z0 z1 a b c d
      ha hb hc hd hg (symmetric_ratio_le_32 hg hgMu)).2
    have hz : (0:ℤ) ≤ (symmetricMass32 x0 x1 z0 z1).hi := by
      apply value_le_iff.mp
      simpa only [value_zero] using hmpos.le.trans hm
    simpa only [allMuMassHi,if_neg habove] using hz

def allMuRawBoxMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then allMuRawMeanOption table x0 x1 z0 z1 a b c d else none

def allMuChargedBoxMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then allMuMeanCost table x0 x1 z0 z1 a b c d else none

theorem allMuRawBoxMeanOption_map (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    Option.map (allMuCharge x0 x1 z0 z1)
        (allMuRawBoxMeanOption table x0 x1 z0 z1 a b c d) =
      allMuChargedBoxMeanOption table x0 x1 z0 z1 a b c d := by
  classical
  by_cases h : sourceFull x1 z1
  · simp only [allMuRawBoxMeanOption,allMuChargedBoxMeanOption,if_pos h]
    exact allMuRawMeanOption_map table x0 x1 z0 z1 a b c d
  · simp only [allMuRawBoxMeanOption,allMuChargedBoxMeanOption,if_neg h,Option.map_none]

theorem allMu_box_cost_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcost : allMuChargedBoxMeanOption table x0 x1 z0 z1 a b c d=some cost) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤ value cost := by
  classical
  unfold allMuChargedBoxMeanOption at hcost
  split_ifs at hcost
  · exact allMu_cost_success_integer_upper table x0 x1 z0 z1 a b c d cost
      ha hb hc hd hg hr hcross hcost
  · cases hcost

theorem allMu_box_raw_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (high : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (hhigh : allMuRawBoxMeanOption table x0 x1 z0 z1 a b c d=some high) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤
      value (allMuCharge x0 x1 z0 z1 high) := by
  have hcst : allMuChargedBoxMeanOption table x0 x1 z0 z1 a b c d=
      some (allMuCharge x0 x1 z0 z1 high) := by
    rw [← allMuRawBoxMeanOption_map,hhigh]
    rfl
  exact allMu_box_cost_success_integer_upper table x0 x1 z0 z1 a b c d _
    ha hb hc hd hg hr hcross hcst

theorem allMuCharge_mono (x0 x1 z0 z1 h j : ℤ)
    (hm : 0 ≤ allMuMassHi x0 x1 z0 z1) (hh : h ≤ j) :
    allMuCharge x0 x1 z0 z1 h ≤ allMuCharge x0 x1 z0 z1 j := by
  unfold allMuCharge up
  exact neg_le_neg (Int.ediv_le_ediv P160_pos
    (neg_le_neg (mul_le_mul_of_nonneg_right hh hm)))

theorem allMuCharge_min (x0 x1 z0 z1 h j : ℤ)
    (hm : 0 ≤ allMuMassHi x0 x1 z0 z1) :
    allMuCharge x0 x1 z0 z1 (min h j) =
      min (allMuCharge x0 x1 z0 z1 h) (allMuCharge x0 x1 z0 z1 j) := by
  rcases le_total h j with hh | hh
  · rw [min_eq_left hh,min_eq_left (allMuCharge_mono x0 x1 z0 z1 h j hm hh)]
  · rw [min_eq_right hh,min_eq_right (allMuCharge_mono x0 x1 z0 z1 j h hm hh)]

def allMuSourceBoxUpper (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (fallbackHigh : ℤ) : ℤ :=
  allMuCharge x0 x1 z0 z1 (applyOptionalMean fallbackHigh
    (allMuRawBoxMeanOption table x0 x1 z0 z1 a b c d))

theorem allMuSourceBoxUpper_eq_charged_optional (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (hm : 0 ≤ allMuMassHi x0 x1 z0 z1) :
    allMuSourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      applyOptionalMean (allMuCharge x0 x1 z0 z1 fallbackHigh)
        (allMuChargedBoxMeanOption table x0 x1 z0 z1 a b c d) := by
  rw [← allMuRawBoxMeanOption_map]
  unfold allMuSourceBoxUpper
  cases hs : allMuRawBoxMeanOption table x0 x1 z0 z1 a b c d with
  | none => rfl
  | some high =>
      simp only [Option.map_some,applyOptionalMean]
      exact allMuCharge_min x0 x1 z0 z1 fallbackHigh high hm

theorem allMuSourceBoxUpper_eq_charged_optional_of_geometry (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hcross : noCrossMu originalMuInteger 0 (symmetricRaw x0 z0) (symmetricRaw x1 z1)) :
    allMuSourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      applyOptionalMean (allMuCharge x0 x1 z0 z1 fallbackHigh)
        (allMuChargedBoxMeanOption table x0 x1 z0 z1 a b c d) := by
  exact allMuSourceBoxUpper_eq_charged_optional table x0 x1 z0 z1 a b c d fallbackHigh
    (allMuMassHi_nonneg x0 x1 z0 z1 a b c d ha hb hc hd hg hcross)

theorem allMuSourceBoxUpper_boundary (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (hboundary : ¬sourceFull x1 z1) :
    allMuSourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      allMuCharge x0 x1 z0 z1 fallbackHigh := by
  simp only [allMuSourceBoxUpper,allMuRawBoxMeanOption,if_neg hboundary,applyOptionalMean]

end
end ImbalancedChen.OriginalThirdP4ASymmetricAllMuDispatch
