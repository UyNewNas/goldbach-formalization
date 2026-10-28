import ImbalancedChen.P2Author512EnhancedOrdinaryIntegral
import ImbalancedChen.P2HistoricI80DivisionSoundness

/-!
SOURCE ONLY; UNCOMPILED; ZERO FORMAL CREDIT.

The actual h-to-mu author-512 rectangles have five possible chord planes.
Their affine widths depend only on the two literal mesh steps, not on the
512^2 cell indices or any stored output. Exact rational identities put each
width above one Q80 ulp. The imported directed-division theorem converts
that bound to the literal I80.point lower-integer guard. We then specialize
the preceding enhanced ordinary integral theorem with no geometric or
chord-denominator premises. Eligibility remains the original source test.
-/

namespace ImbalancedChen.P2Author512EnhancedChordDomain

noncomputable section

open Set MeasureTheory
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2Author512EnhancedPairCell
open P2Author512EnhancedPairCellActualBindings
open P2Author512EnhancedOrdinaryIntegral

/-- These are the literal enhanced h-to-mu and shared a-to-h steps.
They are distinct from the old nonenhanced mu-to-d pair512 width. -/
def tStep : ℚ := (mu-h)/authorPairs
def uStep : ℚ := (h-a)/authorPairs

theorem tStep_pos : 0 < tStep := by
  norm_num [tStep,mu,h,authorPairs]

theorem uStep_pos : 0 < uStep := by
  norm_num [uStep,h,a,authorPairs]

/-- Actual decoded rational edges, including the source's successor index.
No row lookup, floating point width or numerical grid checker is used. -/
theorem actual_box_edges (i j : Fin authorPairs) :
    (enhancedL6Box i j).tl = h + (i.val:ℚ)*tStep ∧
    (enhancedL6Box i j).tr = h + ((i.val:ℚ)+1)*tStep ∧
    (enhancedL6Box i j).ul = a + (j.val:ℚ)*uStep ∧
    (enhancedL6Box i j).ur = a + ((j.val:ℚ)+1)*uStep := by
  simp [enhancedL6Box,uLeft,uRight,tStep,uStep,Nat.cast_add,Nat.cast_one]

theorem actual_box_widths (i j : Fin authorPairs) :
    (enhancedL6Box i j).tr - (enhancedL6Box i j).tl = tStep ∧
    (enhancedL6Box i j).ur - (enhancedL6Box i j).ul = uStep := by
  rcases actual_box_edges i j with ⟨htl,htr,hul,hur⟩
  rw [htl,htr,hul,hur]
  constructor <;> ring

/-- Geometry of every actual enhanced rectangle is supplied from the
positive rational mesh steps; it is no longer an input to the integral. -/
theorem actual_box_positive_ordered (i j : Fin authorPairs) :
    0 < (enhancedL6Box i j).tl ∧
    0 < (enhancedL6Box i j).ul ∧
    (enhancedL6Box i j).tl ≤ (enhancedL6Box i j).tr ∧
    (enhancedL6Box i j).ul ≤ (enhancedL6Box i j).ur := by
  rcases actual_box_edges i j with ⟨htl,htr,hul,hur⟩
  have hi : (0:ℚ) ≤ (i.val:ℚ) := Nat.cast_nonneg _
  have hj : (0:ℚ) ≤ (j.val:ℚ) := Nat.cast_nonneg _
  have hbase : (0:ℚ) < h := by norm_num [h]
  have abase : (0:ℚ) < a := by norm_num [a]
  have hdt := tStep_pos
  have hdu := uStep_pos
  rw [htl,htr,hul,hur]
  constructor
  · exact add_pos_of_pos_of_nonneg hbase (mul_nonneg hi hdt.le)
  constructor
  · exact add_pos_of_pos_of_nonneg abase (mul_nonneg hj hdu.le)
  constructor <;> nlinarith

/-- In the strictly negative-slope case the source's signed-corner
selector has this exact width. The constant plane coefficient cancels. -/
theorem negative_plane_width (p : Plane) (b : PairBox)
    (hb : p.b < 0) (hd : p.d < 0) :
    (affineRange p b.tl b.tr b.ul b.ur).2 -
      (affineRange p b.tl b.tr b.ul b.ur).1 =
      (-p.b)*(b.tr-b.tl) + (-p.d)*(b.ur-b.ul) := by
  simp only [affineRange,if_neg (not_le.mpr hb),if_neg (not_le.mpr hd)]
  ring

/-- The five literal widths. The same physical box is used on both sides;
the endpoint winner, h bank and saved floor do not enter this identity. -/
theorem actual_five_affine_widths (i j : Fin authorPairs) :
    (affineRange ordinaryPlane₀
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
      (affineRange ordinaryPlane₀
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1 = (1/2)*tStep+uStep ∧
    (affineRange ordinaryPlane₁
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
      (affineRange ordinaryPlane₁
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1 = (5/2)*tStep+uStep ∧
    (affineRange enhancedPlane₀
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
      (affineRange enhancedPlane₀
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1 = (1/2)*tStep+(1/2)*uStep ∧
    (affineRange enhancedPlane₁
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
      (affineRange enhancedPlane₁
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1 = (5/2)*tStep+(5/2)*uStep ∧
    (affineRange singletonPlane
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
      (affineRange singletonPlane
      (enhancedL6Box i j).tl (enhancedL6Box i j).tr
      (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1 = tStep+uStep := by
  have hw := actual_box_widths i j
  have hw0 := negative_plane_width ordinaryPlane₀ (enhancedL6Box i j)
    (by norm_num [ordinaryPlane₀]) (by norm_num [ordinaryPlane₀])
  have hw1 := negative_plane_width ordinaryPlane₁ (enhancedL6Box i j)
    (by norm_num [ordinaryPlane₁]) (by norm_num [ordinaryPlane₁])
  have he0 := negative_plane_width enhancedPlane₀ (enhancedL6Box i j)
    (by norm_num [enhancedPlane₀]) (by norm_num [enhancedPlane₀])
  have he1 := negative_plane_width enhancedPlane₁ (enhancedL6Box i j)
    (by norm_num [enhancedPlane₁]) (by norm_num [enhancedPlane₁])
  have hs := negative_plane_width singletonPlane (enhancedL6Box i j)
    (by norm_num [singletonPlane]) (by norm_num [singletonPlane])
  simp only [hw.1,hw.2,ordinaryPlane₀,ordinaryPlane₁,
    enhancedPlane₀,enhancedPlane₁,singletonPlane] at hw0 hw1 he0 he1 hs
  norm_num at hw0 hw1 he0 he1 hs
  exact ⟨hw0,hw1,he0,he1,hs⟩

/-- Closed rational comparisons of the five fixed mesh widths with Q80.
These are proof terms proposed for the compiler; no evaluator was run. -/
theorem five_widths_one_ulp :
    1/(Q:ℚ) ≤ (1/2)*tStep+uStep ∧
    1/(Q:ℚ) ≤ (5/2)*tStep+uStep ∧
    1/(Q:ℚ) ≤ (1/2)*tStep+(1/2)*uStep ∧
    1/(Q:ℚ) ≤ (5/2)*tStep+(5/2)*uStep ∧
    1/(Q:ℚ) ≤ tStep+uStep := by
  norm_num [Q,tStep,uStep,mu,h,a,authorPairs]

/-- Every literal candidate plane has a positive directed denominator,
including candidates later rejected by the source eligibility test. -/
theorem actual_alternative_denominator_guard (i j : Fin authorPairs)
    (pc : Plane × Option Plane) (hmem : pc ∈ alternatives (enhancedL6Box i j)) :
    0 < (I80.point
      ((affineRange pc.1 (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur).2 -
       (affineRange pc.1 (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur).1)).lo := by
  apply point_lo_pos_of_one_ulp_le
  have hw := actual_five_affine_widths i j
  have hu := five_widths_one_ulp
  simp only [alternatives,enhancedL6Box,if_true,List.mem_append,
    List.mem_cons,List.mem_singleton] at hmem
  rcases hmem with ((he | he) | (he | he | he))
  · subst pc
    rw [hw.1]
    exact hu.1
  · subst pc
    rw [hw.2.1]
    exact hu.2.1
  · subst pc
    rw [hw.2.2.1]
    exact hu.2.2.1
  · subst pc
    rw [hw.2.2.2.1]
    exact hu.2.2.2.1
  · subst pc
    rw [hw.2.2.2.2]
    exact hu.2.2.2.2

/-- The actual 512x512 enhanced ordinary saved integer has its true
single-cell integral semantics without any geometric or denominator
premise. This is a statement for every cell, not an executed table check. -/
theorem actual_enhanced_ordinary_Q80_lower (i j : Fin authorPairs) :
    (((ordinaryLower actualSf actualLog (enhancedL6Box i j):ℚ)/Q:ℚ):ℝ) ≤
      enhancedOrdinaryIntegral (enhancedL6Box i j).tl (enhancedL6Box i j).tr
        (enhancedL6Box i j).ul (enhancedL6Box i j).ur := by
  rcases actual_box_positive_ordered i j with ⟨htl,hul,ht,hu⟩
  apply enhanced_box_ordinary_Q80_lower (enhancedL6Box i j)
    rfl rfl htl hul ht hu
  intro pc hp _heligible
  exact actual_alternative_denominator_guard i j pc hp

end

end ImbalancedChen.P2Author512EnhancedChordDomain
