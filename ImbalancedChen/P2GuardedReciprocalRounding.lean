import ImbalancedChen.P2GuardedReciprocalRoundingCore
import ImbalancedChen.CurrentChenUpsilon8HarmonicMean

/-!
# Sign-separated reciprocal and division certificates

Verification records: docs/verification/20261123-blue-compilation.

`P2DirectedLogRounding` supplies the sibling interval-enclosure operations.
A reciprocal is accepted only for an ordered rational
interval wholly above or wholly below zero.  The checked operations return
`none` on a failed guard, including intervals containing zero.

The final application is the literal existing eighth harmonic kernel and,
on its original region, its unmodified reciprocal-gap integrand.
-/

namespace ImbalancedChen.Certificates.P2DirectedLogRounding

/-- These are enclosures of the literal original U8 affine gap and its
existing continuous cutoff denominator, respectively. -/
def u8GapBox (a b : Enclosure) : Enclosure := ((Enclosure.point 1).sub a).sub b

def u8DenominatorBox (a b : Enclosure) : Enclosure :=
  (u8GapBox a b).clampLower (1 / 3)

def u8KernelQ80 (a b : Enclosure) : Enclosure :=
  (u8DenominatorBox a b).reciprocalQ80

theorem u8DenominatorBox_guard (a b : Enclosure)
    (ha : a.lower ≤ a.upper) (hb : b.lower ≤ b.upper) :
    (u8DenominatorBox a b).reciprocalCheck = true := by
  have horder : (u8GapBox a b).lower ≤ (u8GapBox a b).upper := by
    dsimp [u8GapBox, Enclosure.sub, Enclosure.add, Enclosure.neg, Enclosure.point]
    linarith
  have hvalid : (u8DenominatorBox a b).ReciprocalValid := by
    constructor
    · exact max_le_max le_rfl horder
    · left
      exact lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1 / 3) (le_max_left _ _)
  simp [Enclosure.reciprocalCheck, hvalid]

/-- Pointwise Q80 soundness for the existing actual U8 harmonic kernel.
No integral value, final gain, or numerical kernel bound is an input. -/
theorem u8KernelQ80_contains {a b : Enclosure} {x : Fin 2 → ℝ}
    (ha : a.Contains (x 0)) (hb : b.Contains (x 1)) :
    (u8KernelQ80 a b).Contains (ImbalancedChen.currentChenUpsilon8HarmonicKernel x) := by
  have haorder : a.lower ≤ a.upper := by exact_mod_cast ha.1.trans ha.2
  have hborder : b.lower ≤ b.upper := by exact_mod_cast hb.1.trans hb.2
  have hgap : (u8GapBox a b).Contains (1 - x 0 - x 1) := by
    simpa only [u8GapBox, Rat.cast_one] using
      Enclosure.sub_contains
        (Enclosure.sub_contains (Enclosure.point_contains 1) ha) hb
  have hden : (u8DenominatorBox a b).Contains
      (max (1 / 3 : ℝ) (1 - x 0 - x 1)) := by
    simpa only [u8DenominatorBox, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      Enclosure.clampLower_contains hgap (1 / 3)
  simpa only [u8KernelQ80, ImbalancedChen.currentChenUpsilon8HarmonicKernel] using
    Enclosure.reciprocalQ80_contains hden (u8DenominatorBox_guard a b haorder hborder)

/-- On the literal original U8 region this bounds its unmodified integrand,
using the already proved kernel dictionary rather than a surrogate target. -/
theorem u8OriginalGapKernelQ80_contains {a b : Enclosure} {x : Fin 2 → ℝ}
    (ha : a.Contains (x 0)) (hb : b.Contains (x 1))
    (hx : x ∈ ImbalancedChen.currentChenUpsilon8HarmonicRegion) :
    (u8KernelQ80 a b).Contains (1 / (1 - x 0 - x 1)) := by
  have h := u8KernelQ80_contains ha hb
  rw [ImbalancedChen.currentChenUpsilon8HarmonicKernel_eq hx] at h
  exact h

end ImbalancedChen.Certificates.P2DirectedLogRounding
