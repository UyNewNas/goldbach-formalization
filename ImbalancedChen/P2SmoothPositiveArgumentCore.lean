import ImbalancedChen.P4BSmoothGateUpperStep
import Mathlib.Tactic.Ring

/-! SOURCE ONLY / UNCOMPILED.
Five existing scalar declarations extracted verbatim. Original fully
qualified names and proof bodies are retained. See SCALAR_EXTRACTION.json
for original bytes, complete headers, reversible owner postimages, and
the rule requiring those postimages when importing the old owners.
This module does not replace any missing P5 local-zero smooth proof. -/

namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight
noncomputable section
open Real P4B
open scoped ContDiff

def floorGate (z : ℝ) : ℝ := smoothGateUpperStep (1/2) (z-1)
end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight

namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile
noncomputable section
open Real P4B
open scoped ContDiff

/-- A smooth positive argument equal to the physical coordinate once x≥b.
It changes the logarithm only where the full physical weight vanishes. -/
def positiveArg (b x : ℝ) := b+(x-b)*smoothGateUpperStep (b/2) (x-b)

theorem positiveArg_eq {b x : ℝ} (hb : 0<b) (h : b≤x) : positiveArg b x=x := by
  rw [positiveArg,smoothGateUpperStep_eq_one (half_pos hb) (sub_nonneg.mpr h)]
  ring

theorem positiveArg_pos {b : ℝ} (hb : 0<b) (x : ℝ) : 0<positiveArg b x := by
  by_cases h : b≤x
  · rw [positiveArg_eq hb h]
    exact hb.trans_le h
  by_cases hx : x≤b/2
  · have h0 := smoothGateUpperStep_eq_zero (half_pos hb) (show x-b≤ -(b/2) by linarith only [hx])
    simpa only [positiveArg,h0,mul_zero,add_zero] using hb
  have hp := lt_of_not_ge hx
  have hn := mul_le_mul_of_nonpos_left (smoothGateUpperStep_le_one (b/2) (x-b))
    (sub_nonpos.mpr (le_of_not_ge h))
  dsimp only [positiveArg]
  linarith only [lt_trans (half_pos hb) hp,hn]

theorem positiveArg_smooth (b : ℝ) : ContDiff ℝ ∞ (positiveArg b) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    ((contDiff_smoothGateUpperStep _).comp (contDiff_id.sub contDiff_const)))

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile

