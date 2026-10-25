import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A certified physical cell needs levels arbitrarily close to its cap, not
only one admissible midpoint.  All data below are rational and fixed before
N or a tuple.  The original gate upper endpoint G and cap lower endpoint U
are inputs; no scalar density, H248 correctness or analytic licence is an
input or conclusion.  The final residual comparison identifies the exact
error that a physical buffered ordinary kernel must pay.
-/

namespace ImbalancedChen.P5Z.NearCapRationalParameters

def capLoss (G U eta : ℚ) : ℚ := min eta ((U - G) / 2)

def level (G U eta : ℚ) : ℚ := U - capLoss G U eta

def delta (G U eta : ℚ) : ℚ :=
  min (3 / 4096) (min ((level G U eta - G) / 64)
    ((U - level G U eta) / 64))

def xi (G U eta wLower : ℚ) : ℚ := min (wLower / 2) (delta G U eta)

def rho (G U eta : ℚ) : ℚ := delta G U eta

theorem capLoss_pos {G U eta : ℚ} (hGU : G < U) (heta : 0 < eta) :
    0 < capLoss G U eta := by
  exact lt_min heta (by linarith)

theorem capLoss_le_eta (G U eta : ℚ) : capLoss G U eta ≤ eta := min_le_left _ _

theorem capLoss_le_half_gap (G U eta : ℚ) :
    capLoss G U eta ≤ (U - G) / 2 := min_le_right _ _

theorem gate_lt_level {G U eta : ℚ} (hGU : G < U) : G < level G U eta := by
  have h := capLoss_le_half_gap G U eta
  dsimp only [level]
  linarith

theorem level_lt_cap {G U eta : ℚ} (hGU : G < U) (heta : 0 < eta) :
    level G U eta < U := by
  have h := capLoss_pos hGU heta
  dsimp only [level]
  linarith

theorem level_error {G U eta : ℚ} (hGU : G < U) (heta : 0 < eta) :
    0 < U - level G U eta ∧ U - level G U eta ≤ eta := by
  constructor
  · exact sub_pos.mpr (level_lt_cap hGU heta)
  · simpa only [level, sub_sub_cancel] using capLoss_le_eta G U eta

theorem delta_pos {G U eta : ℚ} (hGU : G < U) (heta : 0 < eta) :
    0 < delta G U eta := by
  exact lt_min (by norm_num) (lt_min
    (by linarith [gate_lt_level (eta := eta) hGU])
    (by linarith [level_lt_cap hGU heta]))

theorem delta_le_cap (G U eta : ℚ) : delta G U eta ≤ 3 / 4096 := min_le_left _ _

theorem gate_buffer (G U eta : ℚ) :
    G + 64 * delta G U eta ≤ level G U eta := by
  have h := (min_le_right (3 / 4096 : ℚ)
    (min ((level G U eta - G) / 64) ((U - level G U eta) / 64))).trans
      (min_le_left _ _)
  change delta G U eta ≤ (level G U eta - G) / 64 at h
  linarith

theorem cap_buffer (G U eta : ℚ) : level G U eta + 64 * delta G U eta ≤ U := by
  have h := (min_le_right (3 / 4096 : ℚ)
    (min ((level G U eta - G) / 64) ((U - level G U eta) / 64))).trans
      (min_le_right _ _)
  change delta G U eta ≤ (U - level G U eta) / 64 at h
  linarith

theorem delta_le_eta (G U eta : ℚ) : delta G U eta ≤ eta / 64 := by
  have h := cap_buffer G U eta
  have he := capLoss_le_eta G U eta
  dsimp only [level] at h
  linarith

theorem xi_pos {G U eta wLower : ℚ}
    (hGU : G < U) (heta : 0 < eta) (hw : 0 < wLower) :
    0 < xi G U eta wLower :=
  lt_min (by linarith) (delta_pos hGU heta)

theorem xi_le_half (G U eta wLower : ℚ) : xi G U eta wLower ≤ wLower / 2 :=
  min_le_left _ _

theorem xi_le_delta (G U eta wLower : ℚ) :
    xi G U eta wLower ≤ delta G U eta := min_le_right _ _

theorem small_parameter_bounds (G U eta wLower : ℚ) :
    rho G U eta ≤ eta / 64 ∧ xi G U eta wLower ≤ eta / 64 := by
  exact ⟨delta_le_eta G U eta,
    (xi_le_delta G U eta wLower).trans (delta_le_eta G U eta)⟩

/-- The actual residual at a tuple is `C-T`, whereas the fixed cell uses
`level-Tplus-20*delta`.  Only genuine cell endpoint errors occur here. -/
theorem residual_error
    (G U eta C T Tplus capError prefixError : ℚ)
    (hGU : G < U) (heta : 0 < eta)
    (hCU : U ≤ C) (hC : C ≤ U + capError)
    (hT : T ≤ Tplus) (hTplus : Tplus ≤ T + prefixError) :
    0 ≤ (C - T) - (level G U eta - Tplus - 20 * delta G U eta) ∧
      (C - T) - (level G U eta - Tplus - 20 * delta G U eta) ≤
        capError + prefixError + (21 / 16) * eta := by
  have hd := cap_buffer G U eta
  have he := capLoss_le_eta G U eta
  have hde := delta_le_eta G U eta
  have hp := capLoss_pos hGU heta
  have hdp := delta_pos hGU heta
  dsimp only [level] at hd ⊢
  constructor <;> linarith

/-- The original last full-square gate supplies this fixed positive
residual, including all twenty buffer units. -/
theorem residual_lower
    (G U eta Tplus wLower : ℚ) (hG : Tplus + wLower ≤ G) :
    wLower + 44 * delta G U eta ≤ level G U eta - Tplus - 20 * delta G U eta := by
  have h := gate_buffer G U eta
  linarith

end ImbalancedChen.P5Z.NearCapRationalParameters
