import ImbalancedChen.OriginalPairedN48AllNativeQueryGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original max(0, baselineLo-costHi) comparison uses P112 endpoints and
Q80 stored floors.  Zero floors are handled by the true analytic C0 cap,
not by incorrectly requiring an unclamped numerical endpoint difference.
Actual row-token callers discharge the two directed interval directions.
-/

namespace ImbalancedChen.OriginalPairedN48Q112ClampedReceiver

noncomputable section
open Set
open LiLiuPrereqBuchstab
open OriginalPairedN48AllNativeQueryGeometry
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48MethodZeroQ112SwitchReduction
open P2N48OriginalQ80DirectedRowSoundness
open P2N48OriginalStrictLogMassAndOmegaPorts
open P5Z.U11Integral P5Z.U11Canonical

def originalRowMaxFloorCheck (r : SourceRow) (e : DirectedMethodZeroRow) : Bool :=
  decide ((r.floorQ : ℤ) * replayP ≤
    max 0 (e.switchBaselineLo - e.omegaCostHi) * replayQ)

/-- Genuine actual-domain C0 bound for every row and every tied pattern. -/
theorem actual_parent_buchstab_cap (r : SourceRow) {v : LogFour}
    (hv : v ∈ fullParent r) : buchstab (omegaArgument v) ≤ omegaCap := by
  have hq := all_native_actual_raw_query_contains r hv.1
  have hl : (2 : ℝ) ≤ (rawQueryLower r : ℝ) := by
    exact_mod_cast (all_native_raw_query_range r).1
  have h := P2SeedOmegaGlobalEnvelope.actual_buchstab_global_cap (hl.trans hq.1)
  simpa only [omegaCap, P2SeedOmegaLiteralFibre.omegaCap] using h

/-- Scale-correct receiver for the literal original P112/Q80 max check.
The data premises are precisely interval directions, a local omega query,
and a finite integer comparison; no old-count bound is assumed. -/
theorem q112_original_max_floor_sound (r : SourceRow) (e : DirectedMethodZeroRow)
    (omegaUpper : ℝ)
    (hLo : (e.switchBaselineLo : ℝ) / (replayP : ℝ) ≤
      anchorK * omegaCap * parentUnweightedMass (fullParent r))
    (hHi : anchorK * omegaUpper * parentUnweightedMass (fullParent r) ≤
      (e.omegaCostHi : ℝ) / (replayP : ℝ))
    (hOmega : ∀ v ∈ fullParent r, buchstab (omegaArgument v) ≤ omegaUpper)
    (hcheck : originalRowMaxFloorCheck r e = true) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have hk : 0 ≤ anchorK := by norm_num [anchorK]
  have hT : anchorK * parentSwitchedMass (fullParent r) ≤
      (e.omegaCostHi : ℝ) / (replayP : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (true_switch_mass_le_scalar_mass r omegaUpper hOmega) hk
    have hs : anchorK * parentSwitchedMass (fullParent r) ≤
        anchorK * omegaUpper * parentUnweightedMass (fullParent r) := by
      simpa only [mul_assoc] using h
    exact hs.trans hHi
  have hCap : anchorK * parentSwitchedMass (fullParent r) ≤
      anchorK * omegaCap * parentUnweightedMass (fullParent r) := by
    have h := mul_le_mul_of_nonneg_left
      (true_switch_mass_le_scalar_mass r omegaCap (fun v hv => actual_parent_buchstab_cap r hv)) hk
    simpa only [mul_assoc] using h
  have hF := of_decide_eq_true (show decide ((r.floorQ : ℤ) * replayP ≤
      max 0 (e.switchBaselineLo - e.omegaCostHi) * replayQ) = true from hcheck)
  by_cases hd : 0 ≤ e.switchBaselineLo - e.omegaCostHi
  · rw [max_eq_right hd] at hF
    have hFR : (r.floorQ : ℝ) * (replayP : ℝ) ≤
        ((e.switchBaselineLo - e.omegaCostHi : ℤ) : ℝ) * (replayQ : ℝ) := by
      exact_mod_cast hF
    have hP : (0 : ℝ) < replayP := by norm_num [replayP]
    have hQ : (0 : ℝ) < replayQ := by norm_num [replayQ]
    have hUnit := (div_le_div_iff₀ hQ hP).2 hFR
    have hScale : (replayQ : ℝ) = floorScale := by norm_num [replayQ, floorScale]
    have hFloor : (r.floorQ : ℝ) / floorScale ≤
        (e.switchBaselineLo : ℝ) / (replayP : ℝ) - (e.omegaCostHi : ℝ) / (replayP : ℝ) := by
      simpa only [hScale, Int.cast_sub, sub_div] using hUnit
    dsimp [savedParent]
    linarith only [hLo, hT, hFloor]
  · rw [max_eq_left (le_of_not_ge hd), zero_mul] at hF
    have hP : (0 : ℤ) < replayP := by norm_num [replayP]
    have hZero : r.floorQ = 0 := by
      have hNonpos : (r.floorQ : ℤ) ≤ 0 :=
        (mul_le_mul_right hP).mp (by simpa only [zero_mul] using hF)
      omega
    simpa only [savedParent, hZero, Nat.cast_zero, zero_div, sub_zero] using hCap

end
end ImbalancedChen.OriginalPairedN48Q112ClampedReceiver
