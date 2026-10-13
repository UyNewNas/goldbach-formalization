import ImbalancedChen.BufferedFirstCubeGeometry

/-!
# A uniform residual floor for the actual box-enclosure formulas

The `v(x)` branch alone gives a lower bound `1/2` when the first coordinate
lies in `[0, 19/96]`. This remains true for the rational interval lower bound,
and loses at most `1/D` in the existing signed integer rounding algorithm.

`ScaledBox.extendedClippedLower` is the lower endpoint returned by the two
branches of `certify_extended_prefix.py::phi_range` at manuscript pin
`ba6ec11d800eccc54406490631895e174de85766`: above the crossing coordinate it
uses only `v_lo`, and below it uses the existing seven-entry maximum. The
algorithm clips both at `NT`. Its usual no-crossing dispatch precondition is
not needed for the lower-floor result, which holds for either branch.

These results supply a positive residual for the buffered cap used in a tail
estimate. They do not assert that a full adopted policy has been instantiated,
prove any distribution statement, or identify an actual tail integral.
-/

namespace ImbalancedChen.VariableEnvelope

noncomputable section

theorem half_le_v_of_extended_range {x : ℝ} (hx : 0 ≤ x)
    (hstop : x ≤ extendedFirstStop) : (1 : ℝ) / 2 ≤ v x := by
  rw [v_eq_min]
  apply le_min
  · dsimp [A]
    linarith
  · dsimp [C, extendedFirstStop] at *
    linarith

/-- Both actual affine interval endpoints lie above one half. -/
theorem half_le_qVLo_of_extended_range {l u : ℚ}
    (hl : 0 ≤ l) (hu : u ≤ 19 / 96) : (1 : ℚ) / 2 ≤ qVLo l u := by
  unfold qVLo
  apply le_min <;> dsimp [qA, qC] <;> linarith

theorem RationalBox.half_le_lower (b : RationalBox)
    (hl : 0 ≤ b.lx) (hu : b.ux ≤ 19 / 96) : (1 : ℚ) / 2 ≤ b.lower := by
  exact (half_le_qVLo_of_extended_range hl hu).trans (le_max_left _ _)

/-- The existing integer rectangle lower bound includes its downward error. -/
theorem ScaledBox.half_sub_inv_le_lower (D : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hl : 0 ≤ (b.toRational D).lx) (hu : (b.toRational D).ux ≤ 19 / 96) :
    (1 : ℚ) / 2 - 1 / D ≤ b.lower D := by
  have hf := (b.toRational D).half_le_lower hl hu
  have hr := (b.rawLower_rounding D hD).2
  linarith

theorem scaledVLo_half_sub_inv_le (D l u : ℤ) (hD : 0 < D)
    (hl : 0 ≤ (l : ℚ) / D) (hu : (u : ℚ) / D ≤ 19 / 96) :
    (1 : ℚ) / 2 - 1 / D ≤ (scaledVLo D l u : ℚ) / D := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hf := half_le_qVLo_of_extended_range hl hu
  have hr : (D : ℚ) * qVLo ((l : ℚ) / D) ((u : ℚ) / D) ≤
      (scaledVLo D l u : ℚ) + 1 := by
    exact_mod_cast (scaledVLo_rounding D l u hD).2
  apply (le_div_iff₀ hDQ).mpr
  have hi : ((1 : ℚ) / D) * D = 1 := div_mul_cancel₀ 1 hDQ.ne'
  nlinarith [mul_le_mul_of_nonneg_left hf hDQ.le]

theorem ScaledBox.half_sub_inv_le_clippedLower (D M NT : ℤ) (b : ScaledBox)
    (hD : 0 < D) (hNT : (1 : ℚ) / 2 ≤ (NT : ℚ) / D)
    (hl : 0 ≤ (b.toRational D).lx) (hu : (b.toRational D).ux ≤ 19 / 96) :
    (1 : ℚ) / 2 - 1 / D ≤ b.clippedLower D M NT := by
  rw [b.clippedLower_eq D M NT hD]
  apply le_min
  · have hd : (0 : ℚ) ≤ 1 / D := by positivity
    linarith
  · exact b.half_sub_inv_le_lower D hD hl hu

/-- Literal lower endpoint of both extended-prefix dispatch branches. -/
def ScaledBox.extendedClippedLower (D M NT : ℤ) (b : ScaledBox) : ℚ :=
  if M ≤ b.lx then min ((NT : ℚ) / D) ((scaledVLo D b.lx b.ux : ℚ) / D)
  else b.clippedLower D M NT

theorem ScaledBox.extendedClippedLower_above (D M NT : ℤ) (b : ScaledBox)
    (hx : M ≤ b.lx) :
    b.extendedClippedLower D M NT =
      min ((NT : ℚ) / D) ((scaledVLo D b.lx b.ux : ℚ) / D) := if_pos hx

theorem ScaledBox.extendedClippedLower_below (D M NT : ℤ) (b : ScaledBox)
    (hx : b.lx < M) : b.extendedClippedLower D M NT = b.clippedLower D M NT :=
  if_neg (not_le.mpr hx)

/-- Both branches, including the transition side, have the same floor. -/
theorem ScaledBox.half_sub_inv_le_extendedClippedLower
    (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hNT : (1 : ℚ) / 2 ≤ (NT : ℚ) / D)
    (hl : 0 ≤ (b.toRational D).lx) (hu : (b.toRational D).ux ≤ 19 / 96) :
    (1 : ℚ) / 2 - 1 / D ≤ b.extendedClippedLower D M NT := by
  unfold ScaledBox.extendedClippedLower
  split_ifs
  · apply le_min
    · have hd : (0 : ℚ) ≤ 1 / D := by positivity
      linarith
    · exact scaledVLo_half_sub_inv_le D b.lx b.ux hD hl hu
  · exact b.half_sub_inv_le_clippedLower D M NT hD hNT hl hu

/-- A real residual floor, allowing an explicit rounding loss `delta`. -/
theorem bufferedCoarseCap_residual_floor {e delta Gamma x y : ℝ}
    (hdelta : 0 ≤ delta) (hGamma : 1 / 2 - delta ≤ Gamma)
    (hbudget : 2 * e + delta ≤ 1 / 192)
    (hx : x ≤ extendedFirstStop) (hy : y ≤ extendedFirstStop) :
    19 / 192 ≤ bufferedCoarseCap e Gamma - x - y := by
  have hc : 1 / 2 - delta - 2 * e ≤ bufferedCoarseCap e Gamma := by
    unfold bufferedCoarseCap
    apply le_min
    · dsimp [extendedDistributionCap]
      linarith
    · linarith
  dsimp [extendedFirstStop] at hx hy
  linarith

/-- The actual two-branch certificate endpoint supplies the floor; no
unproved lower bound on a generic `Gamma` remains in this result. -/
theorem ScaledBox.extendedClippedLower_buffered_residual_floor
    (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hNT : (1 : ℚ) / 2 ≤ (NT : ℚ) / D)
    (hl : 0 ≤ (b.toRational D).lx) (hu : (b.toRational D).ux ≤ 19 / 96)
    {e x y : ℝ} (hbudget : 2 * e + 1 / (D : ℝ) ≤ 1 / 192)
    (hx : x ≤ extendedFirstStop) (hy : y ≤ extendedFirstStop) :
    19 / 192 ≤ bufferedCoarseCap e (b.extendedClippedLower D M NT) - x - y := by
  apply bufferedCoarseCap_residual_floor (delta := 1 / (D : ℝ))
  · positivity
  · have hfloor := b.half_sub_inv_le_extendedClippedLower D M NT hD hNT hl hu
    have hcast := (Rat.cast_le (K := ℝ)).2 hfloor
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_intCast] using hcast
  · exact hbudget
  · exact hx
  · exact hy

/-- The denominator used by the frozen extended certificate pays the loss
uniformly for a fixed positive interval of epsilon values. -/
theorem extendedCertificate_rounding_budget {e : ℝ} (he : e ≤ 1 / 768) :
    2 * e + 1 / 805306368000 ≤ 1 / 192 := by
  linarith

/-- Concrete coordinate scale, crossing and cap from the frozen script.
Only actual first-coordinate endpoint bounds and the epsilon range remain. -/
theorem ScaledBox.currentExtended_buffered_residual_floor (b : ScaledBox)
    (hl : 0 ≤ b.lx) (hu : b.ux ≤ 159383552000)
    {e x y : ℝ} (he : e ≤ 1 / 768)
    (hx : x ≤ extendedFirstStop) (hy : y ≤ extendedFirstStop) :
    19 / 192 ≤ bufferedCoarseCap e
      (b.extendedClippedLower 805306368000 157286400000 481573208064) - x - y := by
  apply b.extendedClippedLower_buffered_residual_floor
    805306368000 157286400000 481573208064 (by norm_num) (by norm_num)
  · dsimp [ScaledBox.toRational]
    positivity
  · dsimp [ScaledBox.toRational]
    apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 805306368000)).mpr
    norm_num
    exact_mod_cast hu
  · exact extendedCertificate_rounding_budget he
  · exact hx
  · exact hy

end

end ImbalancedChen.VariableEnvelope
