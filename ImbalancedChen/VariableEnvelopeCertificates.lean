import ImbalancedChen.VariableEnvelopeBoxes
import ImbalancedChen.VariableEnvelopeScaled

/-!
# Whole-box bridge for the existing integer prefix certificates

`rawLower`, `rawUpper`, and `phiRange` preserve the integer formulas of
`certify_variable_prefix.py` and the below-mu branch of
`certify_extended_prefix.py`, including signed rounding and `min(NT, ...)`.
The clipped upper endpoint bounds the clipped envelope only. The explicit
extended adapter requires the script's actual below-mu dispatch condition;
no result about its different above-mu expression is asserted.
-/

namespace ImbalancedChen.VariableEnvelope

structure ScaledBox where
  lx : ℤ
  ux : ℤ
  ly : ℤ
  uy : ℤ
  lz : ℤ
  uz : ℤ
  deriving DecidableEq, Repr

namespace ScaledBox

def toRational (D : ℤ) (b : ScaledBox) : RationalBox :=
  ⟨(b.lx : ℚ) / D, (b.ux : ℚ) / D, (b.ly : ℚ) / D,
    (b.uy : ℚ) / D, (b.lz : ℚ) / D, (b.uz : ℚ) / D⟩

/-- Exact `low` before the certificate's final `min(NT, low)`. -/
def rawLower (D : ℤ) (b : ScaledBox) : ℤ :=
  maxSeven (scaledVLo D b.lx b.ux) (scaledVLo D b.ly b.uy)
    (scaledVLo D (b.lx + b.ly) (b.ux + b.uy))
    (scaledVLo D (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
    (scaledVLo D (b.lx + b.lz) (b.ux + b.uz))
    (scaledVLo D (b.ly + b.lz) (b.uy + b.uz)) (scaledBLo D b.uz)

/-- Exact `high` before the certificate's final `min(NT, high)`. -/
def rawUpper (D M : ℤ) (b : ScaledBox) : ℤ :=
  maxSeven (scaledVHi D M b.lx b.ux) (scaledVHi D M b.ly b.uy)
    (scaledVHi D M (b.lx + b.ly) (b.ux + b.uy))
    (scaledVHi D M (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
    (scaledVHi D M (b.lx + b.lz) (b.ux + b.uz))
    (scaledVHi D M (b.ly + b.lz) (b.uy + b.uz)) (scaledBHi D b.lz)

/-- Exact pair returned by the old `phi_range`, including its truncation. -/
def phiRange (D M NT : ℤ) (b : ScaledBox) : ℤ × ℤ :=
  (min NT (rawLower D b), min NT (rawUpper D M b))

def lower (D : ℤ) (b : ScaledBox) : ℚ := (rawLower D b : ℚ) / D

def upper (D M : ℤ) (b : ScaledBox) : ℚ := (rawUpper D M b : ℚ) / D

def clippedLower (D M NT : ℤ) (b : ScaledBox) : ℚ := ((phiRange D M NT b).1 : ℚ) / D

def clippedUpper (D M NT : ℤ) (b : ScaledBox) : ℚ := ((phiRange D M NT b).2 : ℚ) / D

/-- A true result includes positivity, an exact crossing coordinate, and nonemptiness. -/
def marginCheck (D M NT : ℤ) (b : ScaledBox) (η : ℚ) : Bool :=
  decide (0 < D ∧ 128 * M = 25 * D) &&
    (toRational D b).feasible &&
    decide (0 < clippedLower D M NT b - 3 * ((b.ux : ℚ) / D) - η)

/-- Only the actual below-mu path of the extended certificate is accepted. -/
def extendedBelowCheck (D M NT : ℤ) (b : ScaledBox) (η : ℚ) : Bool :=
  decide (b.lx < M ∧ b.ux ≤ M) && marginCheck D M NT b η

private theorem cast_int_maxSeven (a b c d e f g : ℤ) :
    ((maxSeven a b c d e f g : ℤ) : ℝ) = maxSeven (a : ℝ) b c d e f g := by
  simp [maxSeven]

private theorem mul_maxSeven (D a b c d e f g : ℝ) (hD : 0 ≤ D) :
    D * maxSeven a b c d e f g =
      maxSeven (D*a) (D*b) (D*c) (D*d) (D*e) (D*f) (D*g) := by
  simp only [maxSeven, mul_max_of_nonneg _ _ hD]

private theorem maxSeven_add_one (a b c d e f g : ℝ) :
    maxSeven (a+1) (b+1) (c+1) (d+1) (e+1) (f+1) (g+1) =
      maxSeven a b c d e f g + 1 := by
  simp only [maxSeven, max_add_add_right]

/-- The entire old lower algorithm rounds the rational box lower bound down by at most one. -/
theorem rawLower_scaled_rounding (D : ℤ) (b : ScaledBox) (hD : 0 < D) :
    (rawLower D b : ℝ) ≤ D * ((toRational D b).lower : ℝ) ∧
    D * ((toRational D b).lower : ℝ) ≤ (rawLower D b : ℝ) + 1 := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have hx := scaledVLo_rounding D b.lx b.ux hD
  have hy := scaledVLo_rounding D b.ly b.uy hD
  have hxy := scaledVLo_rounding D (b.lx+b.ly) (b.ux+b.uy) hD
  have hxyz := scaledVLo_rounding D (b.lx+b.ly+b.lz) (b.ux+b.uy+b.uz) hD
  have hxz := scaledVLo_rounding D (b.lx+b.lz) (b.ux+b.uz) hD
  have hyz := scaledVLo_rounding D (b.ly+b.lz) (b.uy+b.uz) hD
  have hb := scaledBLo_rounding D b.uz hD
  constructor
  · convert maxSeven_mono hx.1 hy.1 hxy.1 hxyz.1 hxz.1 hyz.1 hb.1 using 1 <;>
      first | rfl | simp only [rawLower, RationalBox.lower, toRational, cast_int_maxSeven,
        cast_maxSeven, mul_maxSeven _ _ _ _ _ _ _ _ hD0, Int.cast_add, add_div]
  · have hh := maxSeven_mono hx.2 hy.2 hxy.2 hxyz.2 hxz.2 hyz.2 hb.2
    rw [maxSeven_add_one] at hh
    convert hh using 1 <;>
      first | rfl | simp only [rawLower, RationalBox.lower, toRational, cast_int_maxSeven,
        cast_maxSeven, mul_maxSeven _ _ _ _ _ _ _ _ hD0, Int.cast_add, add_div]

/-- The entire old upper algorithm rounds the rational box upper bound up by at most one. -/
theorem rawUpper_scaled_rounding (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) :
    D * ((toRational D b).upper : ℝ) ≤ (rawUpper D M b : ℝ) ∧
    (rawUpper D M b : ℝ) ≤ D * ((toRational D b).upper : ℝ) + 1 := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have hx := scaledVHi_rounding D M b.lx b.ux hD hM
  have hy := scaledVHi_rounding D M b.ly b.uy hD hM
  have hxy := scaledVHi_rounding D M (b.lx+b.ly) (b.ux+b.uy) hD hM
  have hxyz := scaledVHi_rounding D M (b.lx+b.ly+b.lz) (b.ux+b.uy+b.uz) hD hM
  have hxz := scaledVHi_rounding D M (b.lx+b.lz) (b.ux+b.uz) hD hM
  have hyz := scaledVHi_rounding D M (b.ly+b.lz) (b.uy+b.uz) hD hM
  have hb := scaledBHi_rounding D b.lz hD
  constructor
  · convert maxSeven_mono hx.1 hy.1 hxy.1 hxyz.1 hxz.1 hyz.1 hb.1 using 1 <;>
      first | rfl | simp only [rawUpper, RationalBox.upper, toRational, cast_int_maxSeven,
        cast_maxSeven, mul_maxSeven _ _ _ _ _ _ _ _ hD0, Int.cast_add, add_div]
  · have hh := maxSeven_mono hx.2 hy.2 hxy.2 hxyz.2 hxz.2 hyz.2 hb.2
    rw [maxSeven_add_one] at hh
    convert hh using 1 <;>
      first | rfl | simp only [rawUpper, RationalBox.upper, toRational, cast_int_maxSeven,
        cast_maxSeven, mul_maxSeven _ _ _ _ _ _ _ _ hD0, Int.cast_add, add_div]





/-- After normalization, downward rounding costs at most `1 / D`. -/
theorem rawLower_rounding (D : ℤ) (b : ScaledBox) (hD : 0 < D) :
    lower D b ≤ (toRational D b).lower ∧
    (toRational D b).lower ≤ lower D b + 1 / (D : ℚ) := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hh : (rawLower D b : ℚ) ≤ D * (toRational D b).lower ∧
      D * (toRational D b).lower ≤ (rawLower D b : ℚ) + 1 := by
    exact_mod_cast rawLower_scaled_rounding D b hD
  unfold lower
  constructor
  · apply (div_le_iff₀ hDQ).2
    nlinarith [hh.1]
  · rw [← add_div]
    apply (le_div_iff₀ hDQ).2
    nlinarith [hh.2]

/-- After normalization, upward rounding costs at most `1 / D`. -/
theorem rawUpper_rounding (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) :
    (toRational D b).upper ≤ upper D M b ∧
    upper D M b ≤ (toRational D b).upper + 1 / (D : ℚ) := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hh : D * (toRational D b).upper ≤ (rawUpper D M b : ℚ) ∧
      (rawUpper D M b : ℚ) ≤ D * (toRational D b).upper + 1 := by
    exact_mod_cast rawUpper_scaled_rounding D M b hD hM
  unfold upper
  constructor
  · apply (le_div_iff₀ hDQ).2
    nlinarith [hh.1]
  · apply (div_le_iff₀ hDQ).2
    have hc : (1 : ℚ) / D * D = 1 := div_mul_cancel₀ 1 (ne_of_gt hDQ)
    nlinarith [hh.2]

/-- The raw old-script interval bounds the original eight gated branches at every valid point. -/
theorem raw_bounds (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {x y z : ℝ}
    (h : (toRational D b).ValidPoint x y z) :
    (lower D b : ℝ) ≤ original x y z ∧ original x y z ≤ (upper D M b : ℝ) := by
  have hl : (lower D b : ℝ) ≤ ((toRational D b).lower : ℝ) :=
    Rat.cast_le.mpr (rawLower_rounding D b hD).1
  have hu : ((toRational D b).upper : ℝ) ≤ (upper D M b : ℝ) :=
    Rat.cast_le.mpr (rawUpper_rounding D M b hD hM).1
  exact ⟨hl.trans (RationalBox.lower_le_original h),
    (RationalBox.original_le_upper h).trans hu⟩

theorem clippedLower_eq (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D) :
    clippedLower D M NT b = min ((NT : ℚ) / D) (lower D b) := by
  have hD0 : (0 : ℚ) ≤ D := by exact_mod_cast le_of_lt hD
  simp only [clippedLower, phiRange, Int.cast_min, lower, min_div_div_right hD0]

theorem clippedUpper_eq (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D) :
    clippedUpper D M NT b = min ((NT : ℚ) / D) (upper D M b) := by
  have hD0 : (0 : ℚ) ≤ D := by exact_mod_cast le_of_lt hD
  simp only [clippedUpper, phiRange, Int.cast_min, upper, min_div_div_right hD0]

/-- `phi_range` bounds the truncated envelope; its upper endpoint need not bound `original`. -/
theorem phiRange_bounds (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {x y z : ℝ}
    (h : (toRational D b).ValidPoint x y z) :
    (clippedLower D M NT b : ℝ) ≤ min ((NT : ℝ) / D) (original x y z) ∧
    min ((NT : ℝ) / D) (original x y z) ≤ (clippedUpper D M NT b : ℝ) := by
  rw [clippedLower_eq D M NT b hD, clippedUpper_eq D M NT b hD]
  simp only [Rat.cast_min, Rat.cast_div, Rat.cast_intCast]
  have hh := raw_bounds D M b hD hM h
  exact ⟨min_le_min_left _ hh.1, min_le_min_left _ hh.2⟩

/-- The clipped lower endpoint also remains a lower bound for the untruncated envelope. -/
theorem clippedLower_le_original (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {x y z : ℝ}
    (h : (toRational D b).ValidPoint x y z) :
    (clippedLower D M NT b : ℝ) ≤ original x y z :=
  (phiRange_bounds D M NT b hD hM h).1.trans (min_le_right _ _)

/-- Integer precision and geometric width contribute separately to the interval gap. -/
theorem upper_sub_lower_le (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) (hw : (toRational D b).WellFormed) :
    upper D M b - lower D b ≤ 9 / 2 * (toRational D b).width + 2 / (D : ℚ) := by
  have hl := rawLower_rounding D b hD
  have hu := rawUpper_rounding D M b hD hM
  have hg := RationalBox.upper_sub_lower_le hw
  have htwo : (2 : ℚ) / D = 2 * (1 / (D : ℚ)) := by ring
  rw [htwo]
  linarith [hl.2, hu.2]

private theorem min_gap {a b t δ : ℚ} (hδ : 0 ≤ δ) (h : b - a ≤ δ) :
    min t b - min t a ≤ δ := by
  by_cases ha : a ≤ t
  · rw [min_eq_right ha]
    linarith [min_le_right t b]
  · rw [min_eq_left (le_of_not_ge ha)]
    linarith [min_le_left t b]

/-- Truncation does not enlarge the explicit width-plus-rounding error bound. -/
theorem clippedUpper_sub_clippedLower_le (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) (hw : (toRational D b).WellFormed) :
    clippedUpper D M NT b - clippedLower D M NT b ≤
      9 / 2 * (toRational D b).width + 2 / (D : ℚ) := by
  rw [clippedLower_eq D M NT b hD, clippedUpper_eq D M NT b hD]
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  apply min_gap _ (upper_sub_lower_le D M b hD hM hw)
  have hwidth := RationalBox.width_nonneg (toRational D b)
  have hround : (0 : ℚ) ≤ 2 / D := div_nonneg (by norm_num) (le_of_lt hDQ)
  linarith

/-- Both one-sided errors obey the same explicit bound, with no extremum-sampling assumption. -/
theorem enclosure_error (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {x y z : ℝ}
    (h : (toRational D b).ValidPoint x y z) :
    0 ≤ original x y z - lower D b ∧
    original x y z - lower D b ≤ (9 / 2 : ℝ) * (toRational D b).width + 2 / D ∧
    0 ≤ (upper D M b : ℝ) - original x y z ∧
    (upper D M b : ℝ) - original x y z ≤ (9 / 2 : ℝ) * (toRational D b).width + 2 / D := by
  have hh := raw_bounds D M b hD hM h
  have hg : (upper D M b : ℝ) - lower D b ≤
      (9 / 2 : ℝ) * (toRational D b).width + 2 / D := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr
      (upper_sub_lower_le D M b hD hM (RationalBox.wellFormed_of_inBox h.1))
    push_cast at hh
    exact hh
  constructor
  · linarith [hh.1]
  constructor
  · linarith [hh.1, hh.2]
  constructor <;> linarith [hh.1, hh.2]

/-- Width tending to zero and growing scale give an explicit error target.
At a fixed integer scale the separate `2 / D` term is deliberately retained. -/
theorem error_lt_of_width_and_precision (D M : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {x y z ε : ℝ}
    (h : (toRational D b).ValidPoint x y z)
    (hw : ((toRational D b).width : ℝ) < ε / 9)
    (hp : (2 : ℝ) / D ≤ ε / 2) :
    original x y z - lower D b < ε ∧ (upper D M b : ℝ) - original x y z < ε := by
  have hh := enclosure_error D M b hD hM h
  constructor <;> linarith [hh.2.1, hh.2.2.2]

/-- Rational success certifies the strict surplus at every actual point of the effective box. -/
theorem margin_of_rational_check (D M NT : ℤ) (b : ScaledBox) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {η : ℚ}
    (hc : 0 < clippedLower D M NT b - 3 * ((b.ux : ℚ) / D) - η)
    {x y z : ℝ} (h : (toRational D b).ValidPoint x y z) :
    0 < original x y z - 3 * x - η := by
  have hcr : (0 : ℝ) < (clippedLower D M NT b : ℝ) - 3 * ((b.ux : ℝ) / D) - η := by
    exact_mod_cast hc
  have hl := clippedLower_le_original D M NT b hD hM h
  have hx : x ≤ (b.ux : ℝ) / D := by
    simpa only [toRational, Rat.cast_div, Rat.cast_intCast] using h.1.2.1
  linarith

/-- Acceptance proves nonemptiness and a strict surplus, using only integer/rational checks. -/
theorem marginCheck_sound (D M NT : ℤ) (b : ScaledBox) {η : ℚ}
    (h : marginCheck D M NT b η = true) :
    (∃ x y z : ℝ, (toRational D b).ValidPoint x y z) ∧
      ∀ x y z : ℝ, (toRational D b).ValidPoint x y z →
        0 < original x y z - 3 * x - η := by
  have hh : ((0 < D ∧ 128 * M = 25 * D) ∧ (toRational D b).feasible = true) ∧
      0 < clippedLower D M NT b - 3 * ((b.ux : ℚ) / D) - η := by
    simpa only [marginCheck, Bool.and_eq_true, decide_eq_true_eq] using h
  exact ⟨(RationalBox.feasible_iff _).mp hh.1.2,
    fun _ _ _ hp => margin_of_rational_check D M NT b hh.1.1.1 hh.1.1.2 hh.2 hp⟩

/-- An empty effective box can never receive a successful surplus certificate. -/
theorem marginCheck_false_of_empty (D M NT : ℤ) (b : ScaledBox) (η : ℚ)
    (he : ¬ ∃ x y z : ℝ, (toRational D b).ValidPoint x y z) :
    marginCheck D M NT b η = false := by
  cases hc : marginCheck D M NT b η
  · rfl
  · exact False.elim (he (marginCheck_sound D M NT b hc).1)

/-- The extended adapter exposes and proves its precise below-mu dispatch restriction. -/
theorem extendedBelowCheck_sound (D M NT : ℤ) (b : ScaledBox) {η : ℚ}
    (h : extendedBelowCheck D M NT b η = true) :
    (b.lx < M ∧ b.ux ≤ M) ∧
    (∃ x y z : ℝ, (toRational D b).ValidPoint x y z) ∧
      ∀ x y z : ℝ, (toRational D b).ValidPoint x y z →
        0 < original x y z - 3 * x - η := by
  have hh : (b.lx < M ∧ b.ux ≤ M) ∧ marginCheck D M NT b η = true := by
    simpa only [extendedBelowCheck, Bool.and_eq_true, decide_eq_true_eq] using h
  exact ⟨hh.1, marginCheck_sound D M NT b hh.2⟩

end ScaledBox
end ImbalancedChen.VariableEnvelope
