import ImbalancedChen.VariableEnvelopeRegularity

/-!
# Integer-scaled bounds used by the existing variable-prefix certificates

The division in this module is integer Euclidean division. All denominators
are positive, so it is exactly Python's `//`; `ceilDiv` is the certificate's
`-((-n)//d)`, including when the numerator is negative. The crossing integer
must satisfy `128 * M = 25 * D`. No extension beyond the original VE domain
is asserted here.
-/

namespace ImbalancedChen.VariableEnvelope

/-- Exact signed ceiling division from the existing certificate scripts. -/
def ceilDiv (n d : ℤ) : ℤ := -((-n) / d)

/-- The certificate's `v_lo`, retaining the downward integer rounding. -/
def scaledVLo (D l u : ℤ) : ℤ := min ((D + l) / 2) ((57 * D - 96 * u) / 64)

/-- The certificate's `v_point_hi`, retaining the upward integer rounding. -/
def scaledVPointHi (D t : ℤ) : ℤ :=
  min (ceilDiv (D + t) 2) (ceilDiv (57 * D - 96 * t) 64)

/-- The certificate's `v_hi`, with both crossing endpoints included. -/
def scaledVHi (D M l u : ℤ) : ℤ :=
  if l ≤ M ∧ M ≤ u then ceilDiv (153 * D) 256
  else max (scaledVPointHi D l) (scaledVPointHi D u)

def scaledBLo (D u : ℤ) : ℤ := (153 * D - 96 * u) / 256

def scaledBHi (D l : ℤ) : ℤ := ceilDiv (153 * D - 96 * l) 256

/-- Euclidean division rounds down, with an error strictly less than one. -/
theorem floorDiv_bounds (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / d ∧
    (n : ℝ) / d < ((n / d : ℤ) : ℝ) + 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : (n / d : ℤ) * d ≤ n := Int.ediv_mul_le n (ne_of_gt hd)
  have hhi : n < (n / d + 1) * d := by
    have hr := Int.emod_lt_of_pos n hd
    have he := Int.emod_add_mul_ediv n d
    nlinarith
  constructor
  · apply (le_div_iff₀ hdR).2
    exact_mod_cast hlo
  · apply (div_lt_iff₀ hdR).2
    exact_mod_cast hhi

/-- Signed ceiling division rounds up, with an error strictly less than one. -/
theorem ceilDiv_bounds (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / d ≤ (ceilDiv n d : ℝ) ∧
    (ceilDiv n d : ℝ) < (n : ℝ) / d + 1 := by
  have h := floorDiv_bounds (-n) d hd
  dsimp [ceilDiv]
  push_cast at *
  simp only [neg_div] at h
  constructor <;> linarith [h.1, h.2]

/-- Both active affine branches are bounded by their correctly rounded interval endpoints. -/
theorem scaled_v_lower (D l u : ℤ) (hD : 0 < D) {t : ℝ}
    (hl : (l : ℝ) ≤ D * t) (hu : D * t ≤ u) :
    (scaledVLo D l u : ℝ) ≤ D * v t := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have ha := (floorDiv_bounds (D + l) 2 (by norm_num)).1
  have hc := (floorDiv_bounds (57 * D - 96 * u) 64 (by norm_num)).1
  push_cast at ha hc
  rw [v_eq_min, mul_min_of_nonneg _ _ hD0, scaledVLo, Int.cast_min]
  apply le_min
  · have hm := min_le_left (((D + l) / 2 : ℤ) : ℝ) (((57 * D - 96 * u) / 64 : ℤ) : ℝ)
    dsimp [A]
    nlinarith
  · have hm := min_le_right (((D + l) / 2 : ℤ) : ℝ) (((57 * D - 96 * u) / 64 : ℤ) : ℝ)
    dsimp [C]
    nlinarith

/-- The crossing test and endpoint maxima bound every real point of the interval. -/
theorem scaled_v_upper (D M l u : ℤ) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {t : ℝ}
    (hl : (l : ℝ) ≤ D * t) (hu : D * t ≤ u) :
    D * v t ≤ (scaledVHi D M l u : ℝ) := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have hMR : (128 : ℝ) * M = 25 * D := by exact_mod_cast hM
  have hcap := mul_le_mul_of_nonneg_left (v_le_cap t) hD0
  have hA := mul_le_mul_of_nonneg_left (show v t ≤ A t by rw [v_eq_min]; exact min_le_left _ _) hD0
  have hC := mul_le_mul_of_nonneg_left (show v t ≤ C t by rw [v_eq_min]; exact min_le_right _ _) hD0
  dsimp [A, C, cap] at hcap hA hC
  unfold scaledVHi
  split_ifs with hcross
  · have hc := (ceilDiv_bounds (153 * D) 256 (by norm_num)).1
    push_cast at hc
    nlinarith
  · by_cases hleft : u < M
    · have hleftR : (u : ℝ) < M := by exact_mod_cast hleft
      apply le_trans _ (show (scaledVPointHi D u : ℝ) ≤ ↑(max (scaledVPointHi D l) (scaledVPointHi D u)) by
        rw [Int.cast_max]; exact le_max_right _ _)
      rw [scaledVPointHi, Int.cast_min]
      have ha := (ceilDiv_bounds (D + u) 2 (by norm_num)).1
      have hc := (ceilDiv_bounds (57 * D - 96 * u) 64 (by norm_num)).1
      push_cast at ha hc
      exact le_min (by nlinarith) (by nlinarith)
    · have hright : M < l := by omega
      have hrightR : (M : ℝ) < l := by exact_mod_cast hright
      apply le_trans _ (show (scaledVPointHi D l : ℝ) ≤ ↑(max (scaledVPointHi D l) (scaledVPointHi D u)) by
        rw [Int.cast_max]; exact le_max_left _ _)
      rw [scaledVPointHi, Int.cast_min]
      have ha := (ceilDiv_bounds (D + l) 2 (by norm_num)).1
      have hc := (ceilDiv_bounds (57 * D - 96 * l) 64 (by norm_num)).1
      push_cast at ha hc
      exact le_min (by nlinarith) (by nlinarith)

/-- Soundness of the exact old `v_lo` / `v_hi` integer algorithm. -/
theorem scaled_v_bounds (D M l u : ℤ) (hD : 0 < D)
    (hM : 128 * M = 25 * D) {t : ℝ}
    (hl : (l : ℝ) ≤ D * t) (hu : D * t ≤ u) :
    (scaledVLo D l u : ℝ) ≤ D * v t ∧
    D * v t ≤ (scaledVHi D M l u : ℝ) :=
  ⟨scaled_v_lower D l u hD hl hu, scaled_v_upper D M l u hD hM hl hu⟩

/-- The decreasing B branch uses the upper box endpoint for its lower bound. -/
theorem scaled_B_bounds (D l u : ℤ) {t : ℝ}
    (hl : (l : ℝ) ≤ D * t) (hu : D * t ≤ u) :
    (scaledBLo D u : ℝ) ≤ D * B t ∧
    D * B t ≤ (scaledBHi D l : ℝ) := by
  have hlo := (floorDiv_bounds (153 * D - 96 * u) 256 (by norm_num)).1
  have hhi := (ceilDiv_bounds (153 * D - 96 * l) 256 (by norm_num)).1
  push_cast at hlo hhi
  dsimp [scaledBLo, scaledBHi, B, cap]
  constructor <;> nlinarith




/-- Scaling the normalized rational A branch gives the script's exact numerator. -/
theorem scaled_qA (D t : ℤ) (hD : 0 < D) :
    (D : ℝ) * (qA ((t : ℚ) / D) : ℝ) = ((D : ℝ) + t) / 2 := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  simp only [cast_qA, Rat.cast_div, Rat.cast_intCast, A]
  field_simp

/-- Scaling the normalized rational C branch gives the script's exact numerator. -/
theorem scaled_qC (D t : ℤ) (hD : 0 < D) :
    (D : ℝ) * (qC ((t : ℚ) / D) : ℝ) = (57 * (D : ℝ) - 96 * t) / 64 := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  simp only [cast_qC, Rat.cast_div, Rat.cast_intCast, C]
  field_simp
  ring

/-- Scaling the normalized rational B branch gives the script's exact numerator. -/
theorem scaled_qB (D t : ℤ) (hD : 0 < D) :
    (D : ℝ) * (qB ((t : ℚ) / D) : ℝ) = (153 * (D : ℝ) - 96 * t) / 256 := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  simp only [cast_qB, Rat.cast_div, Rat.cast_intCast, B, cap]
  field_simp
  ring

/-- The integer lower bound is within one scaled unit of the rational lower bound. -/
theorem scaledVLo_rounding (D l u : ℤ) (hD : 0 < D) :
    (scaledVLo D l u : ℝ) ≤ D * (qVLo ((l : ℚ) / D) ((u : ℚ) / D) : ℝ) ∧
    D * (qVLo ((l : ℚ) / D) ((u : ℚ) / D) : ℝ) ≤ (scaledVLo D l u : ℝ) + 1 := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have ha := floorDiv_bounds (D + l) 2 (by norm_num)
  have hc := floorDiv_bounds (57 * D - 96 * u) 64 (by norm_num)
  push_cast at ha hc
  simp only [qVLo, Rat.cast_min, mul_min_of_nonneg _ _ hD0,
    scaled_qA D l hD, scaled_qC D u hD, scaledVLo, Int.cast_min]
  constructor
  · exact min_le_min ha.1 hc.1
  · simpa only [min_add_add_right] using min_le_min (le_of_lt ha.2) (le_of_lt hc.2)

/-- The endpoint upper bound is within one scaled unit of the exact rational value. -/
theorem scaledVPointHi_rounding (D t : ℤ) (hD : 0 < D) :
    D * (qV ((t : ℚ) / D) : ℝ) ≤ (scaledVPointHi D t : ℝ) ∧
    (scaledVPointHi D t : ℝ) ≤ D * (qV ((t : ℚ) / D) : ℝ) + 1 := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  have ha := ceilDiv_bounds (D + t) 2 (by norm_num)
  have hc := ceilDiv_bounds (57 * D - 96 * t) 64 (by norm_num)
  push_cast at ha hc
  simp only [qV, Rat.cast_min, mul_min_of_nonneg _ _ hD0,
    scaled_qA D t hD, scaled_qC D t hD, scaledVPointHi, Int.cast_min]
  constructor
  · exact min_le_min ha.1 hc.1
  · simpa only [min_add_add_right] using min_le_min (le_of_lt ha.2) (le_of_lt hc.2)

/-- The script's integer crossing test is exactly the normalized rational crossing test. -/
theorem scaled_crossing_iff (D M l u : ℤ) (hD : 0 < D) (hM : 128 * M = 25 * D) :
    ((l : ℚ) / D ≤ 25 / 128 ∧ 25 / 128 ≤ (u : ℚ) / D) ↔ l ≤ M ∧ M ≤ u := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hMQ : (128 : ℚ) * M = 25 * D := by exact_mod_cast hM
  have hmu : (25 / 128 : ℚ) * D = M := by linarith
  simp only [div_le_iff₀ hDQ, le_div_iff₀ hDQ, hmu]
  norm_cast

/-- The exact old upper algorithm is at most one scaled unit above the rational bound. -/
theorem scaledVHi_rounding (D M l u : ℤ) (hD : 0 < D) (hM : 128 * M = 25 * D) :
    D * (qVHi ((l : ℚ) / D) ((u : ℚ) / D) : ℝ) ≤ (scaledVHi D M l u : ℝ) ∧
    (scaledVHi D M l u : ℝ) ≤ D * (qVHi ((l : ℚ) / D) ((u : ℚ) / D) : ℝ) + 1 := by
  have hD0 : (0 : ℝ) ≤ D := by exact_mod_cast le_of_lt hD
  unfold qVHi scaledVHi
  by_cases hcross : l ≤ M ∧ M ≤ u
  · have hcrossQ := (scaled_crossing_iff D M l u hD hM).2 hcross
    simp only [if_pos hcross, if_pos hcrossQ]
    have hh := ceilDiv_bounds (153 * D) 256 (by norm_num)
    push_cast at hh ⊢
    constructor <;> nlinarith [hh.1, hh.2]
  · have hcrossQ : ¬ ((l : ℚ) / D ≤ 25 / 128 ∧ 25 / 128 ≤ (u : ℚ) / D) :=
      fun h => hcross ((scaled_crossing_iff D M l u hD hM).1 h)
    simp only [if_neg hcross, if_neg hcrossQ, Rat.cast_max, Int.cast_max,
      mul_max_of_nonneg _ _ hD0]
    have hl := scaledVPointHi_rounding D l hD
    have hu := scaledVPointHi_rounding D u hD
    constructor
    · exact max_le_max hl.1 hu.1
    · simpa only [max_add_add_right] using max_le_max hl.2 hu.2

/-- The rounded lower B endpoint has error at most one scaled unit. -/
theorem scaledBLo_rounding (D u : ℤ) (hD : 0 < D) :
    (scaledBLo D u : ℝ) ≤ D * (qB ((u : ℚ) / D) : ℝ) ∧
    D * (qB ((u : ℚ) / D) : ℝ) ≤ (scaledBLo D u : ℝ) + 1 := by
  rw [scaled_qB D u hD]
  have hh := floorDiv_bounds (153 * D - 96 * u) 256 (by norm_num)
  push_cast at hh
  exact ⟨hh.1, le_of_lt hh.2⟩

/-- The rounded upper B endpoint has error at most one scaled unit. -/
theorem scaledBHi_rounding (D l : ℤ) (hD : 0 < D) :
    D * (qB ((l : ℚ) / D) : ℝ) ≤ (scaledBHi D l : ℝ) ∧
    (scaledBHi D l : ℝ) ≤ D * (qB ((l : ℚ) / D) : ℝ) + 1 := by
  rw [scaled_qB D l hD]
  have hh := ceilDiv_bounds (153 * D - 96 * l) 256 (by norm_num)
  push_cast at hh
  exact ⟨hh.1, le_of_lt hh.2⟩

end ImbalancedChen.VariableEnvelope
