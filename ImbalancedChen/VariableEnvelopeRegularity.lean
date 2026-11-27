import ImbalancedChen.VariableEnvelopeConsequences

/-!
# Rational interval bounds and regularity of the variable envelope

The rational scalar interfaces retain the affine expressions used by the
prefix certificates. Bounds hold throughout an interval, including intervals
that cross the peak of `v`. The six-branch regularity results below use no
ordering assumptions; returning to the gated expression requires `Ordered`.
-/

namespace ImbalancedChen.VariableEnvelope

def qA (t : ℚ) : ℚ := (1 + t) / 2
def qC (t : ℚ) : ℚ := 57 / 64 - 3 / 2 * t
def qB (t : ℚ) : ℚ := 153 / 256 - 3 / 8 * t
def qV (t : ℚ) : ℚ := min (qA t) (qC t)
def qVLo (l u : ℚ) : ℚ := min (qA l) (qC u)
def qVHi (l u : ℚ) : ℚ :=
  if l ≤ 25 / 128 ∧ 25 / 128 ≤ u then 153 / 256 else max (qV l) (qV u)

theorem cast_qA (t : ℚ) : (qA t : ℝ) = A t := by
  simp [qA, A]

theorem cast_qC (t : ℚ) : (qC t : ℝ) = C t := by
  simp [qC, C]

theorem cast_qB (t : ℚ) : (qB t : ℝ) = B t := by
  simp [qB, B, cap]

theorem cast_qV (t : ℚ) : (qV t : ℝ) = v t := by
  simp [qV, v_eq_min, cast_qA, cast_qC]

theorem cast_qVLo (l u : ℚ) : (qVLo l u : ℝ) = min (A l) (C u) := by
  simp [qVLo, cast_qA, cast_qC]

theorem qVLo_le_v {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    (qVLo l u : ℝ) ≤ v t := by
  rw [cast_qVLo, v_eq_min]
  apply min_le_min
  · dsimp [A]; linarith
  · dsimp [C]; linarith

theorem v_le_qVHi {l u : ℚ} {t : ℝ} (hl : (l : ℝ) ≤ t) (hu : t ≤ (u : ℝ)) :
    v t ≤ (qVHi l u : ℝ) := by
  unfold qVHi
  split_ifs with h
  · simpa [cap] using v_le_cap t
  · simp only [Rat.cast_max, cast_qV]
    by_cases hlu : u ≤ 25 / 128
    · have hur : (u : ℝ) ≤ mu := by
        have hh : (u : ℝ) ≤ ((25 / 128 : ℚ) : ℝ) := Rat.cast_le.mpr hlu
        norm_num [mu] at hh ⊢
        exact hh
      rw [v_eq_A (hu.trans hur), v_eq_A hur]
      apply le_max_of_le_right
      dsimp [A]; linarith
    · have hll : (25 / 128 : ℚ) < l := by
        have hmu : (25 / 128 : ℚ) ≤ u := le_of_not_ge hlu
        exact lt_of_not_ge (fun hh => h ⟨hh, hmu⟩)
      have hlr : mu ≤ (l : ℝ) := by
        have hh : ((25 / 128 : ℚ) : ℝ) ≤ (l : ℝ) := Rat.cast_le.mpr (le_of_lt hll)
        norm_num [mu] at hh ⊢
        exact hh
      rw [v_eq_C (hlr.trans hl), v_eq_C hlr]
      apply le_max_of_le_left
      dsimp [C]; linarith

theorem qV_eq_qA {t : ℚ} (h : t ≤ 25 / 128) : qV t = qA t := by
  apply min_eq_left
  dsimp [qA, qC]; linarith

theorem qV_eq_qC {t : ℚ} (h : 25 / 128 ≤ t) : qV t = qC t := by
  apply min_eq_right
  dsimp [qA, qC]; linarith

/-- The interval enclosure shrinks at most linearly, even when it crosses `mu`. -/
theorem qVHi_sub_qVLo_le {l u : ℚ} (hlu : l ≤ u) :
    qVHi l u - qVLo l u ≤ 3 / 2 * (u - l) := by
  unfold qVHi qVLo
  split_ifs with h
  · rcases h with ⟨hl, hu⟩
    rcases le_total (qA l) (qC u) with ha | hc
    · rw [min_eq_left ha]; dsimp [qA]; linarith
    · rw [min_eq_right hc]; dsimp [qC]; linarith
  · by_cases hu : u ≤ 25 / 128
    · rw [qV_eq_qA (hlu.trans hu), qV_eq_qA hu]
      have hmono : qA l ≤ qA u := by dsimp [qA]; linarith
      have hsmall : qA l ≤ qC u := by dsimp [qA, qC]; linarith
      rw [max_eq_right hmono, min_eq_left hsmall]
      dsimp [qA]; linarith
    · have hl : (25 / 128 : ℚ) ≤ l := by
        exact le_of_not_ge (fun hh => h ⟨hh, le_of_not_ge hu⟩)
      rw [qV_eq_qC hl, qV_eq_qC (hl.trans hlu)]
      have hmono : qC u ≤ qC l := by dsimp [qC]; linarith
      have hsmall : qC u ≤ qA l := by dsimp [qA, qC]; linarith
      rw [max_eq_left hmono, min_eq_right hsmall]
      dsimp [qC]; linarith

private theorem abs_min_sub_min_le {a b c e d : ℝ}
    (hac : |a - c| ≤ d) (hbe : |b - e| ≤ d) :
    |min a b - min c e| ≤ d := by
  exact (_root_.abs_min_sub_min_le_max a b c e).trans (max_le hac hbe)

private theorem abs_max_sub_max_le {a b c e d : ℝ}
    (hac : |a - c| ≤ d) (hbe : |b - e| ≤ d) :
    |max a b - max c e| ≤ d := by
  exact (_root_.abs_max_sub_max_le_max a b c e).trans (max_le hac hbe)

/-- The scalar tent has Lipschitz constant `3/2`, globally. -/
theorem v_abs_sub_le_of_le {s t d : ℝ} (h : |s - t| ≤ d) :
    |v s - v t| ≤ 3 / 2 * d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans h
  rcases abs_le.mp h with ⟨h₁, h₂⟩
  rw [v_eq_min, v_eq_min]
  apply abs_min_sub_min_le
  · apply abs_le.mpr; dsimp [A]; constructor <;> linarith
  · apply abs_le.mpr; dsimp [C]; constructor <;> linarith

theorem v_abs_sub_le (s t : ℝ) : |v s - v t| ≤ 3 / 2 * |s - t| :=
  v_abs_sub_le_of_le (le_refl _)

/-- A common coordinate error gives a global `9/2` bound for all six branches. -/
theorem six_abs_sub_le {x y z x' y' z' d : ℝ}
    (hx : |x - x'| ≤ d) (hy : |y - y'| ≤ d) (hz : |z - z'| ≤ d) :
    |six x y z - six x' y' z'| ≤ 9 / 2 * d := by
  have hd : 0 ≤ d := (abs_nonneg _).trans hx
  have hxy : |(x + y) - (x' + y')| ≤ 2 * d := by
    rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
    rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
    apply abs_le.mpr; constructor <;> linarith
  have hxyz : |(x + y + z) - (x' + y' + z')| ≤ 3 * d := by
    rcases abs_le.mp hxy with ⟨hxy₁, hxy₂⟩
    rcases abs_le.mp hz with ⟨hz₁, hz₂⟩
    apply abs_le.mpr; constructor <;> linarith
  have hxz : |(x + z) - (x' + z')| ≤ 2 * d := by
    rcases abs_le.mp hx with ⟨hx₁, hx₂⟩
    rcases abs_le.mp hz with ⟨hz₁, hz₂⟩
    apply abs_le.mpr; constructor <;> linarith
  have hyz : |(y + z) - (y' + z')| ≤ 2 * d := by
    rcases abs_le.mp hy with ⟨hy₁, hy₂⟩
    rcases abs_le.mp hz with ⟨hz₁, hz₂⟩
    apply abs_le.mpr; constructor <;> linarith
  have h₁ : |v x - v x'| ≤ 9 / 2 * d := by
    have := v_abs_sub_le_of_le hx; linarith
  have h₂ : |v (x + y) - v (x' + y')| ≤ 9 / 2 * d := by
    have := v_abs_sub_le_of_le hxy; linarith
  have h₃ : |v (x + y + z) - v (x' + y' + z')| ≤ 9 / 2 * d := by
    have := v_abs_sub_le_of_le hxyz; linarith
  have h₄ : |B z - B z'| ≤ 9 / 2 * d := by
    rcases abs_le.mp hz with ⟨hz₁, hz₂⟩
    apply abs_le.mpr; dsimp [B]; constructor <;> linarith
  have h₅ : |v (x + z) - v (x' + z')| ≤ 9 / 2 * d := by
    have := v_abs_sub_le_of_le hxz; linarith
  have h₆ : |v (y + z) - v (y' + z')| ≤ 9 / 2 * d := by
    have := v_abs_sub_le_of_le hyz; linarith
  exact abs_max_sub_max_le h₁ (abs_max_sub_max_le h₂ (abs_max_sub_max_le h₃
    (abs_max_sub_max_le h₄ (abs_max_sub_max_le h₅ h₆))))

/-- Explicit Lipschitz inequality for the maximum coordinate distance. -/
theorem six_lipschitz_max (x y z x' y' z' : ℝ) :
    |six x y z - six x' y' z'| ≤
      9 / 2 * max |x - x'| (max |y - y'| |z - z'|) := by
  apply six_abs_sub_le
  · exact le_max_left _ _
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_right _ _)

/-- The gated formula inherits the bound when both points satisfy the proved domain. -/
theorem original_abs_sub_le {x y z x' y' z' d : ℝ}
    (h : Ordered x y z) (h' : Ordered x' y' z')
    (hx : |x - x'| ≤ d) (hy : |y - y'| ≤ d) (hz : |z - z'| ≤ d) :
    |original x y z - original x' y' z'| ≤ 9 / 2 * d := by
  rw [original_eq_six h, original_eq_six h']
  exact six_abs_sub_le hx hy hz

theorem original_lipschitz_max {x y z x' y' z' : ℝ}
    (h : Ordered x y z) (h' : Ordered x' y' z') :
    |original x y z - original x' y' z'| ≤
      9 / 2 * max |x - x'| (max |y - y'| |z - z'|) := by
  rw [original_eq_six h, original_eq_six h']
  exact six_lipschitz_max x y z x' y' z'

end ImbalancedChen.VariableEnvelope
