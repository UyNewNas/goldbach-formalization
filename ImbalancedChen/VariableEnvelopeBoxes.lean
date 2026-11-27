import ImbalancedChen.VariableEnvelopeRegularity

/-!
# Rational boxes for the actual variable envelope

The seven entries below are exactly the six `v` intervals and the `B` interval
used by `phi_range` in the prefix certificates. The extra `v(y)` is dominated
on the ordered domain. Bounds are interval proofs, not corner sampling.
-/

namespace ImbalancedChen.VariableEnvelope

def maxSeven {α : Type*} [LinearOrder α] (a b c d e f g : α) : α :=
  max a (max b (max c (max d (max e (max f g)))))

theorem maxSeven_le_iff {α : Type*} [LinearOrder α] {a b c d e f g t : α} :
    maxSeven a b c d e f g ≤ t ↔
      a ≤ t ∧ b ≤ t ∧ c ≤ t ∧ d ≤ t ∧ e ≤ t ∧ f ≤ t ∧ g ≤ t := by
  simp [maxSeven]

theorem maxSeven_mono {α : Type*} [LinearOrder α]
    {a b c d e f g a' b' c' d' e' f' g' : α}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (he : e ≤ e') (hf : f ≤ f') (hg : g ≤ g') :
    maxSeven a b c d e f g ≤ maxSeven a' b' c' d' e' f' g' :=
  max_le_max ha (max_le_max hb (max_le_max hc
    (max_le_max hd (max_le_max he (max_le_max hf hg)))))

theorem cast_maxSeven (a b c d e f g : ℚ) :
    ((maxSeven a b c d e f g : ℚ) : ℝ) =
      maxSeven (a : ℝ) b c d e f g := by simp [maxSeven]

theorem maxSeven_sub_le {a b c d e f g a' b' c' d' e' f' g' δ : ℚ}
    (ha : a' - a ≤ δ) (hb : b' - b ≤ δ) (hc : c' - c ≤ δ)
    (hd : d' - d ≤ δ) (he : e' - e ≤ δ) (hf : f' - f ≤ δ) (hg : g' - g ≤ δ) :
    maxSeven a' b' c' d' e' f' g' - maxSeven a b c d e f g ≤ δ := by
  have hm : maxSeven a' b' c' d' e' f' g' ≤
      maxSeven (a + δ) (b + δ) (c + δ) (d + δ) (e + δ) (f + δ) (g + δ) :=
    maxSeven_mono (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
  have heq : maxSeven (a + δ) (b + δ) (c + δ) (d + δ) (e + δ) (f + δ) (g + δ) =
      maxSeven a b c d e f g + δ := by simp [maxSeven, max_add_add_right]
  rw [heq] at hm
  linarith

theorem maxSeven_v_eq_original {x y z : ℝ} (h : Ordered x y z) :
    maxSeven (v x) (v y) (v (x + y)) (v (x + y + z))
      (v (x + z)) (v (y + z)) (B z) = original x y z := by
  have hy : y ≤ mu := h.2.2.1.trans h.2.2.2
  have hxy : v y ≤ v x := by
    rw [v_eq_A hy, v_eq_A h.2.2.2]
    dsimp [A]; linarith [h.2.2.1]
  rw [original_eq_six h]
  apply le_antisymm
  · rw [maxSeven_le_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact v_le_six x y z
    · exact hxy.trans (v_le_six x y z)
    all_goals simp [six]
  · simp only [six, max_le_iff]
    all_goals simp [maxSeven]

/-- Endpoints may be unordered; feasibility is checked separately. -/
structure RationalBox where
  lx : ℚ
  ux : ℚ
  ly : ℚ
  uy : ℚ
  lz : ℚ
  uz : ℚ
  deriving DecidableEq, Repr

namespace RationalBox

def InBox (b : RationalBox) (x y z : ℝ) : Prop :=
  (b.lx : ℝ) ≤ x ∧ x ≤ b.ux ∧ (b.ly : ℝ) ≤ y ∧ y ≤ b.uy ∧
    (b.lz : ℝ) ≤ z ∧ z ≤ b.uz

def ValidPoint (b : RationalBox) (x y z : ℝ) : Prop :=
  b.InBox x y z ∧ Ordered x y z

def WellFormed (b : RationalBox) : Prop := b.lx ≤ b.ux ∧ b.ly ≤ b.uy ∧ b.lz ≤ b.uz

def lower (b : RationalBox) : ℚ :=
  maxSeven (qVLo b.lx b.ux) (qVLo b.ly b.uy)
    (qVLo (b.lx + b.ly) (b.ux + b.uy))
    (qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
    (qVLo (b.lx + b.lz) (b.ux + b.uz))
    (qVLo (b.ly + b.lz) (b.uy + b.uz)) (qB b.uz)

def upper (b : RationalBox) : ℚ :=
  maxSeven (qVHi b.lx b.ux) (qVHi b.ly b.uy)
    (qVHi (b.lx + b.ly) (b.ux + b.uy))
    (qVHi (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz))
    (qVHi (b.lx + b.lz) (b.ux + b.uz))
    (qVHi (b.ly + b.lz) (b.uy + b.uz)) (qB b.lz)

def width (b : RationalBox) : ℚ :=
  max 0 (max (b.ux - b.lx) (max (b.uy - b.ly) (b.uz - b.lz)))

theorem wellFormed_of_inBox {b : RationalBox} {x y z : ℝ} (h : b.InBox x y z) :
    b.WellFormed := by
  rcases h with ⟨hlx, hux, hly, huy, hlz, huz⟩
  exact ⟨Rat.cast_le.mp (hlx.trans hux), Rat.cast_le.mp (hly.trans huy),
    Rat.cast_le.mp (hlz.trans huz)⟩

theorem lower_le_original {b : RationalBox} {x y z : ℝ} (h : b.ValidPoint x y z) :
    (b.lower : ℝ) ≤ original x y z := by
  rcases h with ⟨⟨hlx, hux, hly, huy, hlz, huz⟩, ho⟩
  rw [← maxSeven_v_eq_original ho, lower, cast_maxSeven]
  apply maxSeven_mono
  · exact qVLo_le_v hlx hux
  · exact qVLo_le_v hly huy
  · apply qVLo_le_v <;> push_cast <;> linarith
  · apply qVLo_le_v <;> push_cast <;> linarith
  · apply qVLo_le_v <;> push_cast <;> linarith
  · apply qVLo_le_v <;> push_cast <;> linarith
  · rw [cast_qB]; dsimp [B]; linarith

theorem original_le_upper {b : RationalBox} {x y z : ℝ} (h : b.ValidPoint x y z) :
    original x y z ≤ (b.upper : ℝ) := by
  rcases h with ⟨⟨hlx, hux, hly, huy, hlz, huz⟩, ho⟩
  rw [← maxSeven_v_eq_original ho, upper, cast_maxSeven]
  apply maxSeven_mono
  · exact v_le_qVHi hlx hux
  · exact v_le_qVHi hly huy
  · apply v_le_qVHi <;> push_cast <;> linarith
  · apply v_le_qVHi <;> push_cast <;> linarith
  · apply v_le_qVHi <;> push_cast <;> linarith
  · apply v_le_qVHi <;> push_cast <;> linarith
  · rw [cast_qB]; dsimp [B]; linarith

theorem enclosure {b : RationalBox} {x y z : ℝ} (h : b.ValidPoint x y z) :
    (b.lower : ℝ) ≤ original x y z ∧ original x y z ≤ (b.upper : ℝ) :=
  ⟨lower_le_original h, original_le_upper h⟩

theorem width_nonneg (b : RationalBox) : 0 ≤ b.width := le_max_left _ _

theorem coordinate_widths_le (b : RationalBox) :
    b.ux - b.lx ≤ b.width ∧ b.uy - b.ly ≤ b.width ∧ b.uz - b.lz ≤ b.width := by
  simp [width]

/-- Exact rational error goes to zero linearly with the maximum side width. -/
theorem upper_sub_lower_le {b : RationalBox} (h : b.WellFormed) :
    b.upper - b.lower ≤ 9 / 2 * b.width := by
  rcases h with ⟨hx, hy, hz⟩
  have hw := b.coordinate_widths_le
  have hw0 := b.width_nonneg
  unfold upper lower
  apply maxSeven_sub_le
  · have hh := qVHi_sub_qVLo_le hx; linarith [hw.1]
  · have hh := qVHi_sub_qVLo_le hy; linarith [hw.2.1]
  · have hh := qVHi_sub_qVLo_le (add_le_add hx hy); linarith [hw.1, hw.2.1]
  · have hh := qVHi_sub_qVLo_le (add_le_add (add_le_add hx hy) hz)
    linarith [hw.1, hw.2.1, hw.2.2]
  · have hh := qVHi_sub_qVLo_le (add_le_add hx hz); linarith [hw.1, hw.2.2]
  · have hh := qVHi_sub_qVLo_le (add_le_add hy hz); linarith [hw.2.1, hw.2.2]
  · dsimp [qB]; linarith [hw.2.2]

theorem enclosure_error {b : RationalBox} {x y z : ℝ} (h : b.ValidPoint x y z) :
    0 ≤ original x y z - b.lower ∧
    original x y z - b.lower ≤ (9 / 2 : ℝ) * b.width ∧
    0 ≤ (b.upper : ℝ) - original x y z ∧
    (b.upper : ℝ) - original x y z ≤ (9 / 2 : ℝ) * b.width := by
  have hl := lower_le_original h
  have hu := original_le_upper h
  have he : (b.upper : ℝ) - b.lower ≤ (9 / 2 : ℝ) * b.width := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr (upper_sub_lower_le (wellFormed_of_inBox h.1))
    norm_num at hh ⊢
    exact hh
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- An explicit epsilon form, including zero-width boxes. -/
theorem error_lt_of_width_lt {b : RationalBox} {x y z ε : ℝ}
    (h : b.ValidPoint x y z) (hw : (b.width : ℝ) < 2 / 9 * ε) :
    original x y z - b.lower < ε ∧ (b.upper : ℝ) - original x y z < ε := by
  have he := enclosure_error h
  constructor <;> linarith [he.2.1, he.2.2.2]

def witnessZ (b : RationalBox) : ℚ := max 0 b.lz
def witnessY (b : RationalBox) : ℚ := max b.witnessZ b.ly
def witnessX (b : RationalBox) : ℚ := max b.witnessY b.lx

/-- A finite rational feasibility test; it constructs an actual ordered point. -/
def feasible (b : RationalBox) : Bool :=
  decide (b.witnessZ ≤ b.uz ∧ b.witnessY ≤ b.uy ∧
    b.witnessX ≤ b.ux ∧ b.witnessX ≤ 25 / 128)

theorem feasible_sound {b : RationalBox} (h : b.feasible = true) :
    b.ValidPoint b.witnessX b.witnessY b.witnessZ := by
  have hh : b.witnessZ ≤ b.uz ∧ b.witnessY ≤ b.uy ∧
      b.witnessX ≤ b.ux ∧ b.witnessX ≤ 25 / 128 := by simpa [feasible] using h
  have hz0 : (0 : ℚ) ≤ b.witnessZ := le_max_left _ _
  have hzy : b.witnessZ ≤ b.witnessY := le_max_left _ _
  have hyx : b.witnessY ≤ b.witnessX := le_max_left _ _
  have hlx : b.lx ≤ b.witnessX := le_max_right _ _
  have hly : b.ly ≤ b.witnessY := le_max_right _ _
  have hlz : b.lz ≤ b.witnessZ := le_max_right _ _
  constructor
  · exact ⟨Rat.cast_le.mpr hlx, Rat.cast_le.mpr hh.2.2.1,
      Rat.cast_le.mpr hly, Rat.cast_le.mpr hh.2.1,
      Rat.cast_le.mpr hlz, Rat.cast_le.mpr hh.1⟩
  · refine ⟨?_, Rat.cast_le.mpr hzy, Rat.cast_le.mpr hyx, ?_⟩
    · exact_mod_cast hz0
    · have hc := Rat.cast_le (K := ℝ) |>.mpr hh.2.2.2
      norm_num [mu] at hc ⊢
      exact hc

theorem feasible_complete {b : RationalBox} {x y z : ℝ} (h : b.ValidPoint x y z) :
    b.feasible = true := by
  rcases h with ⟨⟨hlx, hux, hly, huy, hlz, huz⟩, hz0, hzy, hyx, hxmu⟩
  have hwz : (b.witnessZ : ℝ) ≤ z := by
    simp only [witnessZ, Rat.cast_max, Rat.cast_zero]
    exact max_le hz0 hlz
  have hwy : (b.witnessY : ℝ) ≤ y := by
    simp only [witnessY, Rat.cast_max]
    exact max_le (hwz.trans hzy) hly
  have hwx : (b.witnessX : ℝ) ≤ x := by
    simp only [witnessX, Rat.cast_max]
    exact max_le (hwy.trans hyx) hlx
  have hmu : b.witnessX ≤ (25 / 128 : ℚ) := by
    have hh := hwx.trans hxmu
    dsimp [mu] at hh
    apply Rat.cast_le (K := ℝ) |>.mp
    norm_num
    exact hh
  simpa only [feasible, decide_eq_true_eq] using
    And.intro (Rat.cast_le.mp (hwz.trans huz))
      ⟨Rat.cast_le.mp (hwy.trans huy), Rat.cast_le.mp (hwx.trans hux), hmu⟩

theorem feasible_iff (b : RationalBox) :
    b.feasible = true ↔ ∃ x y z : ℝ, b.ValidPoint x y z := by
  constructor
  · intro h; exact ⟨_, _, _, feasible_sound h⟩
  · rintro ⟨x, y, z, h⟩; exact feasible_complete h

/-- A successful margin certificate always certifies a nonempty effective box. -/
def marginCheck (b : RationalBox) (η : ℚ) : Bool :=
  b.feasible && decide (0 < b.lower - 3 * b.ux - η)

theorem margin_of_rational_check {b : RationalBox} {η : ℚ}
    (hc : 0 < b.lower - 3 * b.ux - η) {x y z : ℝ} (h : b.ValidPoint x y z) :
    0 < original x y z - 3 * x - η := by
  have hcr : (0 : ℝ) < b.lower - 3 * (b.ux : ℝ) - η := by exact_mod_cast hc
  have hl := lower_le_original h
  have hx := h.1.2.1
  linarith

theorem marginCheck_sound {b : RationalBox} {η : ℚ} (h : b.marginCheck η = true) :
    (∃ x y z : ℝ, b.ValidPoint x y z) ∧
      ∀ x y z : ℝ, b.ValidPoint x y z → 0 < original x y z - 3 * x - η := by
  have hh : b.feasible = true ∧ 0 < b.lower - 3 * b.ux - η := by
    simpa [marginCheck] using h
  exact ⟨(feasible_iff b).mp hh.1, fun _ _ _ hp => margin_of_rational_check hh.2 hp⟩

theorem marginCheck_false_of_empty {b : RationalBox}
    (h : ¬ ∃ x y z : ℝ, b.ValidPoint x y z) (η : ℚ) : b.marginCheck η = false := by
  have hf : b.feasible = false := by
    cases hb : b.feasible
    · rfl
    · exact False.elim (h ((feasible_iff b).mp hb))
  simp [marginCheck, hf]

end RationalBox
end ImbalancedChen.VariableEnvelope
