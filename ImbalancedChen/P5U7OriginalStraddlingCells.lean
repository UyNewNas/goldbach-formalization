import ImbalancedChen.P5U7OriginalRationalCellBounds
import ImbalancedChen.P5U7OriginalOmegaFubini

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Rational boxes may cross either the original triangle boundary or the
Buchstab seam. Local argument intervals are clamped separately to each
genuine piece; min/max joins keep both directions valid on straddling
cells. The bounds concern the actual original kernel restricted to its
triangle. No quadrature value or saved endpoint is evaluated.
-/

namespace ImbalancedChen.P5U7OriginalStraddlingCells

noncomputable section

open Set MeasureTheory LiLiuPrereqBuchstab P2ContinuousSieveRational
open scoped BigOperators

structure Box where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  deriving DecidableEq

def Box.Valid (B : Box) : Prop :=
  0 < B.a ∧ B.a ≤ B.b ∧ B.b ≤ 1 / 3 ∧ 0 < B.c ∧ B.c ≤ B.d

instance (B : Box) : Decidable B.Valid := by unfold Box.Valid; infer_instance

def Box.closed (B : Box) : Set (ℝ × ℝ) :=
  Icc (B.a : ℝ) B.b ×ˢ Icc (B.c : ℝ) B.d

def Box.opened (B : Box) : Set (ℝ × ℝ) :=
  Ioo (B.a : ℝ) B.b ×ˢ Ioo (B.c : ℝ) B.d

def Box.area (B : Box) : ℚ := (B.b - B.a) * (B.d - B.c)
def Box.argLo (B : Box) : ℚ := (1 - B.b - B.d) / B.d
def Box.argHi (B : Box) : ℚ := (1 - B.a - B.c) / B.c
def Box.firstLo (B : Box) : ℚ := min 2 (max 1 B.argLo)
def Box.firstHi (B : Box) : ℚ := max 1 (min 2 B.argHi)
def Box.secondLo (B : Box) : ℚ := min (132 / 59) (max 2 B.argLo)
def Box.secondHi (B : Box) : ℚ := max 2 (min (132 / 59) B.argHi)

def Box.numeratorLower (B : Box) (n : ℕ) : ℚ :=
  if B.argHi ≤ 2 then 1 / B.firstHi
  else if 2 ≤ B.argLo then (1 + logLower n B.secondLo) / B.secondHi
  else min (1 / B.firstHi) ((1 + logLower n B.secondLo) / B.secondHi)
def Box.numeratorUpper (B : Box) (n : ℕ) : ℚ :=
  if B.argHi ≤ 2 then 1 / B.firstLo
  else if 2 ≤ B.argLo then (1 + logUpper n B.secondHi) / B.secondLo
  else max (1 / B.firstLo) ((1 + logUpper n B.secondHi) / B.secondLo)
def Box.lower (B : Box) (n : ℕ) : ℚ := B.numeratorLower n / (B.b * B.d ^ 2)
def Box.upper (B : Box) (n : ℕ) : ℚ := B.numeratorUpper n / (B.a * B.c ^ 2)

theorem Box.real_guards {B : Box} (h : B.Valid) :
    0 < (B.a : ℝ) ∧ (B.a : ℝ) ≤ B.b ∧ (B.b : ℝ) ≤ 1 / 3 ∧
      0 < (B.c : ℝ) ∧ (B.c : ℝ) ≤ B.d := by
  unfold Box.Valid at h
  exact_mod_cast h

theorem Box.clamp_guards (B : Box) :
    1 ≤ B.firstLo ∧ B.firstLo ≤ 2 ∧ 1 ≤ B.firstHi ∧ B.firstHi ≤ 2 ∧
      2 ≤ B.secondLo ∧ B.secondLo ≤ 132 / 59 ∧
      2 ≤ B.secondHi ∧ B.secondHi ≤ 132 / 59 := by
  unfold Box.firstLo Box.firstHi Box.secondLo Box.secondHi
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _,
    le_max_left _ _, max_le (by norm_num) (min_le_left _ _),
    le_min (by norm_num) (le_max_left _ _), min_le_left _ _,
    le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem Box.argument_bounds {B : Box} (hB : B.Valid) {p : ℝ × ℝ}
    (hp : p ∈ B.closed) :
    (B.argLo : ℝ) ≤ p5U7OmegaArgument p.1 p.2 ∧
      p5U7OmegaArgument p.1 p.2 ≤ (B.argHi : ℝ) := by
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hB
  have hu : 0 < p.2 := hc.trans_le hp.2.1
  have hd : 0 < (B.d : ℝ) := hc.trans_le hcd
  have htb : (B.b : ℝ) - p.1 ≥ 0 := sub_nonneg.mpr hp.1.2
  have hdu : (B.d : ℝ) - p.2 ≥ 0 := sub_nonneg.mpr hp.2.2
  have hta : p.1 - (B.a : ℝ) ≥ 0 := sub_nonneg.mpr hp.1.1
  have huc : p.2 - (B.c : ℝ) ≥ 0 := sub_nonneg.mpr hp.2.1
  simp only [Box.argLo, Box.argHi, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
    p5U7OmegaArgument]
  constructor
  · apply (div_le_div_iff₀ hd hu).mpr
    nlinarith [mul_nonneg hd.le htb,
      mul_nonneg hdu (show 0 ≤ 1 - (B.b : ℝ) by linarith)]
  · apply (div_le_div_iff₀ hu hc).mpr
    nlinarith [mul_nonneg hc.le hta,
      mul_nonneg huc (show 0 ≤ 1 - (B.a : ℝ) by linarith)]

theorem Box.numerators_nonneg (B : Box) (n : ℕ) :
    0 ≤ B.numeratorLower n ∧ 0 ≤ B.numeratorUpper n := by
  obtain ⟨hFL, _, hFH, _, hSL, _, hSH, _⟩ := Box.clamp_guards B
  have hlogL := p5U7_logLower_nonneg n B.secondLo hSL
  have hnum2 : 0 ≤ (1 + logLower n B.secondLo) / B.secondHi :=
    div_nonneg (by linarith) (by linarith)
  have hlogU : 0 ≤ logUpper n B.secondHi := by
    have hSHr : (2 : ℝ) ≤ B.secondHi := by exact_mod_cast hSH
    have h := (Real.log_nonneg (show 1 ≤ (B.secondHi : ℝ) - 1 by linarith)).trans
      (log_bounds n B.secondHi hSH).2
    exact_mod_cast h
  have hnumU2 : 0 ≤ (1 + logUpper n B.secondHi) / B.secondLo :=
    div_nonneg (by linarith) (by linarith)
  unfold Box.numeratorLower Box.numeratorUpper
  split_ifs <;> constructor
  all_goals first
    | exact div_nonneg zero_le_one (by linarith)
    | exact hnum2
    | exact hnumU2
    | exact le_min (div_nonneg zero_le_one (by linarith)) hnum2
    | exact (div_nonneg zero_le_one (by linarith : 0 ≤ B.firstLo)).trans (le_max_left _ _)

/-- The two actual Buchstab formulas are joined in the safe direction.
This includes points on the s=2 knot and boxes that straddle the knot. -/
theorem Box.buchstab_enclosure {B : Box} (hB : B.Valid) (n : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ B.closed) (hT : p ∈ p5U7OmegaTriangle) :
    (B.numeratorLower n : ℝ) ≤ buchstab (p5U7OmegaArgument p.1 p.2) ∧
      buchstab (p5U7OmegaArgument p.1 p.2) ≤ (B.numeratorUpper n : ℝ) := by
  let s := p5U7OmegaArgument p.1 p.2
  have hgeo := p5U7Omega_closed_geometry hT
  have hs1 : 1 ≤ s := hgeo.2.2.2.2.1
  have hsM : s ≤ 132 / 59 := hgeo.2.2.2.2.2
  obtain ⟨hlo, hhi⟩ := Box.argument_bounds hB hp
  obtain ⟨hFL, _, _, hFH, hSL, _, _, hSH⟩ := Box.clamp_guards B
  have hfirst (hs2 : s ≤ 2) :
      ((1 / B.firstHi : ℚ) : ℝ) ≤ buchstab s ∧
        buchstab s ≤ ((1 / B.firstLo : ℚ) : ℝ) := by
    have hsl : (B.firstLo : ℝ) ≤ s := by
      simp only [Box.firstLo, Rat.cast_min, Rat.cast_max, Rat.cast_ofNat]
      exact (min_le_right _ _).trans (max_le hs1 hlo)
    have hsu : s ≤ (B.firstHi : ℝ) := by
      simp only [Box.firstHi, Rat.cast_min, Rat.cast_max, Rat.cast_ofNat]
      exact (le_min hs2 hhi).trans (le_max_right _ _)
    exact p5U7_buchstab_first_rational_interval B.firstLo B.firstHi hFL hFH hsl hsu
  have hsecond (hs2 : 2 ≤ s) :
      (((1 + logLower n B.secondLo) / B.secondHi : ℚ) : ℝ) ≤ buchstab s ∧
        buchstab s ≤ (((1 + logUpper n B.secondHi) / B.secondLo : ℚ) : ℝ) := by
    have hsl : (B.secondLo : ℝ) ≤ s := by
      simp only [Box.secondLo, Rat.cast_min, Rat.cast_max, Rat.cast_div, Rat.cast_ofNat]
      exact (min_le_right _ _).trans (max_le hs2 hlo)
    have hsu : s ≤ (B.secondHi : ℝ) := by
      simp only [Box.secondHi, Rat.cast_min, Rat.cast_max, Rat.cast_div, Rat.cast_ofNat]
      exact (le_min hsM hhi).trans (le_max_right _ _)
    exact p5U7_buchstab_second_rational_interval n B.secondLo B.secondHi hSL hSH hsl hsu
  by_cases hF : B.argHi ≤ 2
  · have hFr : (B.argHi : ℝ) ≤ 2 := by exact_mod_cast hF
    simpa only [Box.numeratorLower, Box.numeratorUpper, if_pos hF] using
      hfirst (hhi.trans hFr)
  by_cases hS : 2 ≤ B.argLo
  · have hSr : (2 : ℝ) ≤ B.argLo := by exact_mod_cast hS
    simpa only [Box.numeratorLower, Box.numeratorUpper, if_neg hF, if_pos hS] using
      hsecond (hSr.trans hlo)
  simp only [Box.numeratorLower, Box.numeratorUpper, if_neg hF, if_neg hS]
  by_cases hs2 : s ≤ 2
  · have hw := hfirst hs2
    have hL : (B.numeratorLower n : ℝ) ≤ ((1 / B.firstHi : ℚ) : ℝ) := by
      simp only [Box.numeratorLower, if_neg hF, if_neg hS]
      exact_mod_cast min_le_left (1 / B.firstHi) ((1 + logLower n B.secondLo) / B.secondHi)
    have hU : ((1 / B.firstLo : ℚ) : ℝ) ≤
        ((max (1 / B.firstLo) ((1 + logUpper n B.secondHi) / B.secondLo) : ℚ) : ℝ) := by
      exact_mod_cast le_max_left (1 / B.firstLo) ((1 + logUpper n B.secondHi) / B.secondLo)
    simp only [Box.numeratorLower, if_neg hF, if_neg hS] at hL
    exact ⟨hL.trans hw.1, hw.2.trans hU⟩
  · have hs2' : 2 ≤ s := (lt_of_not_ge hs2).le
    have hw := hsecond hs2'
    have hL : ((min (1 / B.firstHi)
        ((1 + logLower n B.secondLo) / B.secondHi) : ℚ) : ℝ) ≤
        (((1 + logLower n B.secondLo) / B.secondHi : ℚ) : ℝ) := by
      exact_mod_cast (min_le_right (1 / B.firstHi)
        ((1 + logLower n B.secondLo) / B.secondHi))
    have hU : (((1 + logUpper n B.secondHi) / B.secondLo : ℚ) : ℝ) ≤
        ((max (1 / B.firstLo) ((1 + logUpper n B.secondHi) / B.secondLo) : ℚ) : ℝ) := by
      exact_mod_cast (le_max_right (1 / B.firstLo)
        ((1 + logUpper n B.secondHi) / B.secondLo))
    exact ⟨hL.trans hw.1, hw.2.trans hU⟩

theorem Box.enclosure {B : Box} (hB : B.Valid) (n : ℕ)
    {p : ℝ × ℝ} (hp : p ∈ B.closed) (hT : p ∈ p5U7OmegaTriangle) :
    (B.lower n : ℝ) ≤ p5U7OmegaKernel 1 p.1 p.2 ∧
      p5U7OmegaKernel 1 p.1 p.2 ≤ (B.upper n : ℝ) := by
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hB
  have ht : 0 < p.1 := ha.trans_le hp.1.1
  have hu : 0 < p.2 := hc.trans_le hp.2.1
  have hd : 0 < p.1 * p.2 ^ 2 := by positivity
  have hdenL : (B.a : ℝ) * (B.c : ℝ) ^ 2 ≤ p.1 * p.2 ^ 2 :=
    mul_le_mul hp.1.1 (pow_le_pow_left₀ hc.le hp.2.1 2) (by positivity) ht.le
  have hdenU : p.1 * p.2 ^ 2 ≤ (B.b : ℝ) * (B.d : ℝ) ^ 2 :=
    mul_le_mul hp.1.2 (pow_le_pow_left₀ hu.le hp.2.2 2) (by positivity) (ha.le.trans hab)
  have hw := Box.buchstab_enclosure hB n hp hT
  have hn := Box.numerators_nonneg B n
  have hnL : (0 : ℝ) ≤ (B.numeratorLower n : ℝ) := by exact_mod_cast hn.1
  have hnU : (0 : ℝ) ≤ (B.numeratorUpper n : ℝ) := by exact_mod_cast hn.2
  simp only [Box.lower, Box.upper, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    p5U7OmegaKernel, one_mul]
  exact ⟨(div_le_div_of_nonneg_left hnL hd hdenU).trans
      (div_le_div_of_nonneg_right hw.1 hd.le),
    (div_le_div_of_nonneg_right hw.2 hd.le).trans
      (div_le_div_of_nonneg_left hnU (by positivity) hdenL)⟩

theorem Box.lower_nonneg {B : Box} (hB : B.Valid) (n : ℕ) : 0 ≤ B.lower n := by
  obtain ⟨ha, hab, _, hc, hcd⟩ := hB
  exact div_nonneg (Box.numerators_nonneg B n).1
    (mul_nonneg (ha.le.trans hab) (sq_nonneg _))

theorem Box.upper_nonneg {B : Box} (hB : B.Valid) (n : ℕ) : 0 ≤ B.upper n := by
  exact div_nonneg (Box.numerators_nonneg B n).2
    (mul_nonneg hB.1.le (sq_nonneg _))

end

end ImbalancedChen.P5U7OriginalStraddlingCells
