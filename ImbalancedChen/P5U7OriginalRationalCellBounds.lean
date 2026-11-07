import ImbalancedChen.P5U7OriginalOmegaIntegral
import ImbalancedChen.P2ContinuousSieveRational

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Directed finite rational enclosures of the genuine original U7 Buchstab
kernel on rational boxes. The two formulas both include their s=2 seam.
Second-strip logarithms use the proved rational Taylor/remainder bounds.
No quadrature is evaluated and no saved original integral endpoint is
claimed. Box admission consists only of rational geometric inequalities.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab P2ContinuousSieveRational
open scoped BigOperators

theorem p5U7_logLower_nonneg (n : ℕ) (q : ℚ) (hq : 2 ≤ q) :
    0 ≤ logLower n q := by
  unfold logLower
  have hq0 : 0 < q := by linarith
  have hz : 0 ≤ (q - 2) / q := div_nonneg (by linarith) hq0.le
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun k _ => div_nonneg (pow_nonneg hz _)
    (by positivity))

/-- Literal first Buchstab piece, including both s=1 and s=2. -/
theorem p5U7_buchstab_first_rational_interval
    (L U : ℚ) (hL : 1 ≤ L) (hU : U ≤ 2)
    {s : ℝ} (hsL : (L : ℝ) ≤ s) (hsU : s ≤ (U : ℝ)) :
    ((1 / U : ℚ) : ℝ) ≤ buchstab s ∧
      buchstab s ≤ ((1 / L : ℚ) : ℝ) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hUr : (U : ℝ) ≤ 2 := by exact_mod_cast hU
  have hs1 : 1 ≤ s := hLr.trans hsL
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  rw [buchstab_eq_one_div hs1 (hsU.trans hUr)]
  constructor
  · simpa only [Rat.cast_div, Rat.cast_one] using
      one_div_le_one_div_of_le hs0 hsU
  · simpa only [Rat.cast_div, Rat.cast_one] using
      one_div_le_one_div_of_le (zero_lt_one.trans_le hLr) hsL

/-- Literal second Buchstab piece. The original maximum 132/59 remains
in the theorem, and s=2 is admitted on this side as well. -/
theorem p5U7_buchstab_second_rational_interval
    (n : ℕ) (L U : ℚ) (hL : 2 ≤ L) (hU : U ≤ 132 / 59)
    {s : ℝ} (hsL : (L : ℝ) ≤ s) (hsU : s ≤ (U : ℝ)) :
    (((1 + logLower n L) / U : ℚ) : ℝ) ≤ buchstab s ∧
      buchstab s ≤ (((1 + logUpper n U) / L : ℚ) : ℝ) := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hUr : (U : ℝ) ≤ 132 / 59 := by exact_mod_cast hU
  have hLU : L ≤ U := by exact_mod_cast (hsL.trans hsU)
  have hU2 : 2 ≤ U := hL.trans hLU
  have hs2 : 2 ≤ s := hLr.trans hsL
  have hs0 : 0 < s := by linarith
  have hLo := (log_bounds n L hL).1
  have hUp := (log_bounds n U hU2).2
  have hlogLo : (logLower n L : ℝ) ≤ Real.log (s - 1) :=
    hLo.trans (Real.log_le_log (by linarith) (by linarith only [hsL]))
  have hlogUp : Real.log (s - 1) ≤ (logUpper n U : ℝ) :=
    (Real.log_le_log (by linarith) (by linarith only [hsU])).trans hUp
  have hnLo : 0 ≤ (1 : ℝ) + (logLower n L : ℝ) := by
    have h := p5U7_logLower_nonneg n L hL
    have hcast : (0 : ℝ) ≤ (logLower n L : ℝ) := by exact_mod_cast h
    linarith
  have hn : 0 ≤ 1 + Real.log (s - 1) := by
    have hlog := Real.log_nonneg (show 1 ≤ s - 1 by linarith)
    linarith
  have hnUp : 0 ≤ (1 : ℝ) + (logUpper n U : ℝ) := by linarith
  rw [buchstab_eq_log_div hs2 (by linarith only [hsU, hUr] : s ≤ 3)]
  push_cast
  constructor
  · calc
      ((1 : ℝ) + (logLower n L : ℝ)) / (U : ℝ) ≤
          ((1 : ℝ) + (logLower n L : ℝ)) / s :=
        div_le_div_of_nonneg_left hnLo hs0 hsU
      _ ≤ (1 + Real.log (s - 1)) / s :=
        div_le_div_of_nonneg_right (by linarith only [hlogLo]) hs0.le
  · calc
      (1 + Real.log (s - 1)) / s ≤
          ((1 : ℝ) + (logUpper n U : ℝ)) / s :=
        div_le_div_of_nonneg_right (by linarith only [hlogUp]) hs0.le
      _ ≤ ((1 : ℝ) + (logUpper n U : ℝ)) / (L : ℝ) :=
        div_le_div_of_nonneg_left hnUp (by linarith) hsL

/-- Rational affine checks suffice to admit a whole box to a specified
Buchstab argument interval. No kernel inequality is an admission premise. -/
theorem p5U7_argument_rational_box
    (a b c d L U : ℚ) (hc : 0 < c) (hL : 1 ≤ L) (hLU : L ≤ U)
    (hleft : b + (1 + L) * d ≤ 1) (hright : 1 ≤ a + (1 + U) * c)
    {t u : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (hu : (c : ℝ) ≤ u ∧ u ≤ (d : ℝ)) :
    (L : ℝ) ≤ p5U7OmegaArgument t u ∧
      p5U7OmegaArgument t u ≤ (U : ℝ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hu0 : 0 < u := hcR.trans_le hu.1
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hUr : (1 : ℝ) ≤ U := by exact_mod_cast hL.trans hLU
  have hleftR : (b : ℝ) + (1 + (L : ℝ)) * (d : ℝ) ≤ 1 := by
    exact_mod_cast hleft
  have hrightR : (1 : ℝ) ≤ (a : ℝ) + (1 + (U : ℝ)) * (c : ℝ) := by
    exact_mod_cast hright
  have hmL := mul_le_mul_of_nonneg_left hu.2 (by linarith : 0 ≤ 1 + (L : ℝ))
  have hmU := mul_le_mul_of_nonneg_left hu.1 (by linarith : 0 ≤ 1 + (U : ℝ))
  unfold p5U7OmegaArgument
  constructor
  · apply (le_div_iff₀ hu0).mpr
    nlinarith only [ht.2, hleftR, hmL]
  · apply (div_le_iff₀ hu0).mpr
    nlinarith only [ht.1, hrightR, hmU]

private theorem p5U7_kernel_box_bounds
    (a b c d : ℚ) (ha : 0 < a) (hc : 0 < c)
    {t u lo hi : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (hu : (c : ℝ) ≤ u ∧ u ≤ (d : ℝ))
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (hbuch : lo ≤ buchstab (p5U7OmegaArgument t u) ∧
      buchstab (p5U7OmegaArgument t u) ≤ hi) :
    lo / ((b : ℝ) * (d : ℝ) ^ 2) ≤ p5U7OmegaKernel 1 t u ∧
      p5U7OmegaKernel 1 t u ≤ hi / ((a : ℝ) * (c : ℝ) ^ 2) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have ht0 : 0 < t := haR.trans_le ht.1
  have hu0 : 0 < u := hcR.trans_le hu.1
  have hb0 : (0 : ℝ) < b := ht0.trans_le ht.2
  have hd0 : (0 : ℝ) < d := hu0.trans_le hu.2
  have hden0 : 0 < t * u ^ 2 := by positivity
  have hdenL : (a : ℝ) * (c : ℝ) ^ 2 ≤ t * u ^ 2 :=
    mul_le_mul ht.1 (pow_le_pow_left₀ hcR.le hu.1 2) (by positivity) ht0.le
  have hdenU : t * u ^ 2 ≤ (b : ℝ) * (d : ℝ) ^ 2 :=
    mul_le_mul ht.2 (pow_le_pow_left₀ hu0.le hu.2 2) (by positivity) hb0.le
  simp only [p5U7OmegaKernel, one_mul]
  constructor
  · exact (div_le_div_of_nonneg_left hlo hden0 hdenU).trans
      (div_le_div_of_nonneg_right hbuch.1 hden0.le)
  · exact (div_le_div_of_nonneg_right hbuch.2 hden0.le).trans
      (div_le_div_of_nonneg_left hhi (by positivity) hdenL)

def p5U7FirstCellLower (b d U : ℚ) : ℚ := (1 / U) / (b * d ^ 2)
def p5U7FirstCellUpper (a c L : ℚ) : ℚ := (1 / L) / (a * c ^ 2)
def p5U7SecondCellLower (n : ℕ) (b d L U : ℚ) : ℚ :=
  ((1 + logLower n L) / U) / (b * d ^ 2)
def p5U7SecondCellUpper (n : ℕ) (a c L U : ℚ) : ℚ :=
  ((1 + logUpper n U) / L) / (a * c ^ 2)

/-- Directed bounds on an admitted first-piece box. The output endpoints
are finite rational expressions, without a logarithmic evaluation. -/
theorem p5U7_original_first_rational_cell_bounds
    (a b c d L U : ℚ) (ha : 0 < a) (hc : 0 < c)
    (hL : 1 ≤ L) (hLU : L ≤ U) (hU : U ≤ 2)
    (hleft : b + (1 + L) * d ≤ 1) (hright : 1 ≤ a + (1 + U) * c)
    {t u : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (hu : (c : ℝ) ≤ u ∧ u ≤ (d : ℝ)) :
    (p5U7FirstCellLower b d U : ℝ) ≤ p5U7OmegaKernel 1 t u ∧
      p5U7OmegaKernel 1 t u ≤ (p5U7FirstCellUpper a c L : ℝ) := by
  have hs := p5U7_argument_rational_box a b c d L U hc hL hLU hleft hright ht hu
  have hw := p5U7_buchstab_first_rational_interval L U hL hU hs.1 hs.2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by linarith)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by linarith)
  have h := p5U7_kernel_box_bounds a b c d ha hc ht hu
    (show 0 ≤ ((1 / U : ℚ) : ℝ) by push_cast; positivity)
    (show 0 ≤ ((1 / L : ℚ) : ℝ) by push_cast; positivity) hw
  simpa only [p5U7FirstCellLower, p5U7FirstCellUpper, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_one] using h

/-- Directed second-piece bounds, with rational Taylor remainder and
the original 132/59 argument ceiling. The s=2 seam is retained. -/
theorem p5U7_original_second_rational_cell_bounds
    (n : ℕ) (a b c d L U : ℚ) (ha : 0 < a) (hc : 0 < c)
    (hL : 2 ≤ L) (hLU : L ≤ U) (hU : U ≤ 132 / 59)
    (hleft : b + (1 + L) * d ≤ 1) (hright : 1 ≤ a + (1 + U) * c)
    {t u : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ))
    (hu : (c : ℝ) ≤ u ∧ u ≤ (d : ℝ)) :
    (p5U7SecondCellLower n b d L U : ℝ) ≤ p5U7OmegaKernel 1 t u ∧
      p5U7OmegaKernel 1 t u ≤ (p5U7SecondCellUpper n a c L U : ℝ) := by
  have hs := p5U7_argument_rational_box a b c d L U hc
    (by linarith) hLU hleft hright ht hu
  have hw := p5U7_buchstab_second_rational_interval n L U hL hU hs.1 hs.2
  have hlo : 0 ≤ (((1 + logLower n L) / U : ℚ) : ℝ) := by
    exact_mod_cast (div_nonneg
      (show (0 : ℚ) ≤ 1 + logLower n L by linarith [p5U7_logLower_nonneg n L hL])
      (show (0 : ℚ) ≤ U by linarith))
  have hhi : 0 ≤ (((1 + logUpper n U) / L : ℚ) : ℝ) :=
    (hlo.trans hw.1).trans hw.2
  have h := p5U7_kernel_box_bounds a b c d ha hc ht hu hlo hhi hw
  simpa only [p5U7SecondCellLower, p5U7SecondCellUpper, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_one, Rat.cast_add] using h

end

end ImbalancedChen
