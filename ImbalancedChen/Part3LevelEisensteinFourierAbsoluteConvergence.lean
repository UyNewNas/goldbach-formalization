import ImbalancedChen.Part3ActualLevelComplexEisensteinFourier
import ImbalancedChen.Part3ActualRamanujanBesselNormalConvergence

/-!
Absolute summability of the true all-level complex Eisenstein Fourier
coefficients. The literal level-restricted Ramanujan series is bounded,
uniformly in frequency and level, by a proved convergent p-series using
the actual gcd bound. The true K strip decay absorbs the remaining natural
frequency power. No hNormalConv or coefficient summability is an input.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.LevelEisensteinFourierAbsoluteConvergence

noncomputable section

open Set Filter
open scoped Topology BigOperators
open ActualLevelComplexEisensteinFourier ActualRamanujanSinglePrimeLevelSplit
open RamanujanMultiplicativeGcdBound20261025a
open Part3ActualRamanujanBesselNormalConvergence
open ComplexOrderKBridgeSourceOnly ComplexOrderKUniformStripDecay20261025a
open OriginalSmoothPoissonTail.Physical.ZeroMode

/-- Frequency-independent absolute arithmetic bound, before Fourier/K factors. -/
def arithmeticBound (s : ℂ) : ℝ := ∑' c : ℕ, (c : ℝ) ^ (1 - 2 * s.re)

theorem arithmeticWeight_summable (s : ℂ) (hs : 1 < s.re) :
    Summable (fun c : ℕ => (c : ℝ) ^ (1 - 2 * s.re)) :=
  summable_nat_rpow.mpr (by linarith)

theorem arithmeticBound_nonneg (s : ℂ) : 0 ≤ arithmeticBound s :=
  tsum_nonneg (fun c => Real.rpow_nonneg (Nat.cast_nonneg c) _)

private theorem actualTerm_two_mul_norm_bound (s : ℂ) (n : ℤ) (c : ℕ) :
    ‖actualTerm n (2 * s) c‖ ≤ (c : ℝ) ^ (1 - 2 * s.re) := by
  by_cases hc : c = 0
  · subst c
    rw [actualTerm_zero, norm_zero]
    exact Real.rpow_nonneg (le_rfl : (0 : ℝ) ≤ 0) _
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc
    have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
    have hg : ‖ramanujan c n‖ ≤ (c : ℝ) :=
      (norm_ramanujan_le_gcd c n).trans (by exact_mod_cast Nat.gcd_le_left n.natAbs hcpos)
    rw [actualTerm, norm_mul, Complex.norm_natCast_cpow_of_pos hcpos]
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofNat_re,
      Complex.ofNat_im, zero_mul, sub_zero]
    calc
      _ ≤ (c : ℝ) * (c : ℝ) ^ (-(2 * s.re)) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hcR.le _)
      _ = _ := by
        rw [show 1 - 2 * s.re = 1 + (-(2 * s.re)) by ring,
          Real.rpow_add hcR, Real.rpow_one]

/-- The actual level c-series is uniformly bounded in its signed frequency.
The proof retains N|c in the summand and only enlarges its majorant. -/
theorem restrictedSeries_norm_le_arithmeticBound (N : ℕ) (s : ℂ) (hs : 1 < s.re) (n : ℤ) :
    ‖restrictedSeries N n (2 * s)‖ ≤ arithmeticBound s := by
  have htwo : (2 : ℝ) < (2 * s).re := by
    simp only [Complex.mul_re, Complex.ofNat_re, Complex.ofNat_im, zero_mul, sub_zero]
    linarith
  have hconv : (if n = 0 then (2 : ℝ) else 1) < (2 * s).re := by split_ifs <;> linarith
  have hc := restrictedSeries_norm_summable N n (2 * s) hconv
  have hpoint (c : ℕ) : ‖if N ∣ c then actualTerm n (2 * s) c else 0‖ ≤
      (c : ℝ) ^ (1 - 2 * s.re) := by
    split_ifs
    · exact actualTerm_two_mul_norm_bound s n c
    · rw [norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg c) _
  exact (norm_tsum_le_tsum_norm hc).trans
    (hc.tsum_le_tsum hpoint (arithmeticWeight_summable s hs))

/-- A scalar constant chosen before the nonzero frequency. -/
def coefficientConstant (s : ℂ) (y : ℝ) (M : ℕ) : ℝ :=
  arithmeticBound s * ‖(2 * (Real.pi : ℂ) ^ s / Complex.Gamma s)‖ *
    ‖(Real.sqrt y : ℂ)‖ * decayConstant M y

def coefficientMajorant (s : ℂ) (y : ℝ) (M : ℕ) (d : ℕ) : ℝ :=
  coefficientConstant s y M * (d : ℝ) ^ M * Real.exp (-(Real.pi * y) * (d : ℝ))

theorem coefficientMajorant_summable (s : ℂ) {y : ℝ} (hy : 0 < y) (M : ℕ) :
    Summable (coefficientMajorant s y M) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul M (mul_pos Real.pi_pos hy)
  simpa only [coefficientMajorant, mul_assoc] using h.const_mul (coefficientConstant s y M)

private theorem natAbs_cast (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]

/-- Actual nonzero canonical coefficients have a summable exponential
majorant. Every level N, including its true divisibility restriction, is covered. -/
theorem levelCanonicalCoefficient_nonzero_norm_bound (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    {y : ℝ} (hy : 0 < y) (M : ℕ) (hsM : |s.re| ≤ (M : ℝ))
    (n : ℤ) (hn : n ≠ 0) :
    ‖levelCanonicalCoefficient N s y n‖ ≤ coefficientMajorant s y M n.natAbs := by
  let d : ℕ := n.natAbs
  have hd : 0 < d := Int.natAbs_pos.mpr hn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdcast : |(n : ℝ)| = (d : ℝ) := (natAbs_cast n).symm
  have hq0 : 0 < 2 * Real.pi * y := by positivity
  have hq : 2 * Real.pi * y ≤ 2 * Real.pi * (d : ℝ) * y := by
    have h := mul_le_mul_of_nonneg_right hd1 (by positivity : 0 ≤ 2 * Real.pi * y)
    nlinarith
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := complexOrderK_uniform_exp_bound hq0 hq hnu
  have hK' : ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (d : ℝ) * y)‖ ≤
      decayConstant M y * Real.exp (-(Real.pi * y) * (d : ℝ)) := by
    simpa only [decayConstant,
      show -(2 * Real.pi * (d : ℝ) * y / 2) = -(Real.pi * y) * (d : ℝ) by ring] using hK
  have hp := power_prefactor_bound hd M hsM
  have harith := restrictedSeries_norm_le_arithmeticBound N s hs n
  have hdecay : 0 ≤ decayConstant M y := (stripDecayConstant_pos _ _ _).le
  have hA := arithmeticBound_nonneg s
  unfold levelCanonicalCoefficient seedFourierKernel
  rw [if_neg hn, zero_add, if_neg hn, hdcast]
  simp only [norm_mul]
  have h := mul_le_mul_of_nonneg_right harith
    (by positivity : 0 ≤ ‖2 * (Real.pi : ℂ) ^ s / Complex.Gamma s‖ *
      ‖((d : ℕ) : ℂ) ^ (s - 1 / 2)‖ * ‖(Real.sqrt y : ℂ)‖ *
        ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (d : ℝ) * y)‖)
  have hpow := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg hA (norm_nonneg _)) (norm_nonneg (Real.sqrt y : ℂ)))
  have hfull := mul_le_mul hpow hK' (norm_nonneg _)
    (by positivity : 0 ≤ arithmeticBound s * ‖2 * (Real.pi : ℂ) ^ s / Complex.Gamma s‖ *
      ‖(Real.sqrt y : ℂ)‖ * (d : ℝ) ^ M)
  have hmid : ‖restrictedSeries N n (2 * s)‖ *
      ‖2 * (Real.pi : ℂ) ^ s / Complex.Gamma s‖ * ‖(d : ℂ) ^ (s - 1 / 2)‖ *
      ‖(Real.sqrt y : ℂ)‖ * ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (d : ℝ) * y)‖ ≤
      arithmeticBound s * ‖2 * (Real.pi : ℂ) ^ s / Complex.Gamma s‖ *
        ‖(d : ℂ) ^ (s - 1 / 2)‖ * ‖(Real.sqrt y : ℂ)‖ *
          ‖complexOrderK (s - 1 / 2) (2 * Real.pi * (d : ℝ) * y)‖ := by
    convert h using 1 <;> ring
  have hfinal := hmid.trans (by convert hfull using 1 <;> ring)
  simpa only [coefficientMajorant, coefficientConstant, d,
    Complex.ofReal_natCast, mul_assoc] using hfinal

/-- True all-level absolute coefficient summability on the integer Fourier lattice. -/
theorem levelCanonicalCoefficient_norm_summable (N : ℕ) (s : ℂ) (hs : 1 < s.re)
    {y : ℝ} (hy : 0 < y) : Summable (fun n : ℤ => ‖levelCanonicalCoefficient N s y n‖) := by
  let M : ℕ := Nat.ceil |s.re|
  have hsM : |s.re| ≤ (M : ℝ) := Nat.le_ceil _
  have hmajor := coefficientMajorant_summable s hy M
  have hshift : Summable (fun k : ℕ => coefficientMajorant s y M (k + 1)) :=
    (summable_nat_add_iff 1).mpr hmajor
  have hp : Summable (fun k : ℕ => ‖levelCanonicalCoefficient N s y ((k + 1 : ℕ) : ℤ)‖) := by
    apply hshift.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    simpa only [Int.natAbs_natCast] using levelCanonicalCoefficient_nonzero_norm_bound N s hs hy M hsM
      (((k + 1 : ℕ) : ℤ)) (by exact_mod_cast (Nat.succ_ne_zero k))
  have hn : Summable (fun k : ℕ => ‖levelCanonicalCoefficient N s y (-((k + 1 : ℕ) : ℤ))‖) := by
    apply hshift.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro k
    simpa only [Int.natAbs_neg, Int.natAbs_natCast] using levelCanonicalCoefficient_nonzero_norm_bound N s hs hy M hsM
      (-((k + 1 : ℕ) : ℤ)) (neg_ne_zero.mpr (by exact_mod_cast (Nat.succ_ne_zero k)))
  have hp0 : Summable (fun k : ℕ => ‖levelCanonicalCoefficient N s y (k : ℤ)‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  exact Summable.of_nat_of_neg_add_one hp0
    (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

end
end ImbalancedChen.Part3.LevelEisensteinFourierAbsoluteConvergence

