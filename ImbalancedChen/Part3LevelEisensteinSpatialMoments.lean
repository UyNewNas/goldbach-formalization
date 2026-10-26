import ImbalancedChen.Part3ActualLevelEisensteinPointwiseFourier
import ImbalancedChen.Part3ContinuedFourierSpatialMoments

/-!
Actual spatial derivative moments for the genuine level-N Fourier family.
The arithmetic coefficient is the literal restricted Ramanujan c-series at
its signed frequency; no level-one divisor coefficient is relabelled. Its
proved frequency-independent bound A(s) gives summable majorants for every
preselected finite pair of spatial derivative orders. The only shared K
facts are the actual qMoment calculus and generic uniform moment decay.
SOURCE_WRITTEN_UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.LevelEisensteinSpatialMoments

noncomputable section

open Set Filter
open scoped Topology BigOperators
open ActualLevelComplexEisensteinFourier ActualRamanujanSinglePrimeLevelSplit
open ActualLevelEisensteinPointwiseFourier LevelEisensteinFourierAbsoluteConvergence
open Part3ActualRamanujanBesselNormalConvergence
open ContinuedFourierSpatialMoments ComplexOrderKQCalculus

/-- Each branch retains its actual positive or negative arithmetic frequency. -/
def signedIndex (negative : Bool) (n : ℕ) : ℤ :=
  if negative then -((n + 1 : ℕ) : ℤ) else ((n + 1 : ℕ) : ℤ)

def levelSpectralCoefficient (N : ℕ) (negative : Bool) (n : ℕ) (s : ℂ) : ℂ :=
  restrictedSeries N (signedIndex negative n) (2 * s) * ((n + 1 : ℕ) : ℂ) ^ (s - 1 / 2)

/-- Unreflected branch moments. The negative Fourier branch is evaluated at
-x and multiplied by (-1)^j when the branches are combined. -/
def levelMomentTerm (N : ℕ) (negative : Bool) (j k n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  levelSpectralCoefficient N negative n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
    (frequency (n + 1) : ℂ) ^ k *
      qMoment k (s - 1 / 2) (frequency (n + 1) * y) * phase (n + 1) x

theorem levelMomentTerm_hasDerivAt_x (N : ℕ) (negative : Bool) (j k n : ℕ)
    (s : ℂ) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => levelMomentTerm N negative j k n s y t)
      (levelMomentTerm N negative (j + 1) k n s y x) x := by
  have h := (phase_hasDerivAt (n + 1) x).const_mul
    (levelSpectralCoefficient N negative n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
      (frequency (n + 1) : ℂ) ^ k * qMoment k (s - 1 / 2) (frequency (n + 1) * y))
  convert h using 1 <;> simp [levelMomentTerm, pow_succ] <;> ring

theorem levelMomentTerm_hasDerivAt_y (N : ℕ) (negative : Bool) (j k n : ℕ)
    (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => levelMomentTerm N negative j k n s t x)
      (levelMomentTerm N negative j (k + 1) n s y x) y := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have h := (qMoment_hasDerivAt k (s - 1 / 2) (mul_pos hw hy)).comp y
    ((hasDerivAt_id y).const_mul (frequency (n + 1)))
  have hc := (h.const_mul
    (levelSpectralCoefficient N negative n s * (Complex.I * (frequency (n + 1) : ℂ)) ^ j *
      (frequency (n + 1) : ℂ) ^ k)).mul_const (phase (n + 1) x)
  convert hc using 1 <;>
    simp [levelMomentTerm, pow_succ, smul_eq_mul, Complex.ofReal_mul] <;> ring

theorem levelSpectralCoefficient_norm_bound (N : ℕ) (negative : Bool) (n M : ℕ)
    (s : ℂ) (hs : 1 < s.re) (hsM : |s.re| ≤ (M : ℝ)) :
    ‖levelSpectralCoefficient N negative n s‖ ≤ arithmeticBound s * ((n + 1 : ℕ) : ℝ) ^ M := by
  rw [levelSpectralCoefficient, norm_mul]
  exact mul_le_mul (restrictedSeries_norm_le_arithmeticBound N s hs _)
    (power_prefactor_bound (by omega) M hsM) (norm_nonneg _) (arithmeticBound_nonneg s)

def levelMomentMajorant (j k M : ℕ) (s : ℂ) (a : ℝ) (n : ℕ) : ℝ :=
  (arithmeticBound s * qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
    (2 * Real.pi) ^ (j + k)) * ((n + 1 : ℕ) : ℝ) ^ (M + j + k) *
      Real.exp (-(Real.pi * a) * ((n + 1 : ℕ) : ℝ))

/-- Every finite spatial moment has its own proved summable majorant,
selected before the frequency, horizontal point and positive height. -/
theorem levelMomentTerm_norm_bound (N : ℕ) (negative : Bool) (j k M : ℕ)
    (s : ℂ) (hs : 1 < s.re) (hsM : |s.re| ≤ (M : ℝ))
    {a : ℝ} (ha : 0 < a) (n : ℕ) {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖levelMomentTerm N negative j k n s y x‖ ≤ levelMomentMajorant j k M s a n := by
  let d : ℕ := n + 1
  have hd : 0 < d := by dsimp [d]; omega
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hypos : 0 < y := ha.trans_le hy
  have hw : 0 < frequency d := by unfold frequency; positivity
  have hq0 : 0 < 2 * Real.pi * a := by positivity
  have hq : 2 * Real.pi * a ≤ frequency d * y := by
    have hdy : a ≤ (d : ℝ) * y := hy.trans (le_mul_of_one_le_left hypos.le hd1)
    dsimp [frequency]
    nlinarith [mul_le_mul_of_nonneg_left hdy (by positivity : 0 ≤ 2 * Real.pi)]
  have hnu : |(s - 1 / 2).re| ≤ (M : ℝ) + 1 := by
    have h := abs_sub_le s.re (1 / 2 : ℝ)
    norm_num at h
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
      Complex.one_im, Complex.ofNat_re, Complex.ofNat_im]
    norm_num
    linarith
  have hK := qMoment_uniform_exp_bound k hq0 hq hnu
  have he : Real.exp (-(frequency d * y / 2)) ≤ Real.exp (-(Real.pi * a) * (d : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ Real.pi * (d : ℝ))
    dsimp [frequency]
    nlinarith
  have hK' := hK.trans (mul_le_mul_of_nonneg_left he (qMomentDecayConstant_nonneg _ _ _))
  have hc := levelSpectralCoefficient_norm_bound N negative n M s hs hsM
  have hA := arithmeticBound_nonneg s
  have hC := qMomentDecayConstant_nonneg k (2 * Real.pi * a) ((M : ℝ) + 1)
  calc
    _ = ‖levelSpectralCoefficient N negative n s‖ * frequency d ^ j * frequency d ^ k *
        ‖qMoment k (s - 1 / 2) (frequency d * y)‖ := by
      simp only [levelMomentTerm, d, norm_mul, norm_pow, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw, one_mul, norm_phase, mul_one]
    _ ≤ (arithmeticBound s * (d : ℝ) ^ M) * frequency d ^ j * frequency d ^ k *
        (qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
          Real.exp (-(Real.pi * a) * (d : ℝ))) := by gcongr
    _ = levelMomentMajorant j k M s a n := by
      dsimp [levelMomentMajorant, frequency, d]
      simp only [mul_pow, pow_add]
      ring

theorem levelMomentMajorant_summable (j k M : ℕ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    Summable (levelMomentMajorant j k M s a) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul (M + j + k) (mul_pos Real.pi_pos ha)
  have hshift := (summable_nat_add_iff 1).mpr h
  simpa only [levelMomentMajorant, mul_assoc] using hshift.const_mul
    (arithmeticBound s * qMomentDecayConstant k (2 * Real.pi * a) ((M : ℝ) + 1) *
      (2 * Real.pi) ^ (j + k))

/-- Actual arbitrary finite derivative-series convergence on every positive
height region; no spatial normal-convergence field is assumed. -/
theorem levelMoment_uniform_convergence (N : ℕ) (negative : Bool) (j k : ℕ)
    (s : ℂ) (hs : 1 < s.re) {a : ℝ} (ha : 0 < a) :
    TendstoUniformlyOn
      (fun H : ℕ => fun p : ℝ × ℝ => ∑ n ∈ Finset.range H, levelMomentTerm N negative j k n s p.2 p.1)
      (fun p : ℝ × ℝ => ∑' n, levelMomentTerm N negative j k n s p.2 p.1)
      atTop {p | a ≤ p.2} := by
  let M : ℕ := Nat.ceil |s.re|
  exact tendstoUniformlyOn_tsum_nat (levelMomentMajorant_summable j k M s ha)
    (fun n p hp => levelMomentTerm_norm_bound N negative j k M s hs (Nat.le_ceil _) ha n hp p.1)

theorem levelMoment_norm_summable (N : ℕ) (negative : Bool) (j k : ℕ)
    (s : ℂ) (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖levelMomentTerm N negative j k n s y x‖) := by
  let M : ℕ := Nat.ceil |s.re|
  exact (levelMomentMajorant_summable j k M s hy).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => levelMomentTerm_norm_bound N negative j k M s hs (Nat.le_ceil _) hy n le_rfl x)

end
end ImbalancedChen.Part3.LevelEisensteinSpatialMoments

