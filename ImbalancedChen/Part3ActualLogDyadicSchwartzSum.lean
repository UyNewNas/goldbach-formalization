import ImbalancedChen.Part3ActualSeparatedRowLogModeSupplier
import ImbalancedChen.Part3ActualLogTagBetaRestriction
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCEONLY / UNCOMPILED. Genuine actual imports, no pending count-module
import. This proves the missing uniform dyadic coefficient summation, not
a bound for Mass6 or an ABL/Kuznetsov spectral theorem.
delta is freely positive and independent of kappa. r records only an
explicit normalized polynomial loss (1+T0*2^j)^r. Raw H^r carries a separate
T0^(-r) factor and is NOT silently treated as this normalized weight.
-/
namespace ImbalancedChen.Part3.ActualLogDyadicSchwartzSumSourceOnly
noncomputable section
open Classical
open scoped BigOperators

def dyadicSchwartzWeight (T r : ℝ) (b j : ℕ) : ℝ :=
  (1 + T * (2 : ℝ) ^ j) ^ r / (1 + T * (2 : ℝ) ^ j) ^ b

theorem dyadicSchwartzWeight_nonneg {T : ℝ} (hT : 0 < T) (r : ℝ) (b j : ℕ) :
    0 ≤ dyadicSchwartzWeight T r b j := by
  unfold dyadicSchwartzWeight
  positivity

/-- Arbitrarily small geometric decay, including the low-lambda blocks. -/
theorem dyadicSchwartzWeight_le_geometric {T r delta : ℝ} {b : ℕ}
    (hT : 0 < T) (hdelta : 0 < delta) (hb : r + delta ≤ (b : ℝ)) (j : ℕ) :
    dyadicSchwartzWeight T r b j ≤ T ^ (-delta) * ((2 : ℝ) ^ (-delta)) ^ j := by
  have hv : 0 < T * (2 : ℝ) ^ j := mul_pos hT (pow_pos (by norm_num) _)
  have hx : 0 < 1 + T * (2 : ℝ) ^ j := by linarith
  have hx1 : 1 ≤ 1 + T * (2 : ℝ) ^ j := by linarith
  unfold dyadicSchwartzWeight
  rw [← Real.rpow_sub_natCast hx.ne']
  calc
    _ ≤ (1 + T * (2 : ℝ) ^ j) ^ (-delta) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    _ ≤ (T * (2 : ℝ) ^ j) ^ (-delta) :=
      Real.rpow_le_rpow_of_nonpos hv (by linarith) (by linarith)
    _ = T ^ (-delta) * ((2 : ℝ) ^ (-delta)) ^ j := by
      rw [Real.mul_rpow hT.le (pow_nonneg (by norm_num) _),
        ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
        mul_comm (j : ℝ) (-delta),
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]

/-- No bound on the number of blocks, Z, or the global h cutoff is needed. -/
theorem dyadicSchwartzWeight_summable_and_bound {T r delta : ℝ} {b : ℕ}
    (hT : 0 < T) (hdelta : 0 < delta) (hb : r + delta ≤ (b : ℝ)) :
    Summable (dyadicSchwartzWeight T r b) ∧
      (∑' j : ℕ, dyadicSchwartzWeight T r b j) ≤
        T ^ (-delta) / (1 - (2 : ℝ) ^ (-delta)) := by
  have hq0 : 0 ≤ (2 : ℝ) ^ (-delta) := Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-delta) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hmajor : HasSum (fun j : ℕ => T ^ (-delta) * ((2 : ℝ) ^ (-delta)) ^ j)
      (T ^ (-delta) / (1 - (2 : ℝ) ^ (-delta))) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (T ^ (-delta))
  have hp := dyadicSchwartzWeight_le_geometric hT hdelta hb
  have hs := hmajor.summable.of_nonneg_of_le
    (dyadicSchwartzWeight_nonneg hT r b) hp
  exact ⟨hs, hasSum_le hp hs.hasSum hmajor⟩

/-- A transparent geometric consumer, not a polynomial bound on H.
An actual bound for 1/T supplies hInv; the geometric theorem itself is above. -/
theorem dyadicSchwartzWeight_bound_of_inverse_scale {T r delta x : ℝ} {b p : ℕ}
    (hT : 0 < T) (hdelta : 0 < delta) (hb : r + delta ≤ (b : ℝ))
    (hx : 0 ≤ x) (hInv : 1 / T ≤ x ^ p) :
    (∑' j : ℕ, dyadicSchwartzWeight T r b j) ≤
      x ^ ((p : ℝ) * delta) / (1 - (2 : ℝ) ^ (-delta)) := by
  have hq1 : (2 : ℝ) ^ (-delta) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : T ^ (-delta) ≤ x ^ ((p : ℝ) * delta) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    have hi : T⁻¹ ≤ x ^ p := by simpa only [one_div] using hInv
    calc
      _ ≤ (x ^ p) ^ delta := Real.rpow_le_rpow (inv_nonneg.mpr hT.le) hi hdelta.le
      _ = _ := (Real.rpow_natCast_mul hx p delta).symm
  exact (dyadicSchwartzWeight_summable_and_bound hT hdelta hb).2.trans
    (div_le_div_of_nonneg_right hpow (sub_nonneg.mpr hq1.le))

open _root_.P3ActualLogAdapterSourceOnly _root_.P3ActualJointGSourceOnly

/-- The actual two-log Fourier coefficients, not a freely chosen majorant. -/
def actualWeightedBlockMass (e : MediumAtom) (D : ℕ) (Z : ℝ)
    (sign : Bool) (r : ℝ) (j : ℕ) : ℝ :=
  (∑' m : ℤ × ℤ, ‖coeff e D Z (j, sign) m‖) * (1 + lambda e D j) ^ r

private theorem actual_base_pos {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) {D : ℕ} (hD : 0 < D) :
    0 < base e D := by
  have hV : 0 < e.V := zero_lt_one.trans_le he.2.1
  have hQ : 0 < e.Q1 := zero_lt_one.trans_le he.2.2.1
  have hS : 0 < e.Q2 := zero_lt_one.trans_le he.2.2.2.1
  have hR : 0 < e.Q3 := zero_lt_one.trans_le he.2.2.2.2.1
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  dsimp [base]
  positivity

/-- Uniform for every positive Z and both h signs. The same single 5*kappa
coefficient fee is retained; kappa=0 is explicitly allowed. No spectral
estimate, derivative bound or coefficient summability is an input. -/
theorem actual_weighted_block_mass_summable_and_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hkappa : 0 ≤ kappa)
    {D : ℕ} (hD : 0 < D) (Z : ℝ) (hZ : 0 < Z) (sign : Bool)
    (r delta : ℝ) (hdelta : 0 < delta) (b : ℕ) (hb : r + delta ≤ (b : ℝ)) :
    Summable (actualWeightedBlockMass e D Z sign r) ∧
      (∑' j : ℕ, actualWeightedBlockMass e D Z sign r j) ≤
        (16 * fourierCost b * e.scale ^ (5 * kappa)) *
          ((base e D) ^ (-delta) / (1 - (2 : ℝ) ^ (-delta))) := by
  have hT := actual_base_pos he hD
  let C : ℝ := 16 * fourierCost b * e.scale ^ (5 * kappa)
  have hx : 0 ≤ e.scale := by
    change 0 ≤ e.U * e.V
    exact mul_nonneg (zero_le_one.trans he.1) (zero_le_one.trans he.2.1)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (by norm_num) (fourierCost_nonneg b)) (Real.rpow_nonneg hx _)
  have hd := dyadicSchwartzWeight_summable_and_bound (r := r) hT hdelta hb
  have hmajor := hd.1.mul_left C
  have hp (j : ℕ) : actualWeightedBlockMass e D Z sign r j ≤
      C * dyadicSchwartzWeight (base e D) r b j := by
    have hc := (coeff_l1_original_five he hkappa b D Z hZ (j, sign)).2
    have hlam : 0 ≤ lambda e D j := mul_nonneg hT.le (Hreal_pos j).le
    calc
      _ ≤ (C / (1 + lambda e D j) ^ b) * (1 + lambda e D j) ^ r :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)
      _ = C * dyadicSchwartzWeight (base e D) r b j := by
        simp only [dyadicSchwartzWeight, lambda, Hreal, Hnat, Nat.cast_pow, Nat.cast_ofNat]
        ring
  have hnonneg (j : ℕ) : 0 ≤ actualWeightedBlockMass e D Z sign r j := by
    have hlam : 0 ≤ lambda e D j := mul_nonneg hT.le (Hreal_pos j).le
    exact mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  have hs := hmajor.of_nonneg_of_le hnonneg hp
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, C * dyadicSchwartzWeight (base e D) r b j :=
      hasSum_le hp hs.hasSum hmajor.hasSum
    _ = C * ∑' j : ℕ, dyadicSchwartzWeight (base e D) r b j := hd.1.tsum_mul_left C
    _ ≤ _ := mul_le_mul_of_nonneg_left hd.2 hC

/-- Applies to every finite actual tag subfamily of one sign; no cardinal fee. -/
theorem actual_finite_weighted_block_mass_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e) (hkappa : 0 ≤ kappa)
    {D : ℕ} (hD : 0 < D) (Z : ℝ) (hZ : 0 < Z) (sign : Bool)
    (r delta : ℝ) (hdelta : 0 < delta) (b : ℕ) (hb : r + delta ≤ (b : ℝ))
    (J : Finset ℕ) :
    (∑ j ∈ J, actualWeightedBlockMass e D Z sign r j) ≤
      (16 * fourierCost b * e.scale ^ (5 * kappa)) *
        ((base e D) ^ (-delta) / (1 - (2 : ℝ) ^ (-delta))) := by
  obtain ⟨hs, hbnd⟩ := actual_weighted_block_mass_summable_and_bound
    he hkappa hD Z hZ sign r delta hdelta b hb
  have hT := actual_base_pos he hD
  have hn (j : ℕ) : 0 ≤ actualWeightedBlockMass e D Z sign r j := by
    have hlam : 0 ≤ lambda e D j := mul_nonneg hT.le (Hreal_pos j).le
    exact mul_nonneg (tsum_nonneg (fun _ => norm_nonneg _))
      (Real.rpow_nonneg (by linarith) _)
  exact (hs.sum_le_tsum J (fun j _ => hn j)).trans hbnd

end
end ImbalancedChen.Part3.ActualLogDyadicSchwartzSumSourceOnly
