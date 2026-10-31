import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.NormCast

/-!
SOURCE ONLY / UNCOMPILED.

Literal `log_point` range reduction from frozen certify_conservative_chen.py,
SHA256 67b9429667e18786058e0fe58676fbe09d556868468f1281166cac2b55f8604e,
lines 121--136. Its argument q is an exact positive INTEGER; its target is
log(q/2^80). The source shift is q.bit_length()-1-80. Positive shifts use
outward integer floor/ceil, negative shifts use an exact left shift.

There is no rational numerator/denominator bit-length comparison or one-step
adjustment in this frozen function. None is invented here. The atanh32 loop
and its tail arithmetic belong to the separate log interpreter module.
-/

namespace ImbalancedChen.Certificates.P2HistoricLogRangeReduction

def Q : ℕ := 2 ^ 80
def binaryExponent (q : ℤ) : ℕ := q.toNat.size - 1
def sourceShift (q : ℤ) : ℤ := (binaryExponent q : ℤ) - 80

/-- Exact rational represented by the reduced fixed-point endpoints. -/
def exactReduced (q : ℤ) : ℚ := (q : ℚ) / (2 : ℚ) ^ binaryExponent q
def scaledExact (q : ℤ) : ℚ := (Q : ℚ) * exactReduced q

/-- Python's positive-shift floor division / exact negative-shift multiply. -/
def sourceRL (q : ℤ) : ℤ :=
  if 0 ≤ sourceShift q then q / (2 ^ (sourceShift q).toNat : ℕ)
  else q * (2 ^ (-sourceShift q).toNat : ℕ)

/-- Python ceildiv is -((-q)//d), with the same positive integer divisor. -/
def sourceRH (q : ℤ) : ℤ :=
  if 0 ≤ sourceShift q then -((-q) / (2 ^ (sourceShift q).toNat : ℕ))
  else q * (2 ^ (-sourceShift q).toNat : ℕ)

theorem Q_pos : (0 : ℚ) < Q := by norm_num [Q]

theorem binaryExponent_bounds {q : ℤ} (hq : 0 < q) :
    2 ^ binaryExponent q ≤ q.toNat ∧ q.toNat < 2 ^ (binaryExponent q + 1) := by
  have hn : 0 < q.toNat := by omega
  have hs : 0 < q.toNat.size := Nat.size_pos.mpr hn
  have he : binaryExponent q + 1 = q.toNat.size := by
    unfold binaryExponent
    omega
  constructor
  · apply Nat.lt_size.mp
    omega
  · rw [he]
    exact Nat.lt_size_self _

/-- `Nat.size` is the exact binary bit length; positivity removes the
truncated natural subtraction before the signed Python shift. -/
theorem sourceShift_bit_length {q : ℤ} (hq : 0 < q) :
    sourceShift q = (q.toNat.size : ℤ) - 1 - 80 := by
  have hs : 0 < q.toNat.size := Nat.size_pos.mpr (by omega)
  unfold sourceShift binaryExponent
  omega

theorem sourceShift_nonneg_iff (q : ℤ) :
    0 ≤ sourceShift q ↔ 80 ≤ binaryExponent q := by
  unfold sourceShift
  omega

theorem positive_shift_toNat {q : ℤ} (hk : 0 ≤ sourceShift q) :
    (sourceShift q).toNat = binaryExponent q - 80 := by
  unfold sourceShift at *
  omega

theorem negative_shift_toNat {q : ℤ} (hk : sourceShift q < 0) :
    (-sourceShift q).toNat = 80 - binaryExponent q := by
  unfold sourceShift at *
  omega

/-- The exact normalization is in [1,2), before any directed round. -/
theorem exactReduced_bounds {q : ℤ} (hq : 0 < q) :
    1 ≤ exactReduced q ∧ exactReduced q < 2 := by
  obtain ⟨hl, hu⟩ := binaryExponent_bounds hq
  have hcast : (q.toNat : ℚ) = (q : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hq.le
  have hlR : (2 : ℚ) ^ binaryExponent q ≤ (q : ℚ) := by
    rw [← hcast]
    exact_mod_cast hl
  have huR : (q : ℚ) < (2 : ℚ) ^ (binaryExponent q + 1) := by
    rw [← hcast]
    exact_mod_cast hu
  have hd : (0 : ℚ) < 2 ^ binaryExponent q := by positivity
  constructor
  · exact (le_div_iff₀ hd).mpr (by simpa using hlR)
  · apply (div_lt_iff₀ hd).mpr
    simpa only [pow_succ, mul_comm] using huR

theorem scaledExact_positive_shift {q : ℤ} (hk : 0 ≤ sourceShift q) :
    scaledExact q = (q : ℚ) / (2 ^ (sourceShift q).toNat : ℕ) := by
  have he : 80 ≤ binaryExponent q := (sourceShift_nonneg_iff q).mp hk
  have hp : (2 : ℚ) ^ binaryExponent q =
      (2 : ℚ) ^ (binaryExponent q - 80) * (2 : ℚ) ^ 80 := by
    rw [← pow_add, Nat.sub_add_cancel he]
  rw [positive_shift_toNat hk]
  simp only [scaledExact, exactReduced, Q, Nat.cast_pow, Nat.cast_ofNat, hp]
  field_simp
  <;> ring

theorem scaledExact_negative_shift {q : ℤ} (hk : sourceShift q < 0) :
    scaledExact q = (q * (2 ^ (-sourceShift q).toNat : ℕ) : ℤ) := by
  have he : binaryExponent q ≤ 80 := by
    unfold sourceShift at hk
    omega
  have hp : (2 : ℚ) ^ 80 =
      (2 : ℚ) ^ (80 - binaryExponent q) * (2 : ℚ) ^ binaryExponent q := by
    rw [← pow_add, Nat.sub_add_cancel he]
  rw [negative_shift_toNat hk]
  simp only [scaledExact, exactReduced, Q, Nat.cast_pow, Nat.cast_ofNat,
    Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat, hp]
  field_simp
  <;> ring

/-- Exact operational binding to Python's signed // and ceildiv branches. -/
theorem sourceRL_eq_floor (q : ℤ) : sourceRL q = ⌊scaledExact q⌋ := by
  by_cases hk : 0 ≤ sourceShift q
  · rw [sourceRL, if_pos hk, scaledExact_positive_shift hk]
    exact (Rat.floor_intCast_div_natCast q _).symm
  · rw [sourceRL, if_neg hk, scaledExact_negative_shift (lt_of_not_ge hk)]
    rw [Int.floor_intCast]

theorem sourceRH_eq_ceil (q : ℤ) : sourceRH q = ⌈scaledExact q⌉ := by
  by_cases hk : 0 ≤ sourceShift q
  · rw [sourceRH, if_pos hk, scaledExact_positive_shift hk]
    exact (Rat.ceil_intCast_div_natCast q _).symm
  · rw [sourceRH, if_neg hk, scaledExact_negative_shift (lt_of_not_ge hk)]
    rw [Int.ceil_intCast]

theorem source_endpoint_width (q : ℤ) : sourceRH q ≤ sourceRL q + 1 := by
  rw [sourceRL_eq_floor, sourceRH_eq_ceil]
  exact Int.ceil_le_floor_add_one _

theorem source_endpoints_exact_of_negative {q : ℤ} (hk : sourceShift q < 0) :
    sourceRL q = sourceRH q := by
  simp only [sourceRL, sourceRH, if_neg (not_le.mpr hk)]

theorem source_reduced_contains (q : ℤ) :
    (sourceRL q : ℚ) / Q ≤ exactReduced q ∧
      exactReduced q ≤ (sourceRH q : ℚ) / Q := by
  rw [sourceRL_eq_floor, sourceRH_eq_ceil]
  constructor
  · apply (div_le_iff₀ Q_pos).mpr
    simpa only [scaledExact, mul_comm] using Int.floor_le (scaledExact q)
  · apply (le_div_iff₀ Q_pos).mpr
    simpa only [scaledExact, mul_comm] using Int.le_ceil (scaledExact q)

theorem source_endpoint_guards {q : ℤ} (hq : 0 < q) :
    (Q : ℤ) ≤ sourceRL q ∧ sourceRL q ≤ sourceRH q ∧ sourceRH q ≤ 2 * Q := by
  obtain ⟨hl, hu⟩ := exactReduced_bounds hq
  have hscaledL : (Q : ℚ) ≤ scaledExact q := by
    simpa only [scaledExact, mul_one] using mul_le_mul_of_nonneg_left hl Q_pos.le
  have hscaledU : scaledExact q < 2 * (Q : ℚ) := by
    simpa only [scaledExact, mul_comm] using mul_lt_mul_of_pos_left hu Q_pos
  rw [sourceRL_eq_floor, sourceRH_eq_ceil]
  refine ⟨Int.le_floor.mpr (by exact_mod_cast hscaledL), Int.floor_le_ceil _, ?_⟩
  exact Int.ceil_le.mpr (by exact_mod_cast hscaledU.le)

theorem source_reduced_contains_real (q : ℤ) :
    (sourceRL q : ℝ) / Q ≤ (exactReduced q : ℝ) ∧
      (exactReduced q : ℝ) ≤ (sourceRH q : ℝ) / Q := by
  constructor
  · exact_mod_cast (source_reduced_contains q).1
  · exact_mod_cast (source_reduced_contains q).2

/-- The precise logarithm identity used by both signed LOG2 branches. -/
theorem log_point_decomposition {q : ℤ} (hq : 0 < q) :
    Real.log ((q : ℝ) / Q) =
      (sourceShift q : ℝ) * Real.log 2 + Real.log (exactReduced q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcast : (exactReduced q : ℝ) = (q : ℝ) / (2 : ℝ) ^ binaryExponent q := by
    simp [exactReduced]
  rw [hcast]
  simp only [Q, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_div hqR.ne' (pow_ne_zero 80 (by norm_num : (2 : ℝ) ≠ 0)),
    Real.log_div hqR.ne' (pow_ne_zero (binaryExponent q) (by norm_num : (2 : ℝ) ≠ 0)),
    Real.log_pow, Real.log_pow]
  norm_num only [sourceShift, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat]
  ring

def atanhParameter (q : ℤ) : ℚ := (exactReduced q - 1) / (exactReduced q + 1)

theorem atanh_parameter_bounds {q : ℤ} (hq : 0 < q) :
    0 ≤ atanhParameter q ∧ atanhParameter q < 1 / 3 := by
  obtain ⟨hl, hu⟩ := exactReduced_bounds hq
  have hd : 0 < exactReduced q + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hl) hd.le
  · apply (div_lt_iff₀ hd).mpr
    linarith

theorem atanh_parameter_bounds_real {q : ℤ} (hq : 0 < q) :
    0 ≤ (atanhParameter q : ℝ) ∧ (atanhParameter q : ℝ) ≤ 1 / 3 := by
  constructor
  · exact_mod_cast (atanh_parameter_bounds hq).1
  · have h : (atanhParameter q : ℝ) ≤ ((1 / 3 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (atanh_parameter_bounds hq).2.le
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

/-- Literal q==Q shortcut in the frozen implementation. -/
theorem sourceShift_Q : sourceShift (Q : ℤ) = 0 := by
  decide +kernel

theorem exactReduced_Q : exactReduced (Q : ℤ) = 1 := by
  decide +kernel

theorem log_point_shortcut : Real.log ((Q : ℝ) / Q) = 0 := by
  exact Real.log_div_self _

end ImbalancedChen.Certificates.P2HistoricLogRangeReduction
