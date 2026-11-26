import ImbalancedChen.Certificates.RationalLogCertificate

/-!
# Working precision and tail of the paired 96-term logarithm

The author's `log_interval` computes at scale `2^224` and returns integers
at scale `2^160`. Its upper endpoint includes one working-scale unit,
which also bounds the remainder used by `RationalLogCertificate` on `[1,2]`.
-/

namespace ImbalancedChen.Certificates.P2OriginalLog96

def workScale : ℤ := 2 ^ 224
def outputScale : ℤ := 2 ^ 160
def outputShift : ℤ := 2 ^ 64

def tail : ℤ := ⌈(9 : ℚ) / (4 * 193 * 3 ^ 193) * (workScale : ℚ)⌉

theorem workScale_pos : 0 < workScale := by norm_num [workScale]
theorem outputScale_pos : 0 < outputScale := by norm_num [outputScale]
theorem outputShift_pos : 0 < outputShift := by norm_num [outputShift]

theorem workScale_eq_mul : workScale = outputScale * outputShift := by
  norm_num [workScale, outputScale, outputShift]

theorem tail_eq_one : tail = 1 := by
  apply le_antisymm
  · unfold tail
    apply Int.ceil_le.mpr
    norm_num [workScale]
  · have h : 0 < tail := by
      unfold tail
      apply Int.lt_ceil.mpr
      norm_num [workScale]
    omega

theorem logParameter_nonneg (q : ℚ) (h1 : 1 ≤ q) : 0 ≤ logParameter q := by
  exact div_nonneg (sub_nonneg.mpr h1) (by linarith : 0 ≤ q + 1)

theorem logParameter_le_third (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    logParameter q ≤ 1 / 3 := by
  unfold logParameter
  apply (div_le_iff₀ (by linarith : 0 < q + 1)).mpr
  linarith only [h2]

theorem remainder_le_tail (q : ℚ) (h1 : 1 ≤ q) (h2 : q ≤ 2) :
    2 * logParameter q ^ 193 / (1 - logParameter q ^ 2) ≤
      (tail : ℚ) / (workScale : ℚ) := by
  have hz := logParameter_nonneg q h1
  have hthird := logParameter_le_third q h1 h2
  have hsquare := pow_le_pow_left₀ hz hthird 2
  have hden : (8 / 9 : ℚ) ≤ 1 - logParameter q ^ 2 := by
    linarith only [hsquare]
  have hpower := pow_le_pow_left₀ hz hthird 193
  calc
    _ ≤ 2 * (1 / 3 : ℚ) ^ 193 / (8 / 9) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hpower (by norm_num))
        (by norm_num) hden
    _ ≤ _ := by rw [tail_eq_one]; norm_num [workScale]

end ImbalancedChen.Certificates.P2OriginalLog96
