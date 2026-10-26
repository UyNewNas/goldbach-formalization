import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.P5ZU1011OriginalFifteenMediumNumericGates

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Unique positive-integer dyadic blocks, including the unit. The closed
factorCarrier display is used only as an enclosing carrier: its upper
boundary belongs to the NEXT half-open block. No factor-two enlargement
of the dyadic LOWER length is required by the numerical Medium gates.
-/
namespace ImbalancedChen.P5Z.UniqueHalfOpenDyadicFactors
noncomputable section
open Classical
open scoped BigOperators
open U1011OriginalFifteenMediumNumericGates

def length (k : ℕ) : ℝ := ((2 ^ k : ℕ) : ℝ)

def piece (f : ℕ → ℝ) (k n : ℕ) : ℝ :=
  if 0 < n ∧ Nat.log2 n = k then f n else 0

def indices (Q : ℝ) : Finset ℕ := Finset.range (Nat.log2 (Nat.floor Q) + 1)

theorem piece_one (f : ℕ → ℝ) : piece f 0 1 = f 1 := by simp [piece]

theorem piece_nonzero {f : ℕ → ℝ} {k n : ℕ} (h : piece f k n ≠ 0) :
    f n ≠ 0 ∧ 0 < n ∧ Nat.log2 n = k := by
  by_cases hc : 0 < n ∧ Nat.log2 n = k
  · exact ⟨by simpa [piece, hc] using h, hc⟩
  · simp [piece, hc] at h

theorem half_open {n k : ℕ} (hn : 0 < n) :
    Nat.log2 n = k ↔ 2 ^ k ≤ n ∧ n < 2 ^ (k + 1) := Nat.log2_eq_iff hn.ne'

theorem upper_boundary_zero (f : ℕ → ℝ) (k : ℕ) :
    piece f k (2 ^ (k + 1)) = 0 := by
  by_contra h
  have hh := (half_open (piece_nonzero h).2.1).mp (piece_nonzero h).2.2
  exact (lt_irrefl _) hh.2

theorem piece_support {f : ℕ → ℝ} {k n : ℕ} (h : piece f k n ≠ 0) :
    n ∈ Part3.factorCarrier (length k) := by
  have hn := piece_nonzero h
  have hb := (half_open hn.2.1).mp hn.2.2
  have h2 : 2 * length k = ((2 ^ (k + 1) : ℕ) : ℝ) := by
    simp only [length, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  apply Finset.mem_Icc.mpr
  constructor
  · simpa [length] using hb.1
  · change n ≤ Nat.floor (2 * length k)
    rw [h2, Nat.floor_natCast]
    exact hb.2.le

theorem active_index_bound {Q : ℝ} {n k : ℕ} (hn : 0 < n)
    (hlog : Nat.log2 n = k) (hQ : (n : ℝ) ≤ Q) : k ∈ indices Q := by
  have hfloor : n ≤ Nat.floor Q := Nat.le_floor hQ
  have hfpos : Nat.floor Q ≠ 0 := by omega
  apply Finset.mem_range.mpr
  have hpower : 2 ^ k ≤ Nat.floor Q := by
    rw [← hlog]
    exact (Nat.log2_self_le hn.ne').trans hfloor
  exact Nat.lt_succ_of_le ((Nat.le_log2 hfpos).mpr hpower)

theorem active_length_le {f : ℕ → ℝ} {Q : ℝ} {k n : ℕ}
    (h : piece f k n ≠ 0) (hQ : (n : ℝ) ≤ Q) : length k ≤ Q := by
  have hb := (half_open (piece_nonzero h).2.1).mp (piece_nonzero h).2.2
  exact (by exact_mod_cast hb.1 : length k ≤ (n : ℝ)).trans hQ

/-- Exact finite FUNCTION identity, not merely a bound on its mass. -/
theorem reconstruct (f : ℕ → ℝ) (Q : ℝ) (hz : f 0 = 0)
    (hs : ∀ n, f n ≠ 0 → (n : ℝ) ≤ Q) (n : ℕ) :
    (∑ k ∈ indices Q, piece f k n) = f n := by
  by_cases hf : f n = 0
  · simp [piece, hf]
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    exact hf (by simpa [this] using hz)
  have hk := active_index_bound hn rfl (hs n hf)
  rw [Finset.sum_eq_single (Nat.log2 n)]
  · simp [piece, hn]
  · intro k hkm hne
    simp [piece, Ne.symm hne]
  · exact fun h => False.elim (h hk)

theorem piece_unit (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (k n : ℕ) :
    |piece f k n| ≤ 1 := by
  unfold piece
  split_ifs <;> simp_all

theorem piece_coprime (f : ℕ → ℝ) (N : ℕ)
    (hc : ∀ n, f n ≠ 0 → Nat.Coprime n N) (k n : ℕ)
    (h : piece f k n ≠ 0) : Nat.Coprime n N := hc n (piece_nonzero h).1

theorem length_one_le (k : ℕ) : 1 ≤ length k := by
  exact_mod_cast (Nat.one_le_pow k 2 (by omega))

/-- The exact finite three-block bank cost. No unproved asymptotic
logarithmic simplification is attached to this identity. -/
theorem block_bank_card (Q1 Q2 Q3 : ℝ) :
    ((indices Q1).product ((indices Q2).product (indices Q3))).card =
      (Nat.log2 (Nat.floor Q1) + 1) *
        ((Nat.log2 (Nat.floor Q2) + 1) * (Nat.log2 (Nat.floor Q3) + 1)) := by
  simp [indices]

/-- Every monomial is increasing in each positive factor length. Thus
the lower dyadic lengths inherit the EXACT four strict gates; no 2Q
inflation or reserve expenditure occurs at this step. -/
theorem numeric_downward {N : ℕ} {x U A B C a b c s : ℝ}
    (hU : 0 ≤ U) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haA : a ≤ A) (hbB : b ≤ B) (hcC : c ≤ C)
    (hg : NumericGates N x U A B C s) : NumericGates N x U a b c s := by
  have hA : 0 ≤ A := ha.trans haA
  have hB : 0 ≤ B := hb.trans hbB
  have hC : 0 ≤ C := hc.trans hcC
  have hb5 : b ^ 5 ≤ B ^ 5 := pow_le_pow_left₀ hb hbB 5
  have hc2 : c ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hc hcC 2
  have hbR : b ^ (73 / 16 : ℝ) ≤ B ^ (73 / 16 : ℝ) :=
    Real.rpow_le_rpow hb hbB (by norm_num)
  have hcR : c ^ (39 / 16 : ℝ) ≤ C ^ (39 / 16 : ℝ) :=
    Real.rpow_le_rpow hc hcC (by norm_num)
  refine ⟨haA.trans_lt hg.1, ?_, ?_, ?_⟩
  · exact (mul_le_mul (mul_le_mul_of_nonneg_left hbB (sq_nonneg U)) hc2
      (sq_nonneg c) (mul_nonneg (sq_nonneg U) hB)).trans_lt hg.2.1
  · have hfirst : (N : ℝ) ^ (7 / 32 : ℝ) * U * a ≤ (N : ℝ) ^ (7 / 32 : ℝ) * U * A :=
      mul_le_mul_of_nonneg_left haA (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) hU)
    exact (mul_le_mul (mul_le_mul hfirst hb5 (pow_nonneg hb 5)
      (by positivity)) hc2 (sq_nonneg c) (by positivity)).trans_lt hg.2.2.1
  · have hfirst : U ^ (23 / 16 : ℝ) * a ≤ U ^ (23 / 16 : ℝ) * A :=
      mul_le_mul_of_nonneg_left haA (Real.rpow_nonneg hU _)
    exact (mul_le_mul (mul_le_mul hfirst hbR (Real.rpow_nonneg hb _) (by positivity))
      hcR (Real.rpow_nonneg hc _) (by positivity)).trans_lt hg.2.2.2

end
end ImbalancedChen.P5Z.UniqueHalfOpenDyadicFactors
