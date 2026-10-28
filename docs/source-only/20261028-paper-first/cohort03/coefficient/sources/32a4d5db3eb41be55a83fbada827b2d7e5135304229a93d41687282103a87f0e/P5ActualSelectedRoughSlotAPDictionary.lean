import ImbalancedChen.Part3ActualRoughIntervalAllModuliSW
import ImbalancedChen.Part3RoughAuxDivisibilityTransport
import ImbalancedChen.P5ActualHBDyadicProductWindow

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Literal selected HB one/Mobius role, on its own right-closed interval.
-- The original real Mobius truncation is clipped in BOTH discrepancy
-- terms, and is never discarded or replaced by a different coefficient.

namespace ImbalancedChen.P5Z.ActualSelectedRoughSlotAPDictionary
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.RoughAuxDivisibility20261027
open ImbalancedChen.Part3.RoughAPTwistAverage20261027
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
open ActualRoughHeathBrownWords HBRightClosedDyadicRoles ActualHBDyadicProductWindow

def roughRole (useMu : Bool) : Role := if useMu then .mobius else .one

def selectedCoefficient (b : Block) (useMu : Bool) (z y τ : ℝ) (n : ℕ) : ℂ :=
  blockValue z y (roughRole useMu) b n * phase τ ((n : ℝ)/(lower b : ℝ))

def intervalCarrier (lo hi : ℝ) : Finset ℕ := Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊

def clippedUpper (useMu : Bool) (y hi : ℝ) : ℝ :=
  if useMu then min hi y else hi

theorem mem_interval_real {lo hi : ℝ} (hlo : 0 ≤ lo) {n : ℕ}
    (hn : n ∈ intervalCarrier lo hi) : lo < (n : ℝ) ∧ (n : ℝ) ≤ hi := by
  have hh := Finset.mem_Ioc.mp hn
  have hLoHi : lo ≤ hi := by
    by_contra h
    have hf := Nat.floor_mono (le_of_lt (lt_of_not_ge h))
    omega
  exact ⟨Nat.lt_of_floor_lt hh.1,
    (by exact_mod_cast hh.2).trans (Nat.floor_le (hlo.trans hLoHi))⟩

theorem owns_on_interval {b : Block} {lo hi : ℝ}
    (hb : 1 < (lower b : ℝ)) (hlo : (lower b : ℝ) ≤ lo)
    (hhi : hi ≤ 2*(lower b : ℝ)) {n : ℕ}
    (hn : n ∈ intervalCarrier lo hi) : Owns b n := by
  have hU : 0 < (lower b : ℝ) := by exact_mod_cast lower_pos b
  have hh := mem_interval_real (hU.le.trans hlo) hn
  cases b with
  | unit => simp only [lower,Nat.cast_one] at hb; linarith
  | dyadic k =>
    change 2^k < n ∧ n ≤ 2^(k+1)
    have hl : ((2^k : ℕ) : ℝ) < (n : ℝ) := hlo.trans_lt hh.1
    have hu : (n : ℝ) ≤ 2*((2^k : ℕ) : ℝ) := hh.2.trans hhi
    exact ⟨by exact_mod_cast hl,by simpa only [pow_succ,mul_comm] using
      (show n ≤ 2*(2^k) by exact_mod_cast hu)⟩

-- Changing a carrier by literal zero coefficients changes neither the
-- residue count nor the exact coprime mean. This is finite algebra only.
theorem auxiliarySWError_restrict_exact (S T : Finset ℕ) (α β : ℕ → ℂ)
    (k q b : ℕ) (hTS : T ⊆ S)
    (hEq : ∀ n ∈ T, α n = β n)
    (hZero : ∀ n ∈ S, n ∉ T → α n = 0) :
    auxiliarySWError S α k q b = auxiliarySWError T β k q b := by
  rw [auxiliarySWError_eq_kernel,auxiliarySWError_eq_kernel]
  calc
    _ = ∑ n ∈ T, α n * auxiliaryKernel k q b n := by
      symm
      exact Finset.sum_subset hTS (fun n hn hnot => by rw [hZero n hn hnot,zero_mul])
    _ = _ := Finset.sum_congr rfl (fun n hn => by rw [hEq n hn])

theorem selected_error_eq_clipped (b : Block) (useMu : Bool) (z y τ lo hi : ℝ)
    (hb : 1 < (lower b : ℝ)) (hlo : (lower b : ℝ) ≤ lo)
    (hhi : hi ≤ 2*(lower b : ℝ)) (k q residue : ℕ) :
    auxiliarySWError (intervalCarrier lo hi)
      (selectedCoefficient b useMu z y τ) k q residue =
    auxiliarySWError (intervalCarrier lo (clippedUpper useMu y hi))
      (actualBaseCoefficient useMu z τ (lower b : ℝ) (fun _ => 1)) k q residue := by
  have hU : 0 < (lower b : ℝ) := by exact_mod_cast lower_pos b
  have hclip : clippedUpper useMu y hi ≤ hi := by
    cases useMu <;> simp [clippedUpper]
  have hsub : intervalCarrier lo (clippedUpper useMu y hi) ⊆ intervalCarrier lo hi := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono hclip)⟩
  apply auxiliarySWError_restrict_exact _ _ _ _ k q residue hsub
  · intro n hn
    have hS := hsub hn
    have ho := owns_on_interval hb hlo hhi hS
    have hh := mem_interval_real (hU.le.trans hlo) hn
    have hn0 : n ≠ 0 := by
      have hp : 0 < (n : ℝ) := (hU.trans_le hlo).trans hh.1
      exact_mod_cast hp.ne'
    cases useMu with
    | false =>
      simp only [selectedCoefficient,roughRole,Bool.false_eq_true,if_false,
        blockValue,if_pos ho,actual,actualBaseCoefficient,if_neg hn0,
        RoughAPPrincipalCancellation20261027.roughCoefficient,mul_one]
      ring
    | true =>
      have hny : (n : ℝ) ≤ y := hh.2.trans (min_le_right hi y)
      simp only [selectedCoefficient,roughRole,if_true,blockValue,if_pos ho,
        actual,roughMuTrunc,if_pos hny,actualBaseCoefficient,if_neg hn0,
        RoughAPPrincipalCancellation20261027.roughCoefficient,mul_one]
      ring
  · intro n hn hnot
    cases useMu with
    | false => exact False.elim (hnot (by simpa [clippedUpper] using hn))
    | true =>
      have hh := mem_interval_real (hU.le.trans hlo) hn
      have hny : ¬(n : ℝ) ≤ y := by
        intro hny
        have hmin : (n : ℝ) ≤ min hi y := le_min hh.2 hny
        have hnmin : n ≤ ⌊min hi y⌋₊ :=
          (Nat.le_floor_iff ((Nat.cast_nonneg n).trans hmin)).mpr hmin
        exact hnot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
          by simpa [clippedUpper] using hnmin⟩)
      simp only [selectedCoefficient,roughRole,if_true,blockValue]
      split_ifs <;> simp [actual,roughMuTrunc,hny]

theorem selected_error_zero_of_cutoff_before_interval (b : Block) (z y τ lo hi : ℝ)
    (hb : 1 < (lower b : ℝ)) (hlo : (lower b : ℝ) ≤ lo)
    (hy : y ≤ lo) (k q residue : ℕ) :
    auxiliarySWError (intervalCarrier lo hi)
      (selectedCoefficient b true z y τ) k q residue = 0 := by
  rw [auxiliarySWError_eq_kernel]
  apply Finset.sum_eq_zero
  intro n hn
  have hU : 0 < (lower b : ℝ) := by exact_mod_cast lower_pos b
  have hh := mem_interval_real (hU.le.trans hlo) hn
  have hny : ¬(n : ℝ) ≤ y := by linarith
  have hz : selectedCoefficient b true z y τ n = 0 := by
    simp only [selectedCoefficient,roughRole,if_true,blockValue]
    split_ifs <;> simp [actual,roughMuTrunc,hny]
  rw [hz,zero_mul]

end
end ImbalancedChen.P5Z.ActualSelectedRoughSlotAPDictionary
