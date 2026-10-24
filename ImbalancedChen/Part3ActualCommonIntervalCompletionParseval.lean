import ImbalancedChen.Part3ActualCommonIntervalCompletionL1
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED. This module supplies the arithmetic missing from
the actual common-mask L1 completion: exact finite Parseval, exact occupancy
for arbitrary intervals (including wraparound), and the resulting L2 cost.
The actual completion has `P.hi < q`, so its final coefficient cost is the
short-interval special case. No spectral saving is claimed.
-/

namespace ImbalancedChen.Part3.ActualCommonIntervalCompletionParsevalSourceOnly
noncomputable section
open Classical Finset
open scoped BigOperators ComplexConjugate
open P3ActualLiteralPacketIntegralSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly

variable {ι : Type*}

/-- The same negative-sign DFT sum as `finiteFourierCoeff_interval`, but with
no period gate, so it also has a valid interpretation after wraparound. -/
def wrappedIntervalCoeff (L U q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ m ∈ Finset.Ico L U, ZMod.stdAddChar (-((m : ZMod q) * h))

def wrappedOccupancy (L U q : ℕ) [NeZero q] (r : ZMod q) : ℕ :=
  ((Finset.Ico L U).filter (fun m => (m : ZMod q) = r)).card

private theorem star_char {q : ℕ} [NeZero q] (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have hneg : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hstar : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left hstar).trans
    (eq_inv_of_mul_eq_one_left hneg).symm

private theorem square_cast (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
  exact (Complex.mul_conj z).symm

/-- Grouping a possibly wrapped interval by its complete residue fibres. -/
theorem wrappedIntervalCoeff_eq_occupancy_dft (L U q : ℕ) [NeZero q]
    (h : ZMod q) :
    wrappedIntervalCoeff L U q h =
      ∑ r : ZMod q, (wrappedOccupancy L U q r : ℂ) *
        ZMod.stdAddChar (-(r * h)) := by
  unfold wrappedIntervalCoeff wrappedOccupancy
  calc
    (∑ m ∈ Finset.Ico L U, ZMod.stdAddChar (-((m : ZMod q) * h))) =
        ∑ m ∈ Finset.Ico L U, ∑ r : ZMod q,
          if (m : ZMod q) = r then ZMod.stdAddChar (-(r * h)) else 0 := by
      apply Finset.sum_congr rfl
      intro m _hm
      simp
    _ = ∑ r : ZMod q, ∑ m ∈ Finset.Ico L U,
          if (m : ZMod q) = r then ZMod.stdAddChar (-(r * h)) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Exact finite Parseval for the common interval, with every collision from
multiple turns around `ZMod q` retained. -/
theorem wrappedIntervalCoeff_parseval (L U q : ℕ) [NeZero q] :
    (∑ h : ZMod q, ‖wrappedIntervalCoeff L U q h‖ ^ 2) =
      (q : ℝ) * ∑ r : ZMod q, (wrappedOccupancy L U q r : ℝ) ^ 2 := by
  let a : ZMod q → ℂ := fun r => (wrappedOccupancy L U q r : ℂ)
  have hpoint (h : ZMod q) :
      ((‖∑ r : ZMod q, a r * ZMod.stdAddChar (-(r * h))‖ ^ 2 : ℝ) : ℂ) =
        ∑ r : ZMod q, ∑ s : ZMod q,
          a r * star (a s) * ZMod.stdAddChar (h * (s - r)) := by
    rw [square_cast, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    apply Finset.sum_congr rfl
    intro s _hs
    calc
      (a r * ZMod.stdAddChar (-(r * h))) *
          star (a s * ZMod.stdAddChar (-(s * h))) =
        a r * star (a s) *
          (ZMod.stdAddChar (-(r * h)) *
            star (ZMod.stdAddChar (-(s * h)))) := by
        rw [star_mul]
        ring
      _ = a r * star (a s) * ZMod.stdAddChar (h * (s - r)) := by
        rw [star_char, ← ZMod.stdAddChar.map_add_eq_mul]
        congr 1
        ring
  apply Complex.ofReal_injective
  calc
    (((∑ h : ZMod q, ‖wrappedIntervalCoeff L U q h‖ ^ 2) : ℝ) : ℂ) =
        ∑ h : ZMod q, ∑ r : ZMod q, ∑ s : ZMod q,
          a r * star (a s) * ZMod.stdAddChar (h * (s - r)) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      simpa only [a, wrappedIntervalCoeff_eq_occupancy_dft] using hpoint h
    _ = ∑ r : ZMod q, ∑ s : ZMod q,
          a r * star (a s) *
            (∑ h : ZMod q, ZMod.stdAddChar (h * (s - r))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
    _ = (q : ℂ) * ∑ r : ZMod q, a r * star (a r) := by
      simp_rw [ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
      simp only [sub_eq_zero]
      simp [Finset.mul_sum, mul_assoc]
    _ = (((q : ℝ) * ∑ r : ZMod q,
          (wrappedOccupancy L U q r : ℝ) ^ 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum,
        Complex.ofReal_pow, a, map_natCast, star_natCast]
      rw [Finset.mul_sum]

private theorem occupancy_eq_count_sub (L U q : ℕ) [NeZero q]
    (hLU : L ≤ U) (r : ZMod q) :
    wrappedOccupancy L U q r =
      U.count (fun n => n ≡ r.val [MOD q]) -
        L.count (fun n => n ≡ r.val [MOD q]) := by
  have hpred (m : ℕ) : ((m : ZMod q) = r) ↔ m ≡ r.val [MOD q] := by
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.natCast_eq_natCast_iff m r.val q)
  have hsub : (Finset.range L).filter (fun n => n ≡ r.val [MOD q]) ⊆
      (Finset.range U).filter (fun n => n ≡ r.val [MOD q]) :=
    Finset.filter_subset_filter _ (Finset.range_mono hLU)
  have he : (Finset.Ico L U).filter (fun n => n ≡ r.val [MOD q]) =
      (Finset.range U).filter (fun n => n ≡ r.val [MOD q]) \
        (Finset.range L).filter (fun n => n ≡ r.val [MOD q]) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff,
      Finset.mem_range]
    by_cases hn : n ≡ r.val [MOD q] <;> simp [hn] <;> omega
  unfold wrappedOccupancy
  simp_rw [hpred]
  rw [he, Finset.card_sdiff_of_subset hsub,
    ← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]

/-- Every residue has either `a` or `a+1` points of an interval of length
`a*q+b`. This explicitly includes the wraparound case `a>0`. -/
theorem wrappedOccupancy_eq_quot_or_succ (L U q : ℕ) [NeZero q]
    (hLU : L ≤ U) (r : ZMod q) :
    wrappedOccupancy L U q r = (U - L) / q ∨
      wrappedOccupancy L U q r = (U - L) / q + 1 := by
  have hq : 0 < q := NeZero.pos q
  rw [occupancy_eq_count_sub L U q hLU r,
    Nat.count_modEq_card U hq r.val,
    Nat.count_modEq_card L hq r.val]
  have hU : U = L + (U - L) := by omega
  have hUmod := Nat.mod_lt U hq
  have hLmod := Nat.mod_lt L hq
  have hNmod := Nat.mod_lt (U - L) hq
  have hUdiv := Nat.mod_add_div U q
  have hLdiv := Nat.mod_add_div L q
  have hNdiv := Nat.mod_add_div (U - L) q
  split_ifs <;> omega

/-- The fibres partition the *literal* interval, including q=1 and empty
intervals. -/
theorem wrappedOccupancy_sum (L U q : ℕ) [NeZero q] :
    (∑ r : ZMod q, wrappedOccupancy L U q r) = U - L := by
  simp only [wrappedOccupancy]
  calc
    ∑ r : ZMod q, ((Finset.Ico L U).filter
      (fun m => (m : ZMod q) = r)).card =
        ∑ r : ZMod q, ∑ m ∈ Finset.Ico L U,
          if (m : ZMod q) = r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← Finset.sum_filter]
      simp
    _ = ∑ m ∈ Finset.Ico L U, ∑ r : ZMod q,
          if (m : ZMod q) = r then 1 else 0 := Finset.sum_comm
    _ = (Finset.Ico L U).card := by simp
    _ = U - L := by simp

/-- Exact arithmetic occupancy energy: if `N=U-L=a*q+b`, then the square
sum is `q*a²+b*(2a+1)`; no short-interval assumption is made. -/
theorem wrappedOccupancy_square_sum (L U q : ℕ) [NeZero q] :
    (∑ r : ZMod q, (wrappedOccupancy L U q r : ℝ) ^ 2) =
      (q : ℝ) * (((U - L) / q : ℕ) : ℝ) ^ 2 +
        (((U - L) % q : ℕ) : ℝ) *
          (2 * (((U - L) / q : ℕ) : ℝ) + 1) := by
  by_cases hLU : L ≤ U
  · let a : ℕ := (U - L) / q
    let b : ℕ := (U - L) % q
    have hsum := wrappedOccupancy_sum L U q
    have hdiv : U - L = q * a + b := by
      dsimp [a, b]
      exact (Nat.mod_add_div (U - L) q).symm.trans (by ac_rfl)
    have hdivR : ((U - L : ℕ) : ℝ) = (q : ℝ) * a + b := by
      exact_mod_cast hdiv
    have hpoint (r : ZMod q) :
        (wrappedOccupancy L U q r : ℝ) ^ 2 =
          (a : ℝ) ^ 2 + (2 * (a : ℝ) + 1) *
            ((wrappedOccupancy L U q r : ℝ) - a) := by
      rcases wrappedOccupancy_eq_quot_or_succ L U q hLU r with h | h
      · simp [a, h]
      · simp [a, h]; ring
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    have hsumR : (∑ r : ZMod q, (wrappedOccupancy L U q r : ℝ)) = U - L := by
      exact_mod_cast hsum
    rw [hsumR]
    dsimp [a, b]
    nlinarith [hdivR]
  · have hUL : U ≤ L := by omega
    have hzero : Finset.Ico L U = ∅ := Ico_eq_empty_of_le hUL
    simp [wrappedOccupancy, hzero]

theorem wrappedIntervalCoeff_parseval_arithmetic (L U q : ℕ) [NeZero q] :
    (∑ h : ZMod q, ‖wrappedIntervalCoeff L U q h‖ ^ 2) =
      (q : ℝ) * ((q : ℝ) * (((U - L) / q : ℕ) : ℝ) ^ 2 +
        (((U - L) % q : ℕ) : ℝ) *
          (2 * (((U - L) / q : ℕ) : ℝ) + 1)) := by
  rw [wrappedIntervalCoeff_parseval, wrappedOccupancy_square_sum]

/-- The actual completion's period gate makes its common interval shorter
than q. Its finite DFT is therefore exactly the no-wrap specialization. -/
theorem actual_finiteFourierCoeff_parseval (P : PacketData ι) (a b q : ℕ)
    [NeZero q] (hperiod : P.hi < q) :
    (∑ h : ZMod q, ‖finiteFourierCoeff P a b q h‖ ^ 2) =
      (q : ℝ) * ((completionHi P a b - completionLo P a b : ℕ) : ℝ) := by
  let L := completionLo P a b
  let U := completionHi P a b
  have hLU : L ≤ U := completionLo_le_hi P a b
  have hlen : U - L < q := by
    have hU : U ≤ P.hi := min_le_left _ _
    omega
  have hcoef (h : ZMod q) :
      finiteFourierCoeff P a b q h = wrappedIntervalCoeff L U q h := by
    rw [finiteFourierCoeff_interval P a b q hperiod]
    rfl
  simp_rw [hcoef, wrappedIntervalCoeff_parseval_arithmetic]
  simp [Nat.div_eq_of_lt hlen, Nat.mod_eq_of_lt hlen]

/-- Exact squared L2 fee for the already proved actual normalized
completion. This is `length/q`, not an assumed logarithmic h-energy. -/
theorem actual_normalizedFourierCoeff_energy (P : PacketData ι) (a b q : ℕ)
    [NeZero q] (hperiod : P.hi < q) :
    (∑ h : ZMod q, ‖normalizedFourierCoeff P a b q h‖ ^ 2) =
      ((completionHi P a b - completionLo P a b : ℕ) : ℝ) / q := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  simp only [normalizedFourierCoeff_norm, div_pow, ← Finset.sum_div]
  rw [actual_finiteFourierCoeff_parseval P a b q hperiod]
  field_simp [ne_of_gt hq]
  ring

/-- Sharp Cauchy completion cost for the actual common-mask coefficients. -/
theorem actual_normalized_completion_sq (P : PacketData ι) (a b q : ℕ)
    [NeZero q] (hperiod : P.hi < q) (G : ZMod q → ℂ) :
    ‖∑ h : ZMod q, normalizedFourierCoeff P a b q h * G h‖ ^ 2 ≤
      (((completionHi P a b - completionLo P a b : ℕ) : ℝ) / q) *
        ∑ h : ZMod q, ‖G h‖ ^ 2 := by
  have ht := norm_sum_le (Finset.univ : Finset (ZMod q))
    (fun h => normalizedFourierCoeff P a b q h * G h)
  have hsq :
      ‖∑ h : ZMod q, normalizedFourierCoeff P a b q h * G h‖ ^ 2 ≤
        (∑ h : ZMod q, ‖normalizedFourierCoeff P a b q h‖ * ‖G h‖) ^ 2 := by
    simpa only [norm_mul, pow_two] using
      mul_le_mul ht ht (norm_nonneg _)
        (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun h => ‖normalizedFourierCoeff P a b q h‖) (fun h => ‖G h‖)
  exact hsq.trans (by simpa only [actual_normalizedFourierCoeff_energy P a b q hperiod]
    using hCS)

end
end ImbalancedChen.Part3.ActualCommonIntervalCompletionParsevalSourceOnly
