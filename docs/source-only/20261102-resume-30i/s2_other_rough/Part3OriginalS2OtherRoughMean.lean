import ImbalancedChen.Part3OriginalS2OtherRoughCounting
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay the actual S2 mean-leg multiple sum by an ordinary fixed divisor
moment. The sole remaining arithmetic sum is the nonzero shifted-product
moment. This is not an arbitrary-log bound for otherRoughCorrection.
-/
namespace ImbalancedChen.Part3OriginalS2OtherRoughMean

open ImbalancedChen ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2OtherRoughSource
open ImbalancedChen.Part3OriginalS2OtherRoughCounting
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Classical Finset
open scoped BigOperators

noncomputable section

theorem ordinary_tau_square_mean {X : ℝ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Icc 1 (Nat.floor X), tau n ^ 2) ≤ X * (1 + Real.log X) ^ 3 := by
  have hI : Finset.Icc 1 (Nat.floor X) = Finset.Ioc 0 (Nat.floor X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI]
  have h := sum_fouvryTau_pow_le_real (k := 2) (r := 2) (by norm_num) hX
  rw [fouvryTau_two] at h
  simpa only [tau, show (2 : ℕ) ^ 2 - 1 = 3 by norm_num] using h

/-- Quotient injection pays one factor 1/p at the genuine multiple source.
Only positive support and the displayed finite upper bound are required. -/
theorem multiples_tau_square_mean (S : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (P : ℝ) (hpP : (p : ℝ) ≤ P)
    (hS : ∀ s ∈ S, 0 < s ∧ (s : ℝ) ≤ P ∧ p ∣ s) :
    (∑ s ∈ S, tau s ^ 2) ≤
      tau p ^ 2 * (P / p) * (1 + Real.log (P / p)) ^ 3 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hX : 1 ≤ P / p := (le_div_iff₀ hpR).mpr (by simpa using hpP)
  have hinj : Set.InjOn (fun s : ℕ => s / p) S := by
    intro s hs t ht hq
    calc
      s = p * (s / p) := (Nat.mul_div_cancel' (hS s hs).2.2).symm
      _ = p * (t / p) := by rw [hq]
      _ = t := Nat.mul_div_cancel' (hS t ht).2.2
  have hmap : S.image (fun s => s / p) ⊆ Finset.Icc 1 (Nat.floor (P / p)) := by
    intro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hspos, hsP, hps⟩ := hS s hs
    have he := Nat.mul_div_cancel' hps
    have hqpos : 0 < s / p := by
      by_contra h
      have hz : s / p = 0 := Nat.eq_zero_of_not_pos h
      rw [hz, mul_zero] at he
      omega
    refine Finset.mem_Icc.mpr ⟨hqpos, Nat.le_floor ?_⟩
    apply (le_div_iff₀ hpR).mpr
    have heR : (p : ℝ) * (s / p : ℕ) = (s : ℝ) := by exact_mod_cast he
    nlinarith
  calc
    _ ≤ ∑ s ∈ S, tau p ^ 2 * tau (s / p) ^ 2 := by
      apply Finset.sum_le_sum
      intro s hs
      have hτ : tau s ≤ tau p * tau (s / p) := by
        conv_lhs => rw [← Nat.mul_div_cancel' (hS s hs).2.2]
        exact tau_mul_le _ _
      simpa only [mul_pow] using pow_le_pow_left₀ (tau_nonneg s) hτ 2
    _ = tau p ^ 2 * ∑ s ∈ S, tau (s / p) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = tau p ^ 2 * ∑ u ∈ S.image (fun s => s / p), tau u ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ tau p ^ 2 * ∑ u ∈ Finset.Icc 1 (Nat.floor (P / p)), tau u ^ 2 :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hmap (fun _ _ _ => sq_nonneg _)) (sq_nonneg _)
    _ ≤ tau p ^ 2 * ((P / p) * (1 + Real.log (P / p)) ^ 3) :=
      mul_le_mul_of_nonneg_left (ordinary_tau_square_mean hX) (sq_nonneg _)
    _ = _ := by ring

theorem tau_prime {p : ℕ} (hp : p.Prime) : tau p = 2 := by
  have hdivs : p.divisors = {1, p} := by
    ext n
    simp [Nat.mem_divisors, Nat.dvd_prime hp, hp.ne_zero]
  simp [tau, hdivs, hp.ne_one.symm]

/-- Original s~R, restricted by the actual common prime. Its divisor
square costs precisely an ordinary mean, with no x^epsilon loss. -/
theorem actual_meanMultiples_bound (d : MediumAtom) (z : ℝ) (k : Key)
    (p : ℕ) (hp : p ∈ commonPrimes d z k) :
    (∑ s ∈ meanMultiples k p, tau s ^ 2) ≤
      (8 * singleZeroR k / p) * (1 + Real.log (2 * singleZeroR k)) ^ 3 := by
  obtain ⟨hpbank, hpprime, hzp, hpa⟩ := Finset.mem_filter.mp hp
  have hpP : (p : ℝ) ≤ 2 * singleZeroR k := by
    have hh : p < 2 ^ (k.w + 1) := Finset.mem_range.mp hpbank
    have hhR : (p : ℝ) < (2 : ℝ) ^ (k.w + 1) := by exact_mod_cast hh
    simpa only [singleZeroR, pow_succ, mul_comm] using hhR.le
  have hS : ∀ s ∈ meanMultiples k p,
      0 < s ∧ (s : ℝ) ≤ 2 * singleZeroR k ∧ p ∣ s := by
    intro s hs
    obtain ⟨hs, hps⟩ := Finset.mem_filter.mp hs
    obtain ⟨hslo, hshi⟩ := Finset.mem_Ico.mp hs
    refine ⟨(pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le hslo, ?_, hps⟩
    have hshiR : (s : ℝ) < (2 : ℝ) ^ (k.w + 1) := by exact_mod_cast hshi
    simpa only [singleZeroR, pow_succ, mul_comm] using hshiR.le
  have hraw := multiples_tau_square_mean (meanMultiples k p) p hpprime.pos
    (2 * singleZeroR k) hpP hS
  rw [tau_prime hpprime] at hraw
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_lt.le
  have hR : 0 < singleZeroR k := by unfold singleZeroR; positivity
  have hX : 1 ≤ 2 * singleZeroR k / p :=
    (le_div_iff₀ hpR).mpr (by simpa using hpP)
  have hle : 2 * singleZeroR k / p ≤ 2 * singleZeroR k :=
    div_le_self (by positivity) hp1
  have hlog := Real.log_le_log (zero_lt_one.trans_le hX) hle
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + Real.log (2 * singleZeroR k / p) by
      linarith [Real.log_nonneg hX]) (add_le_add_left hlog 1) 3
  calc
    _ ≤ (2 : ℝ) ^ 2 * (2 * singleZeroR k / p) *
        (1 + Real.log (2 * singleZeroR k / p)) ^ 3 := hraw
    _ ≤ (2 : ℝ) ^ 2 * (2 * singleZeroR k / p) *
        (1 + Real.log (2 * singleZeroR k)) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

def shiftedRoughMoment (d : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  ∑ p ∈ commonPrimes d z k, (1 / (p : ℝ)) *
    (∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6)

theorem roughMoment_le_paid_mean (d : MediumAtom) (z : ℝ) (k : Key) :
    roughMoment d z k ≤
      8 * singleZeroR k * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
        shiftedRoughMoment d z k := by
  unfold roughMoment shiftedRoughMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have h := mul_le_mul_of_nonneg_right (actual_meanMultiples_bound d z k p hp)
    (show 0 ≤ ∑ v ∈ productMultiples d p, tau v * tau (shiftAbs d.residue v) ^ 6 by
      unfold tau
      positivity)
  convert h using 1 <;> ring

/-- The first 1/p has been PAID, on the unchanged actual S2 source.
The remaining second 1/p is a shifted mixed progression theorem, still
an internal manuscript obligation and not an external estimate port. -/
theorem actual_otherRough_le_shifted_moment
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    ‖otherRoughCorrection d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
      (48 * d.U / singleZeroY d k) * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
        shiftedRoughMoment d z k := by
  have hY : 0 < singleZeroY d k := by
    unfold singleZeroY
    have hQ := zero_lt_one.trans_le hd.2.2.1
    positivity
  have hR : 0 < singleZeroR k := by unfold singleZeroR; positivity
  calc
    _ ≤ (6 * d.U / (singleZeroY d k * singleZeroR k)) * roughMoment d z k :=
      actual_otherRough_le_collapsed_moment hd z hz k
    _ ≤ (6 * d.U / (singleZeroY d k * singleZeroR k)) *
        (8 * singleZeroR k * (1 + Real.log (2 * singleZeroR k)) ^ 3 *
          shiftedRoughMoment d z k) :=
      mul_le_mul_of_nonneg_left (roughMoment_le_paid_mean d z k)
        (by have hU := hd.1; positivity)
    _ = _ := by field_simp [hY.ne', hR.ne']; ring

end
end ImbalancedChen.Part3OriginalS2OtherRoughMean

