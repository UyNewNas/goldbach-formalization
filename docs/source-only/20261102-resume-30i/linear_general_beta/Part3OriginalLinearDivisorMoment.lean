import ImbalancedChen.Part3OriginalLinearDiscardCountPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original manuscript medium proposition and completion note section 3.
The physical alpha/beta coefficient is bounded on its actual product
fibres by tau(v)^(B+1), for every fixed B. The deleted count and the
UNCHANGED coprime mean are both compared to independently defined
positive moments. No progression estimate is assumed here.
-/

namespace ImbalancedChen.Part3.OriginalLinearDivisorMoment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumActualPostSquareDeletion20261028
open OriginalLinearDiscardModulusBinding20261028
open OriginalLinearDiscardCountPayment20261102
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2ShiuPrimitiveFiber

def divisorProgressionMoment (C : ℕ) (atom : MediumAtom) (ell : ℕ) : ℝ :=
  ∑ v ∈ psiMNImage atom,
    if Int.ModEq ell (v : ℤ) atom.residue then (v.divisors.card : ℝ) ^ C else 0

theorem divisorProgressionMoment_nonneg (C : ℕ) (atom : MediumAtom) (ell : ℕ) :
    0 ≤ divisorProgressionMoment C atom ell := by
  unfold divisorProgressionMoment
  apply sum_nonneg
  intro v hv
  split_ifs <;> positivity

theorem divisorProgressionMoment_one (C : ℕ) (atom : MediumAtom) :
    divisorProgressionMoment C atom 1 =
      ∑ v ∈ psiMNImage atom, (v.divisors.card : ℝ) ^ C := by
  simp [divisorProgressionMoment, Int.ModEq]

/-- Every divisor of m is a divisor of the positive physical product v.
This is a divisibility argument, not a pointwise x^epsilon bound. -/
theorem beta_norm_le_product_divisor_power
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom)
    {nm : ℕ × ℕ} (hnm : nm ∈ originalMNCarrier atom)
    {v : ℕ} (hv : 0 < v) (hprod : nm.1 * nm.2 = v) :
    ‖atom.alpha nm.1‖ * ‖atom.beta nm.2‖ ≤ (v.divisors.card : ℝ) ^ B := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hα, _, hβ, _⟩ := hA
  obtain ⟨hn, hm⟩ := mem_product.mp hnm
  have hdiv : nm.2 ∣ v := by rw [← hprod]; exact dvd_mul_left _ _
  have htau : (nm.2.divisors.card : ℝ) ≤ (v.divisors.card : ℝ) := by
    exact_mod_cast card_le_card (Nat.divisors_subset_of_dvd hv.ne' hdiv)
  calc
    _ ≤ 1 * (nm.2.divisors.card : ℝ) ^ B :=
      mul_le_mul (hα _ hn) (hβ _ hm) (norm_nonneg _) zero_le_one
    _ ≤ _ := by
      simpa only [one_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) htau B

/-- Actual finite product-fibre reindexing, with an arbitrary nonnegative
test function of v. The extra tau(v) is the true fibre multiplicity. -/
theorem original_weighted_product_sum_le_moment
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) (F : ℕ → ℝ)
    (hF : ∀ v, 0 ≤ F v) :
    (∑ nm ∈ originalMNCarrier atom,
      (‖atom.alpha nm.1‖ * ‖atom.beta nm.2‖) * F (nm.1 * nm.2)) ≤
        ∑ v ∈ psiMNImage atom, (v.divisors.card : ℝ) ^ (B + 1) * F v := by
  have hmap : ∀ nm ∈ originalMNCarrier atom, nm.1 * nm.2 ∈ psiMNImage atom := by
    intro nm hnm
    exact mem_image_of_mem _ (originalMNCarrier_subset_psiMNCarrier atom hA hnm)
  have hf := sum_fiberwise_of_maps_to (s := originalMNCarrier atom)
    (t := psiMNImage atom) (g := fun nm : ℕ × ℕ => nm.1 * nm.2) hmap
    (fun nm => (‖atom.alpha nm.1‖ * ‖atom.beta nm.2‖) * F (nm.1 * nm.2))
  rw [← hf]
  apply sum_le_sum
  intro v hv
  have hvpos := (psiMNImage_physical_interval hA hv).2.2
  let T := (originalMNCarrier atom).filter (fun nm => nm.1 * nm.2 = v)
  have hsub : T ⊆ (mnCarrier atom).filter (fun nm => nm.1 * nm.2 = v) := by
    intro nm hnm
    have hψ := originalMNCarrier_subset_psiMNCarrier atom hA (mem_filter.mp hnm).1
    exact mem_filter.mpr ⟨(mem_filter.mp hψ).1, (mem_filter.mp hnm).2⟩
  have hcard : (T.card : ℝ) ≤ (v.divisors.card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (mn_fiber_card_le_tau atom v hvpos)
  calc
    _ ≤ ∑ _nm ∈ T, (v.divisors.card : ℝ) ^ B * F v := by
      apply sum_le_sum
      intro nm hnm
      have hp := (mem_filter.mp hnm).2
      rw [hp]
      exact mul_le_mul_of_nonneg_right
        (beta_norm_le_product_divisor_power atom hA (mem_filter.mp hnm).1 hvpos hp) (hF v)
    _ = (T.card : ℝ) * ((v.divisors.card : ℝ) ^ B * F v) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (v.divisors.card : ℝ) * ((v.divisors.card : ℝ) ^ B * F v) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (by positivity) (hF v))
    _ = _ := by rw [pow_succ]; ring

private theorem physicalDeletedKernel_norm_le_count_add_mean (atom : MediumAtom)
    (ell n m : ℕ) :
    ‖physicalDeletedKernel atom n ((ell, 1, 1), m)‖ ≤
      (if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0) +
        1 / (ell.totient : ℝ) := by
  have hd : ‖deletedCongruence atom n ((ell, 1, 1), m)‖ ≤
      if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0 := by
    by_cases he : ((n * m : ℕ) : ℤ) = atom.residue
    · simp only [deletedCongruence, if_pos he, norm_zero]
      split_ifs <;> norm_num
    · simp only [deletedCongruence, if_neg he, fullCongruence,
        complexFactorModulus, mul_one]
      change ‖(if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℂ) else 0)‖ ≤ _
      split_ifs <;> norm_num
  have hm : ‖physicalMeanKernel atom n ((ell, 1, 1), m)‖ ≤ 1 / (ell.totient : ℝ) := by
    simp only [physicalMeanKernel, complexFactorModulus, mul_one, norm_div,
      Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> norm_num
  exact (norm_sub_le _ _).trans (add_le_add hd hm)

/-- The mean is the original coprime mean inside deletedModulusDiscrepancy;
only its norm is enlarged to the q=1 moment. The exact product remains
deleted from the count and is NOT deleted from that mean. -/
theorem original_deletedModulusDiscrepancy_le_divisor_moments
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) (ell : ℕ) :
    ‖deletedModulusDiscrepancy atom ell‖ ≤
      divisorProgressionMoment (B + 1) atom ell +
        divisorProgressionMoment (B + 1) atom 1 / (ell.totient : ℝ) := by
  let F : ℕ → ℝ := fun v =>
    (if Int.ModEq ell (v : ℤ) atom.residue then 1 else 0) + 1 / (ell.totient : ℝ)
  have hF (v : ℕ) : 0 ≤ F v := by dsimp [F]; split_ifs <;> positivity
  calc
    _ ≤ ∑ n ∈ atom.alphaCarrier, ∑ m ∈ atom.betaCarrier,
        ‖atom.alpha n * atom.beta m * physicalDeletedKernel atom n ((ell, 1, 1), m)‖ := by
      apply (norm_sum_le _ _).trans
      exact sum_le_sum (fun n hn => norm_sum_le _ _)
    _ ≤ ∑ nm ∈ originalMNCarrier atom,
        (‖atom.alpha nm.1‖ * ‖atom.beta nm.2‖) * F (nm.1 * nm.2) := by
      rw [originalMNCarrier, sum_product]
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro m hm
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (physicalDeletedKernel_norm_le_count_add_mean atom ell n m) (by positivity)
    _ ≤ ∑ v ∈ psiMNImage atom, (v.divisors.card : ℝ) ^ (B + 1) * F v :=
      original_weighted_product_sum_le_moment atom hA F hF
    _ = _ := by
      rw [divisorProgressionMoment_one]
      unfold F divisorProgressionMoment
      simp only [mul_add, sum_add_distrib, mul_one_div, ← sum_div]
      congr 1
      apply sum_congr rfl
      intro v hv
      split_ifs <;> simp

end
end ImbalancedChen.Part3.OriginalLinearDivisorMoment20261102
