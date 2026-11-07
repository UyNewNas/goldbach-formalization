import ImbalancedChen.P5OriginalOneLongFiniteBrunReduction
import ImbalancedChen.P5OriginalOneLongDivisorIntervals

-- UNCOMPILED_ZERO_CREDIT. Exact guarded draft dependencies are in REGISTRY.
-- This is the actual sharp integer-interval one-long Brun implication.
-- The B1/B2 finite algebra inputs are explicit and are not the target estimate.

namespace ImbalancedChen
namespace OriginalOneLongSharpBrun

noncomputable section
open scoped BigOperators
open Finset
open OriginalOneLongFiniteBrun OriginalOneLongDivisorIntervals

theorem actual_count_atom_eq (L U q a m d : ℕ) :
    (∑ n ∈ Ico L U, (1 : ℝ) * divisorMask d n * actualCount q a m n) =
      divisorAPMass L U q a m d := by
  unfold divisorAPMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : d ∣ n <;> simp [divisorMask, actualCount, h]

theorem actual_mean_atom_eq (L U q m d : ℕ) :
    (∑ n ∈ Ico L U, (1 : ℝ) * divisorMask d n * actualMean q m n) =
      divisorCoprimeMass L U q m d := by
  unfold divisorCoprimeMass
  rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : d ∣ n <;> by_cases hc : (m * n).Coprime q <;>
    simp [divisorMask, actualMean, h, hc, div_eq_mul_inv]

theorem actual_discrepancy_atom_eq (L U q a m d : ℕ) :
    atom (Ico L U) divisorMask (actualCount q a m) (actualMean q m) (fun _ => 1) d =
      (divisorRemainder L U q a m d : ℂ) := by
  unfold atom
  simp only [one_mul]
  rw [← Complex.ofReal_sum]
  congr 1
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hc := actual_count_atom_eq L U q a m d
  have hp := actual_mean_atom_eq L U q m d
  simp only [one_mul] at hc hp
  rw [hc, hp]
  rfl

-- This is B2's precise arithmetic density after deleting all q-primes.
-- For unit m it is the usual sum_((d,q)=1) g(d)/d; for nonunit m it is zero.
def compatibleGapDensity (S : Finset ℕ) (g : ℕ → ℝ) (q m : ℕ) : ℝ :=
  ∑ d ∈ S, if (m * d).Coprime q then g d / (d : ℝ) else 0

theorem gap_main_eq (S : Finset ℕ) (g : ℕ → ℝ) (L U q m : ℕ)
    (hq : 0 < q) (hd : ∀ d ∈ S, 0 < d) :
    (∑ d ∈ S, g d * atomMain L U q m d) =
      (((U - L : ℕ) : ℝ) / (q : ℝ)) * compatibleGapDensity S g q m := by
  unfold compatibleGapDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hdS
  by_cases hc : (m * d).Coprime q
  · simp only [atomMain, if_pos hc]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (hd d hdS).ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    field_simp [hdR, hqR]
    ring
  · simp [atomMain, hc]

-- Uniform sharp E5 precursor with explicit constants, exact coprime mean,
-- literal finite divisor support and arbitrary primitive moving residue.
-- B1 supplies hlo/hhi. B2 supplies hdensity, NOT a distribution estimate.
-- The only primitive classical counting boundary is hprimitive, explicitly
-- quantified at every integer interval and independent of all Brun data.
theorem sharp_one_long_brun_bound
    (L U q a m primeProduct : ℕ) (S : Finset ℕ) (b g : ℕ → ℝ)
    (Tq epsilon : ℝ) (hLU : L ≤ U) (hq : 0 < q) (ha : a.Coprime q)
    (hd : ∀ d ∈ S, 0 < d) (hT : 0 ≤ Tq)
    (hprimitive : PrimitiveCoprimeDensity q Tq)
    (hlo : ∀ n ∈ Ico L U,
      0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ Ico L U,
      polynomial S divisorMask b n - actualRough primeProduct n ≤ polynomial S divisorMask g n)
    (hg : ∀ d ∈ S, 0 ≤ g d)
    (hdensity : compatibleGapDensity S g q m ≤ epsilon) :
    ‖discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
      (actualRough primeProduct) (fun _ => 1)‖ ≤
      2 * (∑ d ∈ S, |b d|) +
        2 * (((U - L : ℕ) : ℝ) / (q : ℝ)) * epsilon +
        2 * (meanError q Tq + 1) * (∑ d ∈ S, g d) := by
  have he (d : ℕ) (hdS : d ∈ S) :
      ‖atom (Ico L U) divisorMask (actualCount q a m) (actualMean q m) (fun _ => 1) d‖ ≤
        (2 : ℝ) := by
    rw [actual_discrepancy_atom_eq, Complex.norm_real, Real.norm_eq_abs]
    exact divisorRemainder_abs_le_two L U q a m d (hd d hdS) hq ha
  have hc (d : ℕ) (hdS : d ∈ S) :
      (∑ n ∈ Ico L U, (1 : ℝ) * divisorMask d n * actualCount q a m n) ≤
        atomMain L U q m d + (meanError q Tq + 2) := by
    rw [actual_count_atom_eq]
    exact divisorAPMass_le_main L U q a m d Tq hLU (hd d hdS) hq ha hT hprimitive
  have hp (d : ℕ) (hdS : d ∈ S) :
      (∑ n ∈ Ico L U, (1 : ℝ) * divisorMask d n * actualMean q m n) ≤
        atomMain L U q m d + meanError q Tq := by
    rw [actual_mean_atom_eq]
    exact divisorCoprimeMass_le_main L U q m d Tq hLU (hd d hdS) hq hT hprimitive
  have hfinite := actual_one_long_finite_reduction (Ico L U) S q a m primeProduct
    (fun _ => 1) (fun _ => 1) b g (atomMain L U q m) (fun _ => 2)
    (fun _ => meanError q Tq + 2) (fun _ => meanError q Tq)
    (by intro n hn; simp) hlo hhi hg he hc hp
  have hsplit :
      (∑ d ∈ S, g d * (2 * atomMain L U q m d + (meanError q Tq + 2) + meanError q Tq)) =
        2 * (∑ d ∈ S, g d * atomMain L U q m d) +
          2 * (meanError q Tq + 1) * (∑ d ∈ S, g d) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hdS
    ring
  have hfirst : (∑ d ∈ S, |b d| * (2 : ℝ)) = 2 * ∑ d ∈ S, |b d| := by
    rw [← Finset.sum_mul]
    ring
  rw [hfirst, hsplit, gap_main_eq S g L U q m hq hd] at hfinite
  have hlength : 0 ≤ ((U - L : ℕ) : ℝ) / (q : ℝ) := by positivity
  have hgap := mul_le_mul_of_nonneg_left hdensity (by positivity :
    0 ≤ 2 * (((U - L : ℕ) : ℝ) / (q : ℝ)))
  nlinarith

def sharpBound (S : Finset ℕ) (b g : ℕ → ℝ)
    (L U q : ℕ) (Tq epsilon : ℝ) : ℝ :=
  2 * (∑ d ∈ S, |b d|) +
    2 * (((U - L : ℕ) : ℝ) / (q : ℝ)) * epsilon +
    2 * (meanError q Tq + 1) * (∑ d ∈ S, g d)

theorem positive_support_card_le (S : Finset ℕ) (Y : ℕ)
    (hd : ∀ d ∈ S, 0 < d) (hY : ∀ d ∈ S, d ≤ Y) : S.card ≤ Y := by
  have hs : S ⊆ Icc 1 Y := by
    intro d hdS
    exact mem_Icc.mpr ⟨hd d hdS, hY d hdS⟩
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs

theorem sharpBound_le_support (S : Finset ℕ) (b g : ℕ → ℝ)
    (L U q : ℕ) (Tq epsilon Y : ℝ) (hT : 0 ≤ Tq)
    (hb : ∀ d ∈ S, |b d| ≤ 1) (hg : ∀ d ∈ S, g d ≤ 1)
    (hY : (S.card : ℝ) ≤ Y) :
    sharpBound S b g L U q Tq epsilon ≤
      (4 + 2 / (q : ℝ) + 2 * Tq / (q.totient : ℝ)) * Y +
        2 * epsilon * (((U - L : ℕ) : ℝ) / (q : ℝ)) := by
  have hbS : (∑ d ∈ S, |b d|) ≤ Y :=
    (support_l1_le_card S b hb).trans hY
  have hgS : (∑ d ∈ S, g d) ≤ Y := by
    calc
      _ ≤ ∑ _d ∈ S, (1 : ℝ) := Finset.sum_le_sum hg
      _ = (S.card : ℝ) := by simp
      _ ≤ Y := hY
  have he0 : 0 ≤ meanError q Tq := meanError_nonneg q Tq hT
  unfold sharpBound
  calc
    _ ≤ 2 * Y + 2 * (((U - L : ℕ) : ℝ) / (q : ℝ)) * epsilon +
        2 * (meanError q Tq + 1) * Y := by
      exact add_le_add
        (add_le_add_right (mul_le_mul_of_nonneg_left hbS (by norm_num)) _)
        (mul_le_mul_of_nonneg_left hgS (by positivity))
    _ = _ := by unfold meanError; ring

-- Restoration of the actual complex short coefficients and modulus weights.
-- Primitive a and every actual product m*n remain inside the discrepancy.
theorem full_sharp_one_long_bound
    (L U a primeProduct : ℕ) (Q M S : Finset ℕ)
    (rho alpha : ℕ → ℂ) (b g : ℕ → ℝ) (T : ℕ → ℝ) (epsilon : ℝ)
    (hLU : L ≤ U) (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q)
    (hd : ∀ d ∈ S, 0 < d) (hT : ∀ q ∈ Q, 0 ≤ T q)
    (hprimitive : ∀ q ∈ Q, PrimitiveCoprimeDensity q (T q))
    (hlo : ∀ n ∈ Ico L U,
      0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ Ico L U,
      polynomial S divisorMask b n - actualRough primeProduct n ≤ polynomial S divisorMask g n)
    (hg : ∀ d ∈ S, 0 ≤ g d)
    (hdensity : ∀ q ∈ Q, ∀ m ∈ M, compatibleGapDensity S g q m ≤ epsilon) :
    ‖∑ q ∈ Q, rho q * ∑ m ∈ M, alpha m *
      discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ ≤
      (∑ m ∈ M, ‖alpha m‖) *
        ∑ q ∈ Q, ‖rho q‖ * sharpBound S b g L U q (T q) epsilon := by
  have hpoint (q : ℕ) (hqQ : q ∈ Q) (m : ℕ) (hmM : m ∈ M) :
      ‖discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ ≤ sharpBound S b g L U q (T q) epsilon := by
    exact sharp_one_long_brun_bound L U q a m primeProduct S b g (T q) epsilon
      hLU (hq q hqQ) (ha q hqQ) hd (hT q hqQ) (hprimitive q hqQ)
      hlo hhi hg (hdensity q hqQ m hmM)
  have hshort (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ M, alpha m * discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ ≤
      (∑ m ∈ M, ‖alpha m‖) * sharpBound S b g L U q (T q) epsilon := by
    calc
      _ ≤ ∑ m ∈ M, ‖alpha m * discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ M, ‖alpha m‖ * sharpBound S b g L U q (T q) epsilon := by
        apply Finset.sum_le_sum
        intro m hmM
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpoint q hqQ m hmM) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ m ∈ M, alpha m *
      discrepancy (Ico L U) (actualCount q a m) (actualMean q m)
        (actualRough primeProduct) (fun _ => 1)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ((∑ m ∈ M, ‖alpha m‖) *
        sharpBound S b g L U q (T q) epsilon) := by
      apply Finset.sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hshort q hqQ) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hqQ
      ring

-- Under the actual coefficient bounds and card(S)<=y, this is the familiar
-- y*(4+2/q+2*Tq/phi(q)) + 2*epsilon*length/q finite E5 error.
-- Summing it against |alpha_m rho_q| uses only their stated finite L1 masses
-- and the fixed-order divisor/totient means; those analytic bindings are separate.

end
end OriginalOneLongSharpBrun
end ImbalancedChen
