import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

-- UNCOMPILED_ZERO_CREDIT. No compiler or formal checker was run.
-- Original: distribution-prime-product-completion-20261010, sections 7--8,
-- equations (E1), (E3) with one variable, and (E5).
-- Independent derivation: direct-brun-long-branches-root-20261010, section 3.
-- This is the finite reduction, not a claim that all analytic inputs are bound.

namespace ImbalancedChen
namespace OriginalOneLongFiniteBrun

noncomputable section
open scoped BigOperators
open Finset

-- N is the finite long interval. In the manuscript application,
-- A d n = 1_(d divides n), C n = 1_(m*n = a mod q), and
-- P n = 1_((m*n,q)=1)/phi(q). Thus P is the EXACT coprime mean.
-- Keeping C and P distinct also retains every nonprimitive vanishing term.
def atom {ι δ : Type*} (N : Finset ι) (A : δ → ι → ℝ)
    (C P : ι → ℝ) (f : ι → ℂ) (d : δ) : ℂ :=
  ∑ n ∈ N, f n * ((A d n * (C n - P n) : ℝ) : ℂ)

def discrepancy {ι : Type*} (N : Finset ι) (C P r : ι → ℝ)
    (f : ι → ℂ) : ℂ :=
  ∑ n ∈ N, f n * ((r n * (C n - P n) : ℝ) : ℂ)

def polynomial {ι δ : Type*} (S : Finset δ) (A : δ → ι → ℝ)
    (b : δ → ℝ) (n : ι) : ℝ := ∑ d ∈ S, b d * A d n

-- Primitive progression and coprime estimates cancel the SAME main term.
-- They are not an assumed rough-long discrepancy estimate.
theorem primitive_main_terms_cancel (count mean main : ℂ) (ec ep : ℝ)
    (hc : ‖count - main‖ ≤ ec) (hp : ‖mean - main‖ ≤ ep) :
    ‖count - mean‖ ≤ ec + ep := by
  calc
    ‖count - mean‖ = ‖(count - main) - (mean - main)‖ := by congr 1; ring
    _ ≤ ‖count - main‖ + ‖mean - main‖ := norm_sub_le _ _
    _ ≤ ec + ep := add_le_add hc hp

-- This exact identity records finite support, with no growing divisor moment.
theorem discrepancy_polynomial {ι δ : Type*} (N : Finset ι) (S : Finset δ)
    (A : δ → ι → ℝ) (C P : ι → ℝ) (f : ι → ℂ) (b : δ → ℝ) :
    discrepancy N C P (polynomial S A b) f =
      ∑ d ∈ S, (b d : ℂ) * atom N A C P f d := by
  classical
  unfold discrepancy polynomial atom
  simp_rw [Finset.sum_mul, Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  ring

theorem expanded_discrepancy_bound {ι δ : Type*}
    (N : Finset ι) (S : Finset δ) (A : δ → ι → ℝ)
    (C P : ι → ℝ) (f : ι → ℂ) (b e : δ → ℝ)
    (he : ∀ d ∈ S, ‖atom N A C P f d‖ ≤ e d) :
    ‖discrepancy N C P (polynomial S A b) f‖ ≤
      ∑ d ∈ S, |b d| * e d := by
  rw [discrepancy_polynomial]
  calc
    _ ≤ ∑ d ∈ S, ‖(b d : ℂ) * atom N A C P f d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ S, |b d| * e d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (he d hd) (abs_nonneg _)

-- Complex profiles are bounded only by nonnegative majorants. No ordering
-- of complex coefficients or positivity of the lower Brun polynomial is used.
theorem rough_to_upper {ι : Type*} (N : Finset ι)
    (C P r U G F : ι → ℝ) (f : ι → ℂ)
    (hC : ∀ n ∈ N, 0 ≤ C n) (hP : ∀ n ∈ N, 0 ≤ P n)
    (hF : ∀ n ∈ N, ‖f n‖ ≤ F n)
    (hlo : ∀ n ∈ N, 0 ≤ U n - r n)
    (hhi : ∀ n ∈ N, U n - r n ≤ G n) :
    ‖discrepancy N C P r f‖ ≤ ‖discrepancy N C P U f‖ +
      ∑ n ∈ N, F n * G n * (C n + P n) := by
  have hdiff : discrepancy N C P r f - discrepancy N C P U f =
      ∑ n ∈ N, f n * (((r n - U n) * (C n - P n) : ℝ) : ℂ) := by
    unfold discrepancy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  have hnorm : ‖discrepancy N C P r f - discrepancy N C P U f‖ ≤
      ∑ n ∈ N, F n * G n * (C n + P n) := by
    rw [hdiff]
    calc
      _ ≤ ∑ n ∈ N, ‖f n * (((r n - U n) * (C n - P n) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ N, F n * G n * (C n + P n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hFn : 0 ≤ F n := (norm_nonneg _).trans (hF n hn)
        have hGn : 0 ≤ G n := (hlo n hn).trans (hhi n hn)
        have habs : |r n - U n| ≤ G n := by
          rw [abs_sub_comm, abs_of_nonneg (hlo n hn)]
          exact hhi n hn
        have hcp : |C n - P n| ≤ C n + P n := by
          rw [abs_le]
          constructor <;> linarith [hC n hn, hP n hn]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        calc
          _ ≤ F n * (G n * (C n + P n)) :=
            mul_le_mul (hF n hn)
              (mul_le_mul habs hcp (abs_nonneg _) hGn)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hFn
          _ = _ := by ring
  have htri := norm_add_le (discrepancy N C P U f)
    (discrepancy N C P r f - discrepancy N C P U f)
  have hid : discrepancy N C P U f +
      (discrepancy N C P r f - discrepancy N C P U f) =
      discrepancy N C P r f := by ring
  rw [hid] at htri
  exact htri.trans (add_le_add_left hnorm _)

-- The positive gap is expanded by its finite coefficients. Its count and
-- exact mean are each bounded from primitive interval estimates, not from
-- a rough distribution conclusion. The common main mass is mass d.
theorem gap_count_mean_bound {ι δ : Type*}
    (N : Finset ι) (S : Finset δ) (A : δ → ι → ℝ)
    (C P F : ι → ℝ) (g mass ec ep : δ → ℝ)
    (hg : ∀ d ∈ S, 0 ≤ g d)
    (hc : ∀ d ∈ S,
      (∑ n ∈ N, F n * A d n * C n) ≤ mass d + ec d)
    (hp : ∀ d ∈ S,
      (∑ n ∈ N, F n * A d n * P n) ≤ mass d + ep d) :
    (∑ n ∈ N, F n * polynomial S A g n * (C n + P n)) ≤
      ∑ d ∈ S, g d * (2 * mass d + ec d + ep d) := by
  classical
  have hexpand : (∑ n ∈ N, F n * polynomial S A g n * (C n + P n)) =
      ∑ d ∈ S, g d * ((∑ n ∈ N, F n * A d n * C n) +
        (∑ n ∈ N, F n * A d n * P n)) := by
    unfold polynomial
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hexpand]
  apply Finset.sum_le_sum
  intro d hd
  apply mul_le_mul_of_nonneg_left _ (hg d hd)
  linarith [hc d hd, hp d hd]

-- Quantitative one-long Brun reduction: this is the new internal implication.
-- b is lambda-plus. g is lambda-plus minus lambda-minus (nonnegative at the
-- single odd Brun layer). Both are supported on the displayed FINITE S.
-- B1 supplies hlo/hhi; B2 and the primitive coprime mean supply mass.
-- The theorem assumes neither (E5) nor any rough branch estimate.
theorem one_long_finite_reduction {ι δ : Type*}
    (N : Finset ι) (S : Finset δ) (A : δ → ι → ℝ)
    (C P r F : ι → ℝ) (f : ι → ℂ)
    (b g mass e ec ep : δ → ℝ)
    (hC : ∀ n ∈ N, 0 ≤ C n) (hP : ∀ n ∈ N, 0 ≤ P n)
    (hF : ∀ n ∈ N, ‖f n‖ ≤ F n)
    (hlo : ∀ n ∈ N, 0 ≤ polynomial S A b n - r n)
    (hhi : ∀ n ∈ N, polynomial S A b n - r n ≤ polynomial S A g n)
    (hg : ∀ d ∈ S, 0 ≤ g d)
    (he : ∀ d ∈ S, ‖atom N A C P f d‖ ≤ e d)
    (hc : ∀ d ∈ S,
      (∑ n ∈ N, F n * A d n * C n) ≤ mass d + ec d)
    (hp : ∀ d ∈ S,
      (∑ n ∈ N, F n * A d n * P n) ≤ mass d + ep d) :
    ‖discrepancy N C P r f‖ ≤
      (∑ d ∈ S, |b d| * e d) +
      ∑ d ∈ S, g d * (2 * mass d + ec d + ep d) := by
  exact (rough_to_upper N C P r (polynomial S A b) (polynomial S A g)
    F f hC hP hF hlo hhi).trans
    (add_le_add (expanded_discrepancy_bound N S A C P f b e he)
      (gap_count_mean_bound N S A C P F g mass ec ep hg hc hp))

-- Every growth cost is the L1 norm on the ACTUAL divisor support. For the
-- explicit Brun weights, |b| <= 1 and 0 <= g <= 1, giving a support-cardinal
-- cost <= y, regardless of the Brun order. No tau(n)^h occurs.
theorem support_l1_le_card {δ : Type*} (S : Finset δ) (b : δ → ℝ)
    (hb : ∀ d ∈ S, |b d| ≤ 1) :
    (∑ d ∈ S, |b d|) ≤ (S.card : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ S, (1 : ℝ) := Finset.sum_le_sum hb
    _ = (S.card : ℝ) := by simp

-- A quantitative support corollary. This is the finite shape behind E5:
-- support-size times primitive error, plus the small Brun-density gap.
theorem finite_cost_bound {δ : Type*} (S : Finset δ)
    (b g mass e ec ep : δ → ℝ) (E gap : ℝ)
    (hE : 0 ≤ E)
    (hb : ∀ d ∈ S, |b d| ≤ 1)
    (hg : ∀ d ∈ S, 0 ≤ g d ∧ g d ≤ 1)
    (he : ∀ d ∈ S, e d ≤ E)
    (herr : ∀ d ∈ S, ec d + ep d ≤ E)
    (hgap : (∑ d ∈ S, g d * mass d) ≤ gap) :
    (∑ d ∈ S, |b d| * e d) +
      (∑ d ∈ S, g d * (2 * mass d + ec d + ep d)) ≤
      2 * (S.card : ℝ) * E + 2 * gap := by
  have hfirst : (∑ d ∈ S, |b d| * e d) ≤ (S.card : ℝ) * E := by
    calc
      _ ≤ ∑ _d ∈ S, E := by
        apply Finset.sum_le_sum
        intro d hd
        exact (mul_le_mul_of_nonneg_left (he d hd) (abs_nonneg _)).trans
          (by nlinarith [hb d hd])
      _ = _ := by simp
  have hlast : (∑ d ∈ S, g d * (ec d + ep d)) ≤ (S.card : ℝ) * E := by
    calc
      _ ≤ ∑ _d ∈ S, E := by
        apply Finset.sum_le_sum
        intro d hd
        exact (mul_le_mul_of_nonneg_left (herr d hd) (hg d hd).1).trans
          (by nlinarith [(hg d hd).2])
      _ = _ := by simp
  have hsplit : (∑ d ∈ S, g d * (2 * mass d + ec d + ep d)) =
      2 * (∑ d ∈ S, g d * mass d) +
        (∑ d ∈ S, g d * (ec d + ep d)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hsplit]
  linarith

def actualCount (q a m n : ℕ) : ℝ := if m * n ≡ a [MOD q] then 1 else 0

def actualMean (q m n : ℕ) : ℝ :=
  if (m * n).Coprime q then 1 / (q.totient : ℝ) else 0

def divisorMask (d n : ℕ) : ℝ := if d ∣ n then 1 else 0

def actualRough (primeProduct n : ℕ) : ℝ :=
  if n.Coprime primeProduct then 1 else 0

-- Concrete binding to the manuscript count and its exact coprime source.
-- The primitive hypotheses below concern each individual inserted divisor,
-- not the complete rough sum on the left of the conclusion.
theorem actual_one_long_finite_reduction
    (N S : Finset ℕ) (q a m primeProduct : ℕ)
    (F : ℕ → ℝ) (f : ℕ → ℂ) (b g mass e ec ep : ℕ → ℝ)
    (hF : ∀ n ∈ N, ‖f n‖ ≤ F n)
    (hlo : ∀ n ∈ N, 0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ N, polynomial S divisorMask b n - actualRough primeProduct n ≤
      polynomial S divisorMask g n)
    (hg : ∀ d ∈ S, 0 ≤ g d)
    (he : ∀ d ∈ S,
      ‖atom N divisorMask (actualCount q a m) (actualMean q m) f d‖ ≤ e d)
    (hc : ∀ d ∈ S, (∑ n ∈ N, F n * divisorMask d n * actualCount q a m n) ≤
      mass d + ec d)
    (hp : ∀ d ∈ S, (∑ n ∈ N, F n * divisorMask d n * actualMean q m n) ≤
      mass d + ep d) :
    ‖discrepancy N (actualCount q a m) (actualMean q m) (actualRough primeProduct) f‖ ≤
      (∑ d ∈ S, |b d| * e d) +
        ∑ d ∈ S, g d * (2 * mass d + ec d + ep d) := by
  apply one_long_finite_reduction N S divisorMask (actualCount q a m)
    (actualMean q m) (actualRough primeProduct) F f b g mass e ec ep
  · intro n hn
    unfold actualCount
    split_ifs <;> norm_num
  · intro n hn
    unfold actualMean
    split_ifs
    · positivity
    · norm_num
  · exact hF
  · exact hlo
  · exact hhi
  · exact hg
  · exact he
  · exact hc
  · exact hp

-- Uniformity is literal: none of these finite constants depends on a residue,
-- scale, short factor, or interval endpoint. Insert their primitive estimates
-- before restoring the short/modulus L1 sums. This module does not establish
-- B1, B2, the smooth partial-summation bridge, or logarithmic divisor means.

end
end OriginalOneLongFiniteBrun
end ImbalancedChen
