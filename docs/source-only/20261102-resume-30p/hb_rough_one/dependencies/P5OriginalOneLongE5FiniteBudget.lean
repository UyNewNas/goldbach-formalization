import ImbalancedChen.P5OriginalPrimitiveCoprimeDensity
import ImbalancedChen.P5OriginalOneLongSmoothAbel
import ImbalancedChen.P5OriginalOneLongModulusMeans
import ImbalancedChen.Part3BrunSymmetricPairCount

-- UNCOMPILED_ZERO_CREDIT. Original E5/(6), actual physical coefficient scope.
-- The only unbound finite Brun inputs are B1 and B2 on the literal divisor
-- support. They are common internal algebra suppliers, never E5 hypotheses.

namespace ImbalancedChen
namespace OriginalOneLongE5FiniteBudget

noncomputable section
open Finset
open scoped BigOperators
open OriginalOneLongFiniteBrun OriginalOneLongDivisorIntervals OriginalOneLongSharpBrun
open OriginalPrimitiveCoprimeDensity OriginalOneLongSmoothAbel OriginalOneLongModulusMeans

open Part3.TwoLongActualBrunProfile Part3.TwoLongBrunLiteralDensity
open Part3.BrunFactorialRecurrenceE1 Part3.BrunSymmetricPairCount

def brunEpsilon (j : ℕ) (P : Finset ℕ) : ℝ :=
  chartHarmonic P ^ (2 * j + 1) / (Nat.factorial (2 * j + 1) : ℝ)

-- Reuses the shared B2 pair-count API. Only the literal subset/divisor
-- dictionary equality is still a binding guard; no recurrence or B2 bound
-- is assumed. Nonprimitive m correctly deletes the entire source.
theorem compatibleGapDensity_sharedB2
    (j : ℕ) (P S : Finset ℕ) (g : ℕ → ℝ) (q m : ℕ)
    (hdictionary : compatibleGapDensity S g q m =
      if m.Coprime q then reciprocalUpper j P q - reciprocalLower j P q else 0) :
    compatibleGapDensity S g q m ≤ brunEpsilon j P := by
  rw [hdictionary]
  split_ifs
  · exact reciprocalGap_le_B2_epsilon j P q
  · unfold brunEpsilon chartHarmonic
    positivity

-- Reuses the shared actual B1 profile after the finite literal dictionary.
theorem pointwise_B1_shared
    (j : ℕ) (P S : Finset ℕ) (b g : ℕ → ℝ) (primeProduct n : ℕ)
    (hupper : polynomial S divisorMask b n = (brunUpper j P n : ℝ))
    (hrough : actualRough primeProduct n = (roughIndicator P n : ℝ))
    (hgap : polynomial S divisorMask g n =
      ((smallDivisorCount P n).choose (2 * j + 1) : ℝ)) :
    0 ≤ polynomial S divisorMask b n - actualRough primeProduct n ∧
      polynomial S divisorMask b n - actualRough primeProduct n ≤ polynomial S divisorMask g n := by
  obtain ⟨hr, hu, hg⟩ := brunRealBounds j P n
  rw [hupper, hrough, hgap]
  exact ⟨sub_nonneg.mpr hu, hg⟩

def intervalBudget (Y epsilon : ℝ) (K q : ℕ) : ℝ :=
  (4 + 2 / (q : ℝ) + 4 * tauR q / (q.totient : ℝ)) * Y +
    2 * epsilon * (K : ℝ) / (q : ℝ)

theorem intervalBudget_nonneg (Y epsilon : ℝ) (K q : ℕ)
    (hY : 0 ≤ Y) (he : 0 ≤ epsilon) : 0 ≤ intervalBudget Y epsilon K q := by
  unfold intervalBudget tauR
  positivity

-- Supplies all sharp prefixes from actual B1/B2 and the PROVED primitive
-- Mobius estimate. No primitive coprime-density hypothesis remains here.
theorem actual_prefix_bound
    (L K q a m primeProduct : ℕ) (S : Finset ℕ) (b g : ℕ → ℝ) (Y epsilon : ℝ)
    (hq : 0 < q) (ha : a.Coprime q) (he : 0 ≤ epsilon)
    (hd : ∀ d ∈ S, 0 < d) (hY : (S.card : ℝ) ≤ Y)
    (hb : ∀ d ∈ S, |b d| ≤ 1) (hg : ∀ d ∈ S, 0 ≤ g d ∧ g d ≤ 1)
    (hlo : ∀ n ∈ Ico L (L + K),
      0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ Ico L (L + K), polynomial S divisorMask b n - actualRough primeProduct n ≤
      polynomial S divisorMask g n)
    (hdensity : compatibleGapDensity S g q m ≤ epsilon) :
    ∀ k ≤ K, ‖discrepancy (Ico L (L + k)) (actualCount q a m) (actualMean q m)
      (actualRough primeProduct) (fun _ => 1)‖ ≤ intervalBudget Y epsilon K q := by
  intro k hk
  have hincl : Ico L (L + k) ⊆ Ico L (L + K) := by
    intro n hn
    obtain ⟨hnL, hnU⟩ := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨hnL, by omega⟩
  have hsharp := sharp_one_long_brun_bound L (L + k) q a m primeProduct S b g
    (2 * (q.divisors.card : ℝ)) epsilon (by omega) hq ha hd (by positivity)
    (primitiveCoprimeDensity_two_tau q hq)
    (fun n hn => hlo n (hincl hn)) (fun n hn => hhi n (hincl hn))
    (fun d hdS => (hg d hdS).1) hdensity
  change _ ≤ sharpBound S b g L (L + k) q (2 * (q.divisors.card : ℝ)) epsilon at hsharp
  have hs := sharpBound_le_support S b g L (L + k) q
    (2 * (q.divisors.card : ℝ)) epsilon Y (by positivity) hb
    (fun d hdS => (hg d hdS).2) hY
  have hlen : (k : ℝ) ≤ K := by exact_mod_cast hk
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    _ ≤ _ := hsharp.trans hs
    _ ≤ intervalBudget Y epsilon K q := by
      unfold intervalBudget tauR
      simp only [Nat.add_sub_cancel_left]
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlen (mul_nonneg (by norm_num) he)) hqR.le
      nlinarith

-- Finite physical modulus budget. J is fixed and R is the physical polylog
-- coefficient envelope. Every tau/totient loss is paid by an ACTUAL mean.
theorem physical_intervalBudget_sum
    (Q : Finset ℕ) (D J K : ℕ) (rho : ℕ → ℂ) (Y epsilon R : ℝ)
    (hD : 1 ≤ D) (hQ : Q ⊆ Ioc 0 D) (hY : 0 ≤ Y) (he : 0 ≤ epsilon)
    (hR : 0 ≤ R) (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R * tauR q ^ J) :
    (∑ q ∈ Q, ‖rho q‖ * intervalBudget Y epsilon K q) ≤
      Y * (4 * R * (D : ℝ) * logBudget D ^ (2 ^ J - 1) +
        2 * R * logBudget D ^ (2 ^ J) +
        4 * R * logBudget D ^ (2 * 2 ^ (J + 1))) +
      2 * epsilon * (K : ℝ) * R * logBudget D ^ (2 ^ J) := by
  obtain ⟨hplain, hrecip, htotient⟩ := physical_rho_moments Q D J R rho hD hR hQ hrho
  have hexpand : (∑ q ∈ Q, ‖rho q‖ * intervalBudget Y epsilon K q) =
      Y * (4 * (∑ q ∈ Q, ‖rho q‖) + 2 * (∑ q ∈ Q, ‖rho q‖ / (q : ℝ)) +
        4 * (∑ q ∈ Q, ‖rho q‖ * tauR q / (q.totient : ℝ))) +
      2 * epsilon * (K : ℝ) * (∑ q ∈ Q, ‖rho q‖ / (q : ℝ)) := by
    rw [mul_add, mul_add]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    unfold intervalBudget
    ring
  rw [hexpand]
  have hmain := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hplain (by norm_num : (0 : ℝ) ≤ 4))
      (mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left htotient (by norm_num : (0 : ℝ) ≤ 4))
  have hgap := mul_le_mul_of_nonneg_left hrecip
    (by positivity : 0 ≤ 2 * epsilon * (K : ℝ))
  have h := add_le_add (mul_le_mul_of_nonneg_left hmain hY) hgap
  nlinarith

def profileError (L K q a m primeProduct : ℕ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ j ∈ range K, F (((L + j : ℕ) : ℝ) / u) *
    actualCoefficient q a m primeProduct (L + j)

-- The actual normalized complex long profile, including its admitted
-- logarithm/twist norm, now follows without a rough-smooth theorem input.
theorem actual_profile_bound
    (L K q a m primeProduct : ℕ) (S : Finset ℕ) (b g : ℕ → ℝ)
    (F : ℝ → ℂ) (u A B Rwidth Y epsilon : ℝ)
    (hq : 0 < q) (ha : a.Coprime q) (he : 0 ≤ epsilon)
    (hd : ∀ d ∈ S, 0 < d) (hY : (S.card : ℝ) ≤ Y)
    (hb : ∀ d ∈ S, |b d| ≤ 1) (hg : ∀ d ∈ S, 0 ≤ g d ∧ g d ≤ 1)
    (hlo : ∀ n ∈ Ico L (L + K),
      0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ Ico L (L + K), polynomial S divisorMask b n - actualRough primeProduct n ≤
      polynomial S divisorMask g n)
    (hdensity : compatibleGapDensity S g q m ≤ epsilon)
    (hu : 0 < u) (hB : 0 ≤ B) (hF : Differentiable ℝ F)
    (hamplitude : ∀ x : ℝ, ‖F x‖ ≤ A) (hderiv : ∀ x : ℝ, ‖deriv F x‖ ≤ B)
    (hwidth : (K : ℝ) ≤ Rwidth * u) :
    ‖profileError L K q a m primeProduct F u‖ ≤ intervalBudget Y epsilon K q * (A + Rwidth * B) := by
  have hY0 : 0 ≤ Y := (Nat.cast_nonneg S.card).trans hY
  exact smooth_actual_one_long_of_sharp_prefix L K q a m primeProduct F u A B Rwidth
    (intervalBudget Y epsilon K q) hu hB (intervalBudget_nonneg Y epsilon K q hY0 he)
    hF hamplitude hderiv hwidth
    (actual_prefix_bound L K q a m primeProduct S b g Y epsilon hq ha he hd hY hb hg hlo hhi hdensity)

def physicalBudget (D J K : ℕ) (Y epsilon R : ℝ) : ℝ :=
  Y * (4 * R * (D : ℝ) * logBudget D ^ (2 ^ J - 1) +
    2 * R * logBudget D ^ (2 ^ J) +
    4 * R * logBudget D ^ (2 * 2 ^ (J + 1))) +
  2 * epsilon * (K : ℝ) * R * logBudget D ^ (2 ^ J)

-- Finite E5 for the actual physical coefficient class and complex profiles.
-- No rough branch estimate is an input: B1/B2, fixed norms and physical
-- coefficient envelopes are the only data. All arithmetic filters are literal.
theorem full_one_long_E5_finite
    (L K a primeProduct D J : ℕ) (Q Mset S : Finset ℕ)
    (rho alpha : ℕ → ℂ) (b g : ℕ → ℝ) (F : ℝ → ℂ)
    (u A B Rwidth Y epsilon Rrho M : ℝ)
    (hD : 1 ≤ D) (hQ : Q ⊆ Ioc 0 D) (ha : ∀ q ∈ Q, a.Coprime q)
    (he : 0 ≤ epsilon) (hRrho : 0 ≤ Rrho)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ Rrho * tauR q ^ J)
    (hM : (∑ m ∈ Mset, ‖alpha m‖) ≤ M)
    (hd : ∀ d ∈ S, 0 < d) (hY : (S.card : ℝ) ≤ Y)
    (hb : ∀ d ∈ S, |b d| ≤ 1) (hg : ∀ d ∈ S, 0 ≤ g d ∧ g d ≤ 1)
    (hlo : ∀ n ∈ Ico L (L + K),
      0 ≤ polynomial S divisorMask b n - actualRough primeProduct n)
    (hhi : ∀ n ∈ Ico L (L + K), polynomial S divisorMask b n - actualRough primeProduct n ≤
      polynomial S divisorMask g n)
    (hdensity : ∀ q ∈ Q, ∀ m ∈ Mset, compatibleGapDensity S g q m ≤ epsilon)
    (hu : 0 < u) (hA : 0 ≤ A) (hB : 0 ≤ B) (hRwidth : 0 ≤ Rwidth)
    (hF : Differentiable ℝ F) (hamplitude : ∀ x : ℝ, ‖F x‖ ≤ A)
    (hderiv : ∀ x : ℝ, ‖deriv F x‖ ≤ B) (hwidth : (K : ℝ) ≤ Rwidth * u) :
    ‖∑ q ∈ Q, rho q * ∑ m ∈ Mset, alpha m * profileError L K q a m primeProduct F u‖ ≤
      M * (A + Rwidth * B) * physicalBudget D J K Y epsilon Rrho := by
  have hY0 : 0 ≤ Y := (Nat.cast_nonneg S.card).trans hY
  have hM0 : 0 ≤ M := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hM
  have hV : 0 ≤ A + Rwidth * B := by positivity
  have hpoint (q : ℕ) (hqQ : q ∈ Q) (m : ℕ) (hm : m ∈ Mset) :
      ‖profileError L K q a m primeProduct F u‖ ≤
        intervalBudget Y epsilon K q * (A + Rwidth * B) := by
    exact actual_profile_bound L K q a m primeProduct S b g F u A B Rwidth Y epsilon
      (mem_Ioc.mp (hQ hqQ)).1 (ha q hqQ) he hd hY hb hg hlo hhi
      (hdensity q hqQ m hm) hu hB hF hamplitude hderiv hwidth
  have hinner (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ Mset, alpha m * profileError L K q a m primeProduct F u‖ ≤
        M * (intervalBudget Y epsilon K q * (A + Rwidth * B)) := by
    calc
      _ ≤ ∑ m ∈ Mset, ‖alpha m * profileError L K q a m primeProduct F u‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Mset, ‖alpha m‖ * (intervalBudget Y epsilon K q * (A + Rwidth * B)) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpoint q hqQ m hm) (norm_nonneg _)
      _ = (∑ m ∈ Mset, ‖alpha m‖) *
          (intervalBudget Y epsilon K q * (A + Rwidth * B)) := by rw [← Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hM
        (mul_nonneg (intervalBudget_nonneg Y epsilon K q hY0 he) hV)
  have hphysical := physical_intervalBudget_sum Q D J K rho Y epsilon Rrho
    hD hQ hY0 he hRrho hrho
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ m ∈ Mset, alpha m * profileError L K q a m primeProduct F u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * (M * (intervalBudget Y epsilon K q * (A + Rwidth * B))) := by
      apply Finset.sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hinner q hqQ) (norm_nonneg _)
    _ = M * (A + Rwidth * B) * ∑ q ∈ Q, ‖rho q‖ * intervalBudget Y epsilon K q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hqQ
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hphysical (mul_nonneg hM0 hV)

end
end OriginalOneLongE5FiniteBudget
end ImbalancedChen
