import ImbalancedChen.Part3PolynomialResidueDivisorBound
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Actual large-beta-gcd mass at the original beta length

Pure finite gcd and Cauchy--Schwarz proofs extracted into an isolated
namespace from fixed goldbach 09b97db5764ade1246bfb77206baa1b124760958:
* GcdMean.lean:17-50, source SHA256
  ec6cba59e9db4a2d6cdd9a8596884e56efce6cf0fec342168fddccfa4c2003a2;
* LargeGCDBetaMass.lean:20-119, source SHA256
  241c5e5877ea7acae90a47a53c8d382c09ea6b17104601844e839859d71dc100.
No original unbuilt large-gcd or raw-estimate module is imported.

The actual real coefficient is the norm of the original cleaned complex
beta. Admissibility gives tau_2^B <= tau_(2^B) on the original positive
beta carrier. The endpoint T=2V and the original mask Y<gcd(n1,n2) are
unchanged, including the explicit fixed logarithm exponent (2^B)^2-1.

This pays the clean beta-pair mass in the polynomial-residue raw bound.
The original signed-divisor exception, the other four gcd coordinates,
root and slow phases, and the primitive V/U cancellation remain open.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace ActualLargeGCDBetaMass
theorem gcd_le_divisor_sum {a : ℕ} (ha : a ≠ 0) (n : ℕ) :
    a.gcd n ≤ ∑ d ∈ a.divisors, if d ∣ n then d else 0 := by
  have hg : a.gcd n ∈ a.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left a n, ha⟩
  calc
    a.gcd n = (if a.gcd n ∣ n then a.gcd n else 0) := by
      rw [if_pos (Nat.gcd_dvd_right a n)]
    _ ≤ ∑ d ∈ a.divisors, if d ∣ n then d else 0 :=
      Finset.single_le_sum (f := fun d => if d ∣ n then d else 0)
        (fun _ _ => Nat.zero_le _) hg

theorem sum_divisor_majorant (a N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ d ∈ a.divisors, if d ∣ n then d else 0) =
      ∑ d ∈ a.divisors, d * (N / d) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp [Nat.Ioc_filter_dvd_card_eq_div, Nat.mul_comm]

theorem sum_gcd_le_divisor_floor {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, a.gcd n) ≤ ∑ d ∈ a.divisors, d * (N / d) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ∑ d ∈ a.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum (fun n _ => gcd_le_divisor_sum ha n)
    _ = _ := sum_divisor_majorant a N

theorem sum_gcd_le {a : ℕ} (ha : a ≠ 0) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, a.gcd n) ≤ N * a.divisors.card := by
  calc
    _ ≤ ∑ d ∈ a.divisors, d * (N / d) := sum_gcd_le_divisor_floor ha N
    _ ≤ ∑ _d ∈ a.divisors, N :=
      Finset.sum_le_sum (fun d _ => Nat.mul_div_le N d)
    _ = _ := by simp [Nat.mul_comm]

/-- Ordered pairs of beta indices whose common divisor exceeds a real cutoff. -/
def largeGCDPairs (N : Finset ℕ) (Y : ℝ) : Finset (ℕ × ℕ) :=
  (N ×ˢ N).filter (fun p => Y < (p.1.gcd p.2 : ℝ))

/-- The double gcd mean on any finite subset of the positive interval. -/
theorem sum_gcd_pairs_le_log {T : ℝ} (hT : 1 ≤ T)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) :
    (∑ p ∈ N ×ˢ N, (p.1.gcd p.2 : ℝ)) ≤ T ^ 2 * (1 + Real.log T) := by
  have hT0 : 0 ≤ T := by linarith
  calc
    _ = ∑ n ∈ N, ∑ m ∈ N, (n.gcd m : ℝ) := sum_product _ _ _
    _ ≤ ∑ n ∈ N, T * (fouvryTau 2 n : ℝ) := by
      apply sum_le_sum
      intro n hn
      calc
        _ ≤ ∑ m ∈ Ioc 0 ⌊T⌋₊, (n.gcd m : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)
        _ ≤ (⌊T⌋₊ : ℝ) * (n.divisors.card : ℝ) := by
          exact_mod_cast sum_gcd_le (mem_Ioc.mp (hN hn)).1.ne' ⌊T⌋₊
        _ ≤ T * (n.divisors.card : ℝ) :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hT0) (by positivity)
        _ = _ := by rw [fouvryTau_two]
    _ = T * ∑ n ∈ N, (fouvryTau 2 n : ℝ) := (mul_sum _ _ _).symm
    _ ≤ T * ∑ n ∈ Ioc 0 ⌊T⌋₊, (fouvryTau 2 n : ℝ) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => by positivity)) hT0
    _ ≤ T * (T * (1 + Real.log T)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using sum_fouvryTau_le_real (k := 2) (by norm_num) hT) hT0
    _ = _ := by ring

/-- Markov's inequality for the large common divisor of the beta indices. -/
theorem card_largeGCDPairs_le {T Y : ℝ} (hT : 1 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) :
    ((largeGCDPairs N Y).card : ℝ) ≤ T ^ 2 * (1 + Real.log T) / Y := by
  apply (le_div_iff₀ hY).mpr
  calc
    _ = ∑ _p ∈ largeGCDPairs N Y, Y := by simp
    _ ≤ ∑ p ∈ largeGCDPairs N Y, (p.1.gcd p.2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact (mem_filter.mp hp).2.le
    _ ≤ ∑ p ∈ N ×ˢ N, (p.1.gcd p.2 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := sum_gcd_pairs_le_log hT N hN

/-- Cauchy--Schwarz on any set of ordered pairs pays one coefficient square
sum and the square root of the number of retained pairs. -/
theorem sum_abs_pair_mul_le_sqrt_card {ι : Type*}
    (N : Finset ι) (S : Finset (ι × ι)) (hS : S ⊆ N ×ˢ N) (β : ι → ℝ) :
    (∑ p ∈ S, |β p.1 * β p.2|) ≤
      Real.sqrt (S.card : ℝ) * ∑ n ∈ N, β n ^ 2 := by
  have hsq :
      (∑ p ∈ S, (β p.1 * β p.2) ^ 2) ≤ (∑ n ∈ N, β n ^ 2) ^ 2 := by
    calc
      _ ≤ ∑ p ∈ N ×ˢ N, (β p.1 * β p.2) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
      _ = _ := by
        simp only [sum_product, pow_two, sum_mul_sum]
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro m _
        ring
  calc
    _ ≤ Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ p ∈ S, (β p.1 * β p.2) ^ 2) := by
      simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] using
        Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ)) (fun p => |β p.1 * β p.2|)
    _ ≤ Real.sqrt (S.card : ℝ) * Real.sqrt ((∑ n ∈ N, β n ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_sq (sum_nonneg (fun _ _ => sq_nonneg _))]

/-- Quantitative discarded beta-pair mass with inverse-square-root cutoff
gain, for arbitrary signed fixed-order divisor-bounded coefficients. -/
theorem sum_abs_largeGCDPairs_le {k : ℕ} (hk : 1 ≤ k) {T Y : ℝ}
    (hT : 1 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊) (β : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ)) :
    (∑ p ∈ largeGCDPairs N Y, |β p.1 * β p.2|) ≤
      T ^ 2 * (1 + Real.log T) ^ (k ^ 2 - 1) *
        Real.sqrt ((1 + Real.log T) / Y) := by
  have hT0 : 0 ≤ T := by linarith
  have hcard :
      Real.sqrt ((largeGCDPairs N Y).card : ℝ) ≤
        T * Real.sqrt ((1 + Real.log T) / Y) := by
    calc
      _ ≤ Real.sqrt (T ^ 2 * (1 + Real.log T) / Y) :=
        Real.sqrt_le_sqrt (card_largeGCDPairs_le hT hY N hN)
      _ = _ := by
        rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0]
  calc
    _ ≤ Real.sqrt ((largeGCDPairs N Y).card : ℝ) * ∑ n ∈ N, β n ^ 2 :=
      sum_abs_pair_mul_le_sqrt_card N (largeGCDPairs N Y) (filter_subset _ _) β
    _ ≤ (T * Real.sqrt ((1 + Real.log T) / Y)) *
        (T * (1 + Real.log T) ^ (k ^ 2 - 1)) :=
      mul_le_mul hcard (sum_alpha_sq_le_fouvryTau hk hT N hN β hβ)
        (sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg hT0 (Real.sqrt_nonneg _))
    _ = _ := by ring

end ActualLargeGCDBetaMass

/-- The actual beta interval is positive and has endpoint 2V. -/
theorem MediumAtom.betaCarrier_subset_twiceV {d : MediumAtom} (hV : 1 ≤ d.V) :
    d.betaCarrier ⊆ Ioc 0 (Nat.floor (2 * d.V)) := by
  intro n hn
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hnR : 1 ≤ (n : ℝ) :=
    hV.trans ((Nat.le_ceil d.V).trans (by exact_mod_cast hlo))
  exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast (show (0 : ℝ) < n by linarith), hhi⟩

/-- The real norm of the actual clean complex coefficient has fixed divisor
order 2^B. No squarefree support or new beta bound is assumed. -/
theorem MediumAtom.cleanedBeta_norm_le_tauPow
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {n : ℕ} (hn : n ∈ d.betaCarrier) :
    ‖d.cleanedBeta n‖ ≤ (fouvryTau (2 ^ B) n : ℝ) := by
  have hnpos := (Finset.mem_Ioc.mp (d.betaCarrier_subset_twiceV hd.2.1 hn)).1
  have hb : ‖d.beta n‖ ≤ (n.divisors.card : ℝ) ^ B := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := hd
    exact hb n hn
  calc
    _ ≤ (n.divisors.card : ℝ) ^ B := by
      by_cases hdiv : (n : ℤ) ∣ d.residue
      · simp only [MediumAtom.cleanedBeta, if_pos hdiv, norm_zero]
        positivity
      · simpa only [MediumAtom.cleanedBeta, if_neg hdiv] using hb
    _ = (fouvryTau 2 n : ℝ) ^ B := by rw [fouvryTau_two]
    _ ≤ _ := by exact_mod_cast fouvryTau_pow_le 2 B hnpos.ne'

/-- A real-function application of the genuine large beta-gcd mass estimate
at T=2V. The original threshold, both beta variables and their norms remain. -/
theorem MediumAtom.commonLargeBetaGCDCleanMass_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {Y : ℝ} (hY : 0 < Y) :
    d.commonLargeBetaGCDCleanMass Y ≤
      (2 * d.V) ^ 2 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
        Real.sqrt ((1 + Real.log (2 * d.V)) / Y) := by
  have hbound := ActualLargeGCDBetaMass.sum_abs_largeGCDPairs_le
    (k := 2 ^ B) (by positivity) (show 1 ≤ 2 * d.V by linarith [hd.2.1]) hY
    d.betaCarrier (d.betaCarrier_subset_twiceV hd.2.1) (fun n ↦ ‖d.cleanedBeta n‖)
    (fun n hn ↦ by simpa only [abs_norm] using d.cleanedBeta_norm_le_tauPow hd hn)
  simpa only [MediumAtom.commonLargeBetaGCDCleanMass, ActualLargeGCDBetaMass.largeGCDPairs,
    Finset.sum_filter, Finset.sum_product, abs_mul, abs_norm] using hbound

/-- A proved large-gcd gain for the actual original complex W at polynomially
moving residue. The removed signed-divisor exception stays explicit. -/
theorem commonLargeBetaGCDW_polynomial_residue_largeGCD_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 0 < Y →
        ‖d.commonLargeBetaGCDW Y‖ ≤
          C * d.U * d.scale ^ epsilon *
            ((2 * d.V) ^ 2 * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) *
              Real.sqrt ((1 + Real.log (2 * d.V)) / Y)) +
            ‖d.commonLargeBetaGCDException Y‖ := by
  obtain ⟨C, hC, hbound⟩ := commonLargeBetaGCDW_polynomial_residue_raw_bound kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y hY ↦ ?_⟩
  have hU0 : 0 ≤ d.U := by linarith [hd.1]
  exact (hbound B sigma c0 d hd Y).trans
    (add_le_add (mul_le_mul_of_nonneg_left (d.commonLargeBetaGCDCleanMass_le hd hY)
      (mul_nonneg (mul_nonneg hC.le hU0)
        (Real.rpow_nonneg (by unfold MediumAtom.scale; positivity [hd.2.1]) _))) le_rfl)

end

end ImbalancedChen.Part3
