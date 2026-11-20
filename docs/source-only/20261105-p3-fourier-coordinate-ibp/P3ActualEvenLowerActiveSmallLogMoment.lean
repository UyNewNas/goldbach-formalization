import ImbalancedChen.P3ActualEvenLowerActivePairPrimeMoment
import ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
import ImbalancedChen.P3ActualEvenLowerEulerMass
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3(T),4(F).

The preceding exact signed active-pair identity leaves the genuine strict
small Rosser first prime-divisor moment unpaid. This file pays its finite
moment using a LOGARITHMIC factor, not the size of the displayed small
presieving support. The first-exit LOWER sign choice, strict s<L,
original even-retained rough source, full physical modulus b*s*r and
the same integer rho remain untouched.

The outer rough Euler mass is STILL a finite, parameter-dependent
expression; no uniform log^E(N), nonzero-shift PP error, or final
causal rho_N assembly is claimed. SOURCE_ONLY / UNCOMPILED /
KERNEL_UNVERIFIED: this environment has no locked Lean/Lake executable.
-/

namespace ImbalancedChen.P3ActualEvenLowerActiveSmallLogMoment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualEvenLowerEulerMass
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
open ImbalancedChen.P3ActualEvenLowerActivePairPrimeMoment

/-- Elementary all-integer omega bound. Distinct prime factors cost at
least a factor 2 each, and their product divides the original integer.
No distributional or sieve theorem is used. -/
theorem primeFactors_card_le_nat_log_two (s : ℕ) (hs : s ≠ 0) :
    s.primeFactors.card ≤ Nat.log 2 s := by
  classical
  have hpow : 2 ^ s.primeFactors.card ≤ s := by
    calc
      2 ^ s.primeFactors.card =
          ∏ p ∈ s.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ s.primeFactors, p := by
        apply Finset.prod_le_prod'
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ s := Nat.le_of_dvd (Nat.pos_of_ne_zero hs)
        (Nat.prod_primeFactors_dvd s)
  exact Nat.le_log_of_pow_le Nat.one_lt_two hpow

/-- The ACTUAL inclusive prime-divisor correction is bounded by a
binary logarithm even when the integer is not squarefree. -/
theorem chen_prime_divisor_count_le_nat_log_two (N s : ℕ)
    (hs : s ≠ 0) :
    chenPrimeDivisorCount N s ≤ (Nat.log 2 s : ℝ) := by
  have hcard := chen_prime_divisor_count_le_primeFactors_card N s hs
  have hlog : (s.primeFactors.card : ℝ) ≤ (Nat.log 2 s : ℝ) := by
    exact_mod_cast primeFactors_card_le_nat_log_two s hs
  exact hcard.trans hlog

/-- This is the genuine STRICTLY ACTIVE Rosser support, not the full
displayed divisor support. If L ≤ A, each member is positive and ≤ A,
so its genuine first prime-divisor moment is at most
log_2(A) times the already established reciprocal-totient log cap. -/
theorem actual_active_small_prime_moment_le_nat_log_cap
    (N cap A : ℕ) (w L : ℝ) (hLA : L ≤ (A : ℝ)) :
    (∑ s ∈ activeSmallRosserByLevel N cap w L,
      chenPrimeDivisorCount N s * (Nat.totient s : ℝ)⁻¹) ≤
      (Nat.log 2 A : ℝ) * logTotientCap A := by
  classical
  let S := activeSmallRosserByLevel N cap w L
  have hcap : S ⊆ Finset.Icc 1 A := by
    intro s hs
    have hs0 : 0 < s := Nat.pos_of_ne_zero
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w
        (Finset.mem_filter.mp hs).1).1
    have hsA : (s : ℝ) ≤ (A : ℝ) :=
      (le_of_lt (Finset.mem_filter.mp hs).2).trans hLA
    exact Finset.mem_Icc.mpr ⟨hs0, by exact_mod_cast hsA⟩
  have hcount (s : ℕ) (hs : s ∈ S) :
      chenPrimeDivisorCount N s ≤ (Nat.log 2 A : ℝ) := by
    have hs0 : 0 < s := (Finset.mem_Icc.mp (hcap hs)).1
    have hsA : s ≤ A := (Finset.mem_Icc.mp (hcap hs)).2
    have hbound : (Nat.log 2 s : ℝ) ≤ (Nat.log 2 A : ℝ) := by
      exact_mod_cast Nat.log_mono_right hsA
    exact (chen_prime_divisor_count_le_nat_log_two N s
      (Nat.ne_of_gt hs0)).trans hbound
  have hsub :
      (∑ s ∈ S, (Nat.totient s : ℝ)⁻¹) ≤
      ∑ s ∈ Finset.Icc 1 A, (Nat.totient s : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hcap
      (fun s hs hnot => by positivity)
  calc
    (∑ s ∈ S, chenPrimeDivisorCount N s * (Nat.totient s : ℝ)⁻¹)
        ≤ ∑ s ∈ S, (Nat.log 2 A : ℝ) *
            (Nat.totient s : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_right (hcount s hs) (by positivity)
    _ = (Nat.log 2 A : ℝ) *
          (∑ s ∈ S, (Nat.totient s : ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ (Nat.log 2 A : ℝ) *
          (∑ s ∈ Finset.Icc 1 A, (Nat.totient s : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ (Nat.log 2 A : ℝ) * logTotientCap A :=
          mul_le_mul_of_nonneg_left (sum_reciprocal_totient_le_log A)
            (by positivity)

/-- The original U6 LOWER integer rho quotient-prime correction, with
the physical prefix b=t.1*t.2 and exactly the original full modulus b*q,
has an EXPLICIT finite bound: one active-small binary-log moment and the
literal even-retained rough Euler zero/first moments. This is NOT the
nonzero-shift PP discrepancy nor its arbitrary-log saving. -/
theorem actual_U6_lower_quotient_prime_correction_abs_le_log_euler
    (N A : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    (hLA : L t ≤ (A : ℝ)) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    |∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
    (Nat.totient b : ℝ)⁻¹ *
      (((Nat.log 2 A : ℝ) * logTotientCap A) *
          roughEulerMass N cap (w t) z +
       logTotientCap A *
          (roughEulerMass N cap (w t) z *
            (∑ p ∈ roughPrimeFinset N cap (w t) z, roughPrimeInvPhi p))) := by
  have hstart := actual_U6_lower_quotient_prime_correction_abs_le_active_moments
    N t ht policy w L hwz
  dsimp at hstart ⊢
  let z := P5CausalRhoQuotientBridge.cutoff N
  let cap := Nat.ceil z
  let S := activeSmallRosserByLevel N cap (w t) (L t)
  let R := fixedEvenRoughSupport (policy t) N cap (w t) z
  let E := roughEulerMass N cap (w t) z
  let J := ∑ p ∈ roughPrimeFinset N cap (w t) z, roughPrimeInvPhi p
  let S0 := ∑ s ∈ S, (Nat.totient s : ℝ)⁻¹
  let S1 := ∑ s ∈ S,
    chenPrimeDivisorCount N s * (Nat.totient s : ℝ)⁻¹
  let R0 := ∑ r ∈ R, (Nat.totient r : ℝ)⁻¹
  let R1 := ∑ r ∈ R,
    chenPrimeDivisorCount N r * (Nat.totient r : ℝ)⁻¹
  have hS0 : S0 ≤ logTotientCap A := by
    have hcap : S ⊆ Finset.Icc 1 A := by
      intro s hs
      have hs0 : 0 < s := Nat.pos_of_ne_zero
        (actualSmallRosserSupport_smallPrimeSupportedAt N cap (w t)
          (Finset.mem_filter.mp hs).1).1
      have hsA : (s : ℝ) ≤ (A : ℝ) :=
        (le_of_lt (Finset.mem_filter.mp hs).2).trans hLA
      exact Finset.mem_Icc.mpr ⟨hs0, by exact_mod_cast hsA⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hcap
      (fun s hs hnot => by positivity)).trans
        (sum_reciprocal_totient_le_log A)
  have hS1 : S1 ≤ (Nat.log 2 A : ℝ) * logTotientCap A :=
    actual_active_small_prime_moment_le_nat_log_cap N cap A (w t) (L t) hLA
  have hR0 : R0 ≤ E :=
    actual_even_retained_rough_totient_mass_le_euler
      (policy t) N cap (w t) z
  have hR1 : R1 ≤ E * J :=
    actual_even_retained_rough_prime_divisor_moment_le_euler
      (policy t) N cap (w t) z
  have hR0nonneg : 0 ≤ R0 :=
    Finset.sum_nonneg (fun r hr => by positivity)
  have hR1nonneg : 0 ≤ R1 :=
    Finset.sum_nonneg (fun r hr => by
      unfold chenPrimeDivisorCount
      positivity)
  have hsmallbound : 0 ≤ (Nat.log 2 A : ℝ) * logTotientCap A :=
    mul_nonneg (by positivity) (logTotientCap_nonneg A)
  have hterm1 :
      S1 * R0 ≤ ((Nat.log 2 A : ℝ) * logTotientCap A) * E := by
    calc
      _ ≤ ((Nat.log 2 A : ℝ) * logTotientCap A) * R0 :=
        mul_le_mul_of_nonneg_right hS1 hR0nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hR0 hsmallbound
  have hterm2 : S0 * R1 ≤ logTotientCap A * (E * J) := by
    calc
      _ ≤ logTotientCap A * R1 :=
        mul_le_mul_of_nonneg_right hS0 hR1nonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hR1
        (logTotientCap_nonneg A)
  calc
    _ ≤ (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (S1 * R0 + S0 * R1) := hstart
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add hterm1 hterm2) (by positivity)

end
end ImbalancedChen.P3ActualEvenLowerActiveSmallLogMoment
