import ImbalancedChen.P3ActualU6PrefixMassLogSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
P3.6; frozen paper UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §1 (PP), §3 (T), §4 (F).

The genuine PRODUCTION reserve
CurrentChenP5CausalRhoQuotientBridge.exists_quotient_full_density_reserve
uses the powers w=N^(nu*epsilon^2), z=N^(nu*r), L=N^(nu*epsilon).
We match z to the actual U6 source cutoff N^(417/5000) by the
EXPLICIT compatibility nu*r=417/5000. Policy remains the original
label-dependent even first-exit LOWER policy; it is not substituted.

The ceiling of L is a common SMALL-MASS budget cap, not a physical
modulus cap and not the ordinary rounded quotient Rosser D(B,N,b).
No claim that the final compiler chooses compatible nu,r,epsilon or
a particular policy, no signed discrepancy, global rho_N, or PP claim.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6EnhancedPowerLevel
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5SelectedMaskTransport
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualU6PrefixMassLogSquare
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

/-- Exact small presieve power from the original even-exit reserve. -/
def enhancedSmallW (N : ℕ) (nu epsilon : ℝ) : ℝ :=
  (N : ℝ) ^ (nu * epsilon ^ 2)

/-- Exact real small Rosser level from the original even-exit reserve. -/
def enhancedRosserL (N : ℕ) (nu epsilon : ℝ) : ℝ :=
  (N : ℝ) ^ (nu * epsilon)

/-- Common positive-mass level only, without changing source moduli. -/
def enhancedPowerCap (N : ℕ) (nu epsilon : ℝ) : ℕ :=
  Nat.ceil (enhancedRosserL N nu epsilon)

/-- The original actual-power lower-sieve gates. The compatibility with
the physical U6 cutoff is made explicit rather than guessed. -/
theorem enhanced_power_gates
    (nu r epsilon : ℝ)
    (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilon8 : epsilon < 1 / 8)
    (hepsilonr : epsilon ^ 2 ≤ r)
    (hnur : nu * r = (417 / 5000 : ℝ))
    (N : ℕ) (hN : 2 ≤ N) :
    1 < enhancedRosserL N nu epsilon ∧
      enhancedSmallW N nu epsilon ≤ enhancedRosserL N nu epsilon ∧
      enhancedSmallW N nu epsilon ≤
        P5CausalRhoQuotientBridge.cutoff N := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNbase : (1 : ℝ) ≤ (N : ℝ) := hN1.le
  have hsquare : epsilon ^ 2 ≤ epsilon := by
    nlinarith [mul_nonneg (le_of_lt hepsilon)
      (show 0 ≤ 1 - epsilon by linarith)]
  have hL : 1 < enhancedRosserL N nu epsilon := by
    unfold enhancedRosserL
    exact Real.one_lt_rpow hN1 (mul_pos hnu hepsilon)
  have hwL : enhancedSmallW N nu epsilon ≤
      enhancedRosserL N nu epsilon := by
    unfold enhancedSmallW enhancedRosserL
    exact Real.rpow_le_rpow_of_exponent_le hNbase
      (mul_le_mul_of_nonneg_left hsquare hnu.le)
  have hwz : enhancedSmallW N nu epsilon ≤
      P5CausalRhoQuotientBridge.cutoff N := by
    have hexp : nu * epsilon ^ 2 ≤ (417 / 5000 : ℝ) := by
      calc
        nu * epsilon ^ 2 ≤ nu * r :=
          mul_le_mul_of_nonneg_left hepsilonr hnu.le
        _ = (417 / 5000 : ℝ) := hnur
    change (N : ℝ) ^ (nu * epsilon ^ 2) ≤
      (N : ℝ) ^ (417 / 5000 : ℝ)
    exact Real.rpow_le_rpow_of_exponent_le hNbase hexp
  exact ⟨hL, hwL, hwz⟩

/-- A single exact natural cap of the actual real L for all U6 rows. -/
theorem enhanced_power_level_le_common_cap
    (N : ℕ) (nu epsilon : ℝ) :
    enhancedRosserL N nu epsilon ≤
      (enhancedPowerCap N nu epsilon : ℝ) := by
  change (N : ℝ) ^ (nu * epsilon) ≤
    (Nat.ceil ((N : ℝ) ^ (nu * epsilon)) : ℝ)
  exact Nat.le_ceil _

/-- Actual all-label even first-exit LOWER finite minorant for the
original power family, without a new source or selected-mask premise. -/
theorem enhanced_power_all_original_U6_rows_minorize
    (nu r epsilon : ℝ)
    (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilon8 : epsilon < 1 / 8)
    (hepsilonr : epsilon ^ 2 ≤ r)
    (hnur : nu * r = (417 / 5000 : ℝ))
    (N : ℕ) (hN : 2 ≤ N)
    (policy : (ℕ × ℕ) → List ℕ → Bool) :
    ∀ t ∈ sixthSupport N,
      P5CausalRhoQuotientBridge.rowEstimator N policy
        (fun _ => enhancedSmallW N nu epsilon)
        (fun _ => enhancedRosserL N nu epsilon) t ≤
          sixthWeight N t := by
  intro t ht
  exact P5CausalRhoQuotientBridge.rowEstimator_le_actual
    N policy (fun _ => enhancedSmallW N nu epsilon)
      (fun _ => enhancedRosserL N nu epsilon) t
      (enhanced_power_gates nu r epsilon hnu hepsilon
        hepsilon8 hepsilonr hnur N hN)

/-- The actual production powers DISCHARGE the previous whole-U6
ledger's assumptions w(t)≤z and L(t)≤A. One C precedes every
power/target/policy; integer rho, physical phi((p1*p2)*q), signed
coefficients, original labels and multiplicities are untouched.

The complete A(N) logarithmic envelope and global rho_N still remain
separate manuscript-internal obligations. -/
theorem exists_enhanced_original_U6_quotient_correction_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu r epsilon : ℝ),
        0 < nu → 0 < epsilon → epsilon < 1 / 8 →
        epsilon ^ 2 ≤ r → nu * r = (417 / 5000 : ℝ) →
        ∀ (N : ℕ), 2 ≤ N →
          ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
            |∑ t ∈ sixthSupport N,
              rowQuotientPrimeCorrection N policy
                (fun _ => enhancedSmallW N nu epsilon)
                (fun _ => enhancedRosserL N nu epsilon) t| ≤
              (logTotientCap N) ^ 2 *
                (logTotientCap (enhancedPowerCap N nu epsilon) *
                  (C * (1 + Real.log (N : ℝ))) *
                  ((Nat.log 2 (enhancedPowerCap N nu epsilon) : ℝ) +
                    C * (1 + Real.log (N : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_all_original_U6_quotient_correction_with_paid_prefix
  refine ⟨C, hC, ?_⟩
  intro nu r epsilon hnu hepsilon hepsilon8 hepsilonr hnur N hN policy
  let A := enhancedPowerCap N nu epsilon
  let w : (ℕ × ℕ) → ℝ := fun _ => enhancedSmallW N nu epsilon
  let L : (ℕ × ℕ) → ℝ := fun _ => enhancedRosserL N nu epsilon
  have hgates :=
    enhanced_power_gates nu r epsilon hnu hepsilon
      hepsilon8 hepsilonr hnur N hN
  have hwz : ∀ t ∈ sixthSupport N,
      w t ≤ P5CausalRhoQuotientBridge.cutoff N := by
    intro t ht
    exact hgates.2.2
  have hLA : ∀ t ∈ sixthSupport N, L t ≤ (A : ℝ) := by
    intro t ht
    exact enhanced_power_level_le_common_cap N nu epsilon
  exact hbound N A hN policy w L hwz hLA

end
end ImbalancedChen.P3ActualU6EnhancedPowerLevel
