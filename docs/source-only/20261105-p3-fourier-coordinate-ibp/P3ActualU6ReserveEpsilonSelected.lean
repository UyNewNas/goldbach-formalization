import ImbalancedChen.P3ActualU6EnhancedCapUniformGate
import Mathlib.Tactic

/-!
P3.6 manuscript-INTERNAL, frozen paper
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1(PP), 3(T), 4(F).

Real production entry:
  P5CausalRhoQuotientBridge.exists_quotient_full_density_reserve
has a UNIVERSAL positive epsilonMax before its EXISTENTIAL epsilon.
Choosing epsilonMax = 1/(nu+1) (nu>0) makes the already-produced
epsilon satisfy nu*epsilon<1, without assuming that the unrestricted
parameters in the preceding packet happened to satisfy it.

This is existential SELECTION of an admissible reserve epsilon, not an
assertion that the final finite compiler selected it, not a replacement
for its original integer rho, and not an offshift-discrepancy or PP proof.
The production density uses its genuine even-exit lower coefficient;
the correction still has the literal labelled sixthSupport N and the
same policy-dependent integer LOWER rho at each physical modulus.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6ReserveEpsilonSelected

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P5CausalRhoQuotientBridge
open ImbalancedChen.P3ActualU6EnhancedPowerLevel
open ImbalancedChen.P3ActualU6EnhancedCapUniformGate
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

/-- True production reserve epsilon may be selected small enough for
the target-power cap while retaining the original FULL density statement,
including its actual even first-exit coefficient, arbitrary cap,
retainEven policy, physical prefix b and literal totient denominator.
This uses the existing epsilonMax quantifier rather than adding a gate
as a new premise. -/
theorem exists_original_lower_reserve_with_target_power_gate
    (nu r eta : ℝ)
    (hnu : 0 < nu) (hr : 0 < r) (heta : 0 < eta) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon ^ 2 ≤ r ∧
      nu * epsilon ≤ 1 ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
            ∀ retainEven : List ℕ → Bool,
              ∀ b : ℕ, ∀ M : ℝ, 0 ≤ M →
                M / (Nat.totient b : ℝ) *
                    (reciprocalTotientDensity
                      (fixedEvenRoughSupport retainEven N cap 0
                        ((N : ℝ) ^ (nu * r)))
                      (fixedEvenRoughCoefficient retainEven N cap 0
                        ((N : ℝ) ^ (nu * r))) -
                      eta * singularSeries N / Real.log (N : ℝ)) ≤
                  M / (Nat.totient b : ℝ) *
                    physicalDensitySum
                      (actualLowerSmallRoughModuli retainEven N cap
                        ((N : ℝ) ^ (nu * epsilon ^ 2))
                        ((N : ℝ) ^ (nu * r)))
                      (actualLowerSmallRoughRho retainEven N cap
                        ((N : ℝ) ^ (nu * epsilon ^ 2))
                        ((N : ℝ) ^ (nu * r))
                        ((N : ℝ) ^ (nu * epsilon))) := by
  have hden : 0 < nu + 1 := by linarith
  have hepsMax : 0 < (1 : ℝ) / (nu + 1) :=
    div_pos (by norm_num) hden
  obtain ⟨epsilon, heps, heps8, hsmall, hepsr,
      N₀, hN₀, hreserve⟩ :=
    P5CausalRhoQuotientBridge.exists_quotient_full_density_reserve
      nu r eta (1 / (nu + 1)) hnu hr heta hepsMax
  have hproduct : epsilon * (nu + 1) < 1 :=
    (lt_div_iff₀ hden).mp hsmall
  have hgate : nu * epsilon ≤ 1 := by
    nlinarith [le_of_lt heps]
  exact ⟨epsilon, heps, heps8, hepsr, hgate, N₀, hN₀, hreserve⟩

/-- A SINGLE Mertens envelope constant precedes all actual reserve
parameters. The epsilon furnished by the existing production density
theorem can be chosen to ALSO pay the same integer LOWER U6 quotient
prime-factor correction by target-N logarithmic factors, on the literal
original sixthSupport and for every original even policy.

The full reserve statement and correction share the SAME epsilon,
nu, r and threshold N₀. Matching the final U6 cutoff still explicitly
requires nu*r=417/5000. The final compiler's selected policy and
all other PP/HB sources remain independent internal obligations. -/
theorem exists_one_constant_original_lower_reserve_and_U6_correction :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu r eta : ℝ), 0 < nu → 0 < r → 0 < eta →
        nu * r = (417 / 5000 : ℝ) →
        ∃ epsilon : ℝ,
          0 < epsilon ∧ epsilon < 1 / 8 ∧
          epsilon ^ 2 ≤ r ∧ nu * epsilon ≤ 1 ∧
          ∃ N₀ : ℕ, 2 ≤ N₀ ∧
            (∀ N : ℕ, N₀ ≤ N → Even N →
              ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
                ∀ retainEven : List ℕ → Bool,
                  ∀ b : ℕ, ∀ M : ℝ, 0 ≤ M →
                    M / (Nat.totient b : ℝ) *
                        (reciprocalTotientDensity
                          (fixedEvenRoughSupport retainEven N cap 0
                            ((N : ℝ) ^ (nu * r)))
                          (fixedEvenRoughCoefficient retainEven N cap 0
                            ((N : ℝ) ^ (nu * r))) -
                          eta * singularSeries N / Real.log (N : ℝ)) ≤
                      M / (Nat.totient b : ℝ) *
                        physicalDensitySum
                          (actualLowerSmallRoughModuli retainEven N cap
                            ((N : ℝ) ^ (nu * epsilon ^ 2))
                            ((N : ℝ) ^ (nu * r)))
                          (actualLowerSmallRoughRho retainEven N cap
                            ((N : ℝ) ^ (nu * epsilon ^ 2))
                            ((N : ℝ) ^ (nu * r))
                            ((N : ℝ) ^ (nu * epsilon)))) ∧
            (∀ N : ℕ, N₀ ≤ N → Even N →
              ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
                |∑ t ∈ sixthSupport N,
                  rowQuotientPrimeCorrection N policy
                    (fun _ => enhancedSmallW N nu epsilon)
                    (fun _ => enhancedRosserL N nu epsilon) t| ≤
                  (logTotientCap N) ^ 3 *
                    (C * (1 + Real.log (N : ℝ))) *
                    ((Nat.log 2 N : ℝ) +
                      C * (1 + Real.log (N : ℝ)))) := by
  obtain ⟨C, hC, hcorrection⟩ :=
    exists_enhanced_original_U6_correction_target_level_gate
  refine ⟨C, hC, ?_⟩
  intro nu r eta hnu hr heta hnur
  obtain ⟨epsilon, heps, heps8, hepsr, hgate,
      N₀, hN₀, hreserve⟩ :=
    exists_original_lower_reserve_with_target_power_gate nu r eta hnu hr heta
  refine ⟨epsilon, heps, heps8, hepsr, hgate,
    N₀, hN₀, hreserve, ?_⟩
  intro N hN hEven policy
  have hN2 : 2 ≤ N := le_trans hN₀ hN
  exact hcorrection nu r epsilon hnu heps heps8 hepsr
    hnur hgate N hN2 policy

end
end ImbalancedChen.P3ActualU6ReserveEpsilonSelected
