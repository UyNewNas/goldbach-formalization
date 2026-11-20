import ImbalancedChen.P3ActualU6EnhancedPowerLevel
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
P3.6 manuscript-INTERNAL: explicit uniformity gate on the actual enhanced
small Rosser cap, NOT on the whole physical modulus.

Paper is pinned to UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
distribution-prime-product-completion §1(PP), §3(T), §4(F).

The preceding production-power bridge supplies
w=N^(nu*epsilon^2), L=N^(nu*epsilon), z=N^(417/5000)
under nu*r=417/5000, epsilon^2<=r, 0<epsilon<1/8.
Those conditions DO NOT imply nu*epsilon<=1. A rational
counterexample is supplied below instead of silently assuming it.

Only WITH the additional explicit, checkable small-LEVEL gate
nu*epsilon<=1 do we have ceil(L)<=N, allowing the already-derived
one-constant integer LOWER U6 correction to be paid by the SAME
logTotientCap(N) and Nat.log 2 N. This is NOT a proof that the final
producer chooses such parameters/policy or that the complete global
rho_N, offshift discrepancy, Fourier H-tail, or PP are closed.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6EnhancedCapUniformGate
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualU6EnhancedPowerLevel
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap

/-- Genuine admissible reserve-power parameters can have an enhanced
small Rosser exponent strictly GREATER than one. This prevents a
false unqualified uniform N-level assertion. -/
theorem compatible_reserve_parameters_can_exceed_target_power :
    ∃ nu r epsilon : ℝ,
      0 < nu ∧ 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon ^ 2 ≤ r ∧ nu * r = (417 / 5000 : ℝ) ∧
      1 < nu * epsilon := by
  refine ⟨834, 1 / 10000, 1 / 100, ?_⟩
  norm_num

/-- The cap of the actual L=N^(nu*epsilon) is at most the original N
only if the exponent condition is separately supplied. This is a
small Rosser mass level; never an auxiliary or physical modulus cap. -/
theorem enhanced_power_cap_le_target_of_exponent_gate
    (N : ℕ) (nu epsilon : ℝ) (hN : 2 ≤ N)
    (hgate : nu * epsilon ≤ 1) :
    enhancedPowerCap N nu epsilon ≤ N := by
  have hNbase : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^ (nu * epsilon) ≤ (N : ℝ) :=
    Real.rpow_le_self_of_one_le hNbase hgate
  change Nat.ceil ((N : ℝ) ^ (nu * epsilon)) ≤ N
  exact Nat.ceil_le.mpr hpow

/-- Elementary monotonicity of the existing finite reciprocal-totient
cap, used without any new distribution input. -/
theorem logTotientCap_le_of_le {A N : ℕ} (hAN : A ≤ N) :
    logTotientCap A ≤ logTotientCap N := by
  unfold logTotientCap
  have hreal : (A : ℝ) ≤ (N : ℝ) := by exact_mod_cast hAN
  have hmax :
      max (1 : ℝ) (A : ℝ) ≤ max (1 : ℝ) (N : ℝ) :=
    max_le_max le_rfl hreal
  have hpos : 0 < max (1 : ℝ) (A : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_left 1 (A : ℝ))
  exact mul_le_mul_of_nonneg_left
    (add_le_add_left (Real.log_le_log hpos hmax) 1) (by norm_num)

/-- BOTH remaining small-level factors have the original target N as
a cap, with the Nat.log comparison from the pinned Mathlib release. -/
theorem enhanced_power_level_both_logs_le_target
    (N : ℕ) (nu epsilon : ℝ) (hN : 2 ≤ N)
    (hgate : nu * epsilon ≤ 1) :
    logTotientCap (enhancedPowerCap N nu epsilon) ≤ logTotientCap N ∧
      Nat.log 2 (enhancedPowerCap N nu epsilon) ≤ Nat.log 2 N := by
  have hcap := enhanced_power_cap_le_target_of_exponent_gate
    N nu epsilon hN hgate
  exact ⟨logTotientCap_le_of_le hcap, Nat.log_mono_right hcap⟩

/-- The SAME universal C inherited from the finite Mertens envelope
now pays the actual U6 even-first-exit LOWER quotient-prime correction
by target-N logarithmic factors, under an explicit producer exponent
gate. Original labelled sixthSupport, policy-dependent INTEGER rho,
repeats and physical phi((t.1*t.2)*q) are not changed.

The extra nu*epsilon<=1 premise is NOT implied by the earlier
compatibility gates, as the counterexample above proves. -/
theorem exists_enhanced_original_U6_correction_target_level_gate :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu r epsilon : ℝ),
        0 < nu → 0 < epsilon → epsilon < 1 / 8 →
        epsilon ^ 2 ≤ r → nu * r = (417 / 5000 : ℝ) →
        nu * epsilon ≤ 1 →
        ∀ (N : ℕ), 2 ≤ N →
          ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
            |∑ t ∈ sixthSupport N,
              rowQuotientPrimeCorrection N policy
                (fun _ => enhancedSmallW N nu epsilon)
                (fun _ => enhancedRosserL N nu epsilon) t| ≤
              (logTotientCap N) ^ 3 *
                (C * (1 + Real.log (N : ℝ))) *
                ((Nat.log 2 N : ℝ) + C * (1 + Real.log (N : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_enhanced_original_U6_quotient_correction_bound
  refine ⟨C, hC, ?_⟩
  intro nu r epsilon hnu heps heps8 hepsr hnur hgate N hN policy
  let A := enhancedPowerCap N nu epsilon
  let U : ℝ := C * (1 + Real.log (N : ℝ))
  have hcap : A ≤ N :=
    enhanced_power_cap_le_target_of_exponent_gate N nu epsilon hN hgate
  have hL : logTotientCap A ≤ logTotientCap N :=
    logTotientCap_le_of_le hcap
  have hk : (Nat.log 2 A : ℝ) ≤ (Nat.log 2 N : ℝ) := by
    exact_mod_cast (Nat.log_mono_right hcap)
  have hNbase : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hU0 : 0 ≤ U := by
    dsimp [U]
    exact mul_nonneg hC.le (by have h := Real.log_nonneg hNbase; linarith)
  have hinner :
      logTotientCap A * U * ((Nat.log 2 A : ℝ) + U) ≤
        logTotientCap N * U * ((Nat.log 2 N : ℝ) + U) := by
    calc
      _ ≤ logTotientCap N * U * ((Nat.log 2 A : ℝ) + U) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hL hU0)
          (add_nonneg (by positivity) hU0)
      _ ≤ logTotientCap N * U * ((Nat.log 2 N : ℝ) + U) :=
        mul_le_mul_of_nonneg_left
          (add_le_add_right hk U)
          (mul_nonneg (logTotientCap_nonneg N) hU0)
  calc
    _ ≤ (logTotientCap N) ^ 2 *
      (logTotientCap A * U * ((Nat.log 2 A : ℝ) + U)) := by
        simpa [A, U] using
          (hbound nu r epsilon hnu heps heps8 hepsr hnur N hN policy)
    _ ≤ (logTotientCap N) ^ 2 *
      (logTotientCap N * U * ((Nat.log 2 N : ℝ) + U)) :=
        mul_le_mul_of_nonneg_left hinner (sq_nonneg _)
    _ = (logTotientCap N) ^ 3 * U * ((Nat.log 2 N : ℝ) + U) := by ring

end
end ImbalancedChen.P3ActualU6EnhancedCapUniformGate
