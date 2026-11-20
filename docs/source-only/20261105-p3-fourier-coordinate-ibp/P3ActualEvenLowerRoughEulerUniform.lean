import ImbalancedChen.P3ActualEvenLowerOneEulerMoment
import ImbalancedChen.Part3RoughEulerEnvelopePayment
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1(PP),3(T),4(F).
The literal rough carrier p<cap, p prime, p∤N, w≤p<z is only
ENLARGED for a positive Euler MASS upper bound to the inclusive
Mertens carrier p≤floor z. The actual integer LOWER rho, physical
b*q, strict endpoints, source tags and multiplicities are unchanged.
Reuses the PINNED existing Mertens primeProduct_asymptotic_order
via the old, uncompiled Part3RoughEulerEnvelopePayment wrapper.
EXTERNAL_INPUTS.json records the classical dependency, not its proof.
No new axiom and no target-equivalent signed discrepancy premise.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerRoughEulerUniform
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
open ImbalancedChen.P3ActualEvenLowerActiveSmallLogMoment
open ImbalancedChen.P3ActualEvenLowerOneEulerMoment
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b
open ImbalancedChen.Part3.RoughFiniteEulerBounds20261026b
open ImbalancedChen.Part3.RoughEulerEnvelopePayment20261026b

private theorem prime_inv_phi_factor_eq (p : ℕ) (hp : p.Prime) :
    1 + (((p-1 : ℕ) : ℝ))⁻¹ = (1 - 1 / (p : ℝ))⁻¹ := by
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpg : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hc : ((p-1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp1]
    norm_num
  rw [hc]
  have hpn : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hpm : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have hsmall : 1 / (p : ℝ) < 1 := (div_lt_one₀ hp0).mpr hpg
  have hd : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by linarith
  field_simp [hpn, hpm, hd]
  <;> ring

/-- Strict physical rough carrier -> inclusive Mertens carrier only
for this nonnegative absolute Euler upper bound. -/
theorem actual_rough_euler_le_inverse_envelope
    (N cap : ℕ) (w z : ℝ) :
    roughEulerMass N cap w z ≤ inverseEnvelope z := by
  classical
  have hsub : roughPrimeFinset N cap w z ⊆ smallPrimes z := by
    intro p hp
    have h := mem_roughPrimeFinset.mp hp
    have hz : 0 ≤ z :=
      le_trans (Nat.cast_nonneg p) (le_of_lt h.2.2.2.2)
    exact (mem_smallPrimes hz).mpr ⟨h.2.1, le_of_lt h.2.2.2.2⟩
  calc
    roughEulerMass N cap w z =
        ∏ p ∈ roughPrimeFinset N cap w z,
          (1 - 1/(p : ℝ))⁻¹ := by
            unfold roughEulerMass
            apply Finset.prod_congr rfl
            intro p hp
            exact prime_inv_phi_factor_eq p
              (mem_roughPrimeFinset.mp hp).2.1
    _ ≤ ∏ p ∈ smallPrimes z, (1 - 1/(p : ℝ))⁻¹ := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hsub
      intro p hp _
      have hprime : p.Prime := smallPrimes_prime hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.pos
      have hpg : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
      have hs : 1 / (p : ℝ) < 1 := (div_lt_one₀ hp0).mpr hpg
      have hs0 : 0 ≤ 1 / (p : ℝ) := by positivity
      have hd : 0 < (1 : ℝ) - 1 / (p : ℝ) := by linarith
      change (1 : ℝ) ≤ 1 / (1 - 1 / (p : ℝ))
      apply (le_div_iff₀ hd).mpr
      linarith
    _ = inverseEnvelope z := rfl

def roughLogEnvelope (C z : ℝ) : ℝ :=
  C * (1 + Real.log (max 2 z))

/-- Uniform in actual N, cap, w, z. External classical Mertens is
REUSED from the existing pinned library wrapper, not implemented. -/
theorem exists_original_rough_euler_le_log_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (N cap : ℕ) (w z : ℝ),
      roughEulerMass N cap w z ≤ roughLogEnvelope C z := by
  obtain ⟨C, hC, hbound⟩ := exists_inverseEnvelope_le_log
  refine ⟨C, hC, ?_⟩
  intro N cap w z
  exact (actual_rough_euler_le_inverse_envelope N cap w z).trans
    (by simpa only [roughLogEnvelope] using hbound z)

/-- The actual even-first-exit LOWER INTEGER rho with the original
physical prefix b and denominator phi(b*q); NOT the full rho_N or PP. -/
theorem exists_actual_U6_lower_quotient_correction_log_envelope :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N A : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
        (policy : (ℕ × ℕ) → List ℕ → Bool)
        (w L : (ℕ × ℕ) → ℝ)
        (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
        (hLA : L t ≤ (A : ℝ)),
      let z := P5CausalRhoQuotientBridge.cutoff N
      let cap := Nat.ceil z
      let b := t.1 * t.2
      let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
      let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
      |∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b*q) : ℝ))| ≤
        (Nat.totient b : ℝ)⁻¹ *
          (logTotientCap A * roughLogEnvelope C z *
            ((Nat.log 2 A : ℝ) + roughLogEnvelope C z)) := by
  obtain ⟨C, hC, hbound⟩ := exists_original_rough_euler_le_log_envelope
  refine ⟨C, hC, ?_⟩
  intro N A t ht policy w L hwz hLA
  have hstart :=
    actual_U6_lower_quotient_prime_correction_abs_le_one_euler
      N A t ht policy w L hwz hLA
  dsimp at hstart ⊢
  let z := P5CausalRhoQuotientBridge.cutoff N
  let cap := Nat.ceil z
  let E := roughEulerMass N cap (w t) z
  let M := roughLogEnvelope C z
  let k : ℝ := (Nat.log 2 A : ℝ)
  have hEM : E ≤ M := hbound N cap (w t) z
  have hJ0 : 0 ≤ ∑ p ∈ roughPrimeFinset N cap (w t) z,
      roughPrimeInvPhi p := by
    apply Finset.sum_nonneg
    intro p hp
    unfold roughPrimeInvPhi
    positivity
  have hE0 : 0 ≤ E := by
    have h := rough_prime_sum_add_one_le_euler N cap (w t) z
    change 1 + (∑ p ∈ roughPrimeFinset N cap (w t) z,
      roughPrimeInvPhi p) ≤ E at h
    linarith
  have hlog0 : 0 ≤ Real.log (max (2 : ℝ) z) :=
    Real.log_nonneg (by
      exact le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left 2 z))
  have hM0 : 0 ≤ M := by
    change 0 ≤ C * (1 + Real.log (max 2 z))
    exact mul_nonneg hC.le (by linarith)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hquad : E * (k + E) ≤ M * (k + M) := by
    calc
      _ ≤ M * (k + E) :=
        mul_le_mul_of_nonneg_right hEM (add_nonneg hk hE0)
      _ ≤ M * (k + M) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hEM k) hM0
  calc
    _ ≤ (Nat.totient (t.1*t.2) : ℝ)⁻¹ *
        (logTotientCap A * E * (k + E)) := hstart
    _ ≤ (Nat.totient (t.1*t.2) : ℝ)⁻¹ *
        (logTotientCap A * M * (k + M)) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          logTotientCap A * E * (k + E) =
              logTotientCap A * (E * (k + E)) := by ring
          _ ≤ logTotientCap A * (M * (k + M)) :=
            mul_le_mul_of_nonneg_left hquad (logTotientCap_nonneg A)
          _ = logTotientCap A * M * (k + M) := by ring
      · positivity

end
end ImbalancedChen.P3ActualEvenLowerRoughEulerUniform
