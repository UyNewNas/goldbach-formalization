import ImbalancedChen.P1Full87ChangedRoughLevelObstruction
import ImbalancedChen.P4ASameRhoCompact
import Mathlib.Tactic

/-!
P1.4 source-only continuation: audit the literal lower rough-prime endpoint
against the real compact physical attachment.

The preceding fifth-factor bound is w^5 <= b, not (N^rho_0)^5 <= b.
The actual compact attachment in ActualUpperCountingInputs and
P4ASameRhoCompact.attached_moduli_eq_firstExit uses
  w = N^(epsilon^2), z = N^thirdPrefixRho, L = N^epsilon
when nu=1. The finite compact precision supplier has
  epsilon > 0, epsilon <= 2*e, e <= 1/384.
Hence 5*epsilon^2 <= 5/36864 < thirdPrefixRho < 599/1000.
For N >= 2 the fifth-power endpoint lies strictly BELOW the rough
ceiling and the manuscript physical theta_* scale. Thus the earlier
conditional low-modulus exclusion premise cannot be installed by
mistaking z=N^rho_0 for w.

The RAW/LICENSED full87 policies are still not identified with the
compact coefficient's precise epsilon and parameter supplier. The last
theorem only specializes their original changed-rough arithmetic carrier
when these endpoints are explicitly selected; it does not assert that
the full87 parameter installation has already been authenticated.

SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No external analytic inputs.
-/

namespace ImbalancedChen.P1Full87CompactWScaleAudit

noncomputable section
open Classical

/-- The REAL compact supplier pays a much smaller presieve exponent
than the manuscript's rho_0. This uses its original epsilon <= 2e and
e <= 1/384, with no additional geometry or sieve premise. -/
theorem compact_fifth_exponent_lt_rough
    (e epsilon : ℝ) (he : e ≤ 1 / 384)
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 2 * e) :
    5 * epsilon ^ 2 ≤ (5 / 36864 : ℝ) ∧
      5 * epsilon ^ 2 < thirdPrefixRho := by
  have hsmall : epsilon ≤ (1 / 192 : ℝ) := by linarith
  have hmul : 0 ≤ epsilon * ((1 / 192 : ℝ) - epsilon) :=
    mul_nonneg heps0.le (sub_nonneg.mpr hsmall)
  have hsq : epsilon ^ 2 ≤ (1 / 36864 : ℝ) := by nlinarith
  constructor
  · nlinarith
  · have hnum : (5 / 36864 : ℝ) < (19 / 96 : ℝ) := by norm_num
    dsimp [thirdPrefixRho]
    linarith

/-- The literal N^(epsilon^2) fifth-power threshold of the compact
physical attachment lies BELOW both its rough prime cutoff N^rho_0 and
the manuscript physical support scale N^theta_*.
No full87 coefficient is identified with this compact policy here. -/
theorem compact_fifth_power_below_rough_and_theta
    (e epsilon : ℝ) (N : ℕ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384)
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 2 * e) :
    ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 <
        (N : ℝ) ^ thirdPrefixRho ∧
      ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 <
        (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hNgt : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpow :
      ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 =
        (N : ℝ) ^ (5 * epsilon ^ 2) := by
    calc
      ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 =
          ((N : ℝ) ^ (epsilon ^ 2)) ^ (5 : ℝ) := by
            rw [Real.rpow_nat_cast]
      _ = (N : ℝ) ^ (epsilon ^ 2 * 5) :=
        (Real.rpow_mul hNnn (epsilon ^ 2) (5 : ℝ)).symm
      _ = (N : ℝ) ^ (5 * epsilon ^ 2) := by
        congr 1
        ring
  have hexp := (compact_fifth_exponent_lt_rough e epsilon he heps0 heps).2
  have htheta : thirdPrefixRho < (599 / 1000 : ℝ) := by
    norm_num [thirdPrefixRho]
  constructor
  · rw [hpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hNgt hexp
  · rw [hpow]
    exact Real.rpow_lt_rpow_of_exponent_lt hNgt (lt_trans hexp htheta)

/-- In particular, the strict hypothesis required by the preceding
rough low-carrier emptiness theorem fails at the physical theta_* real
power for this actual compact precision. This is NOT evidence that
a changed modulus exists. -/
theorem compact_theta_cannot_satisfy_low_carrier_exclusion
    (e epsilon : ℝ) (N : ℕ)
    (hN : 2 ≤ N) (he : e ≤ 1 / 384)
    (heps0 : 0 < epsilon) (heps : epsilon ≤ 2 * e) :
    ¬ ((N : ℝ) ^ (599 / 1000 : ℝ) <
       ((N : ℝ) ^ (epsilon ^ 2)) ^ 5) := by
  have h := (compact_fifth_power_below_rough_and_theta
    e epsilon N hN he heps0 heps).2
  exact not_lt_of_ge h.le

/-- Conditional arithmetic installation into the SAME RAW/LICENSED
carrier from the previous packet. This uses the true original policies,
not a fabricated common history; the only new choice is the explicit
w=N^(epsilon^2), z=N^rho_0. It does not claim that those full87
policies have already been certified to use the compact precision. -/
theorem changed_rough_lower_bound_at_compact_endpoint
    (delta : ℝ) (n : ℕ) (r : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (epsilon : ℝ)
    (hN : 2 ≤ N) (heps0 : 0 < epsilon) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy r q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n r q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) \\
       fixedRoughSupport (R false) N cap
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∪
      (fixedRoughSupport (R false) N cap
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) \\
       fixedRoughSupport (S false) N cap
          ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) →
    (N : ℝ) ^ (5 * epsilon ^ 2) ≤ (b : ℝ) := by
  dsimp only
  intro hb
  have hNge : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hw : (1 : ℝ) ≤ (N : ℝ) ^ (epsilon ^ 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hNge (sq_nonneg epsilon)
    simpa using h
  have hbound :=
    P1Full87ChangedRoughLevelObstruction.actual_full87_changed_rough_wpow_five_le
      delta n r q om N cap b
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) hw hb
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hpow :
      ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 =
        (N : ℝ) ^ (5 * epsilon ^ 2) := by
    calc
      ((N : ℝ) ^ (epsilon ^ 2)) ^ 5 =
          ((N : ℝ) ^ (epsilon ^ 2)) ^ (5 : ℝ) := by
            rw [Real.rpow_nat_cast]
      _ = (N : ℝ) ^ (epsilon ^ 2 * 5) :=
        (Real.rpow_mul hNnn (epsilon ^ 2) (5 : ℝ)).symm
      _ = (N : ℝ) ^ (5 * epsilon ^ 2) := by
        congr 1
        ring
  simpa only [hpow] using hbound

end
end ImbalancedChen.P1Full87CompactWScaleAudit
