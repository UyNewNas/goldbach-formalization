import ImbalancedChen.Multiplicity
import ImbalancedChen.CurrentMainTheorem
import ImbalancedChen.AsymptoticTransfer
import ImbalancedChen.SingularSeries

/-!
# P6: the exact unit correction for a fixed real exponent

Source-only draft, 24 October 2026. This file has not been compiled.
Dependency source hashes and the draft source hash are recorded in the adjacent
`P6RealUnitCorrection.CP.json`. The statements below use the actual finite
counts and leave every analytic count estimate as an explicit hypothesis.

For every real `b`, the omega convention includes the unit receiver precisely
when `N - 1` is prime. The real imbalanced receiver predicate excludes that
receiver. The correction is therefore retained before passing to asymptotic
bounds. Eventual transfer reuses the existing unit-absorption argument; this
file does not establish a new lower count estimate or upper sieve estimate.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Receiver one is excluded for every real exponent, without a restriction
on its sign or size. -/
@[simp] theorem not_realImbalancedReceiver_one (b : ℝ) :
    ¬ RealImbalancedReceiver b 1 := by
  intro h
  exact not_primeOrSemiprime_one h.primeOrSemiprime

/-- No additive prime with receiver one contributes to `RealDb`. -/
theorem realImbalancedPrimes_disjoint_unitReceiverPrimes (b : ℝ) (N : ℕ) :
    Disjoint (realImbalancedPrimes b N) (unitReceiverPrimes N) := by
  apply Finset.disjoint_left.mpr
  intro p hgood hunit
  have hreceiver := (mem_realImbalancedPrimes.mp hgood).2.2
  have hone := (mem_unitReceiverPrimes.mp hunit).2.2
  rw [hone] at hreceiver
  exact not_realImbalancedReceiver_one b hreceiver

/-- The exact set partition retains the separate unit receiver for every
fixed real exponent. Each set is indexed by additive primes. -/
theorem omegaChenPrimes_eq_real_union_unit (b : ℝ) (N : ℕ) :
    omegaChenPrimes N =
      (realImbalancedPrimes b N ∪ realBadPrimes b N) ∪ unitReceiverPrimes N := by
  rw [omegaChenPrimes_eq_chenPrimes_union, chenPrimes_eq_real_union b N]

/-- The omega count is the real accepted count, its exact bad complement,
and precisely the possible unit contribution. No exponent hypothesis is used. -/
theorem D12Omega_eq_RealDb_add_RealB_add_indicator (b : ℝ) (N : ℕ) :
    D12Omega N = RealDb b N + RealB b N +
      (if Nat.Prime (N - 1) then 1 else 0) := by
  rw [D12Omega_eq_D12_add_indicator, D12_eq_RealDb_add_RealB b N]

/-- Natural subtraction is exact here because the preceding partition
supplies the full sum identity. -/
theorem RealDb_eq_D12Omega_sub_RealB_sub_indicator (b : ℝ) (N : ℕ) :
    RealDb b N = D12Omega N - RealB b N -
      (if Nat.Prime (N - 1) then 1 else 0) := by
  have h := D12Omega_eq_RealDb_add_RealB_add_indicator b N
  omega

/-- Real subtraction comes from casting the sum identity, so it does not
silently replace truncated natural subtraction by real subtraction. -/
theorem RealDb_cast_eq_D12Omega_sub_RealB_sub_indicator (b : ℝ) (N : ℕ) :
    (RealDb b N : ℝ) = (D12Omega N : ℝ) - (RealB b N : ℝ) -
      ((if Nat.Prime (N - 1) then (1 : ℕ) else 0) : ℝ) := by
  have h := congrArg (fun n : ℕ => (n : ℝ))
    (D12Omega_eq_RealDb_add_RealB_add_indicator b N)
  simp only [Nat.cast_add] at h
  linarith only [h]

/-- The same exact subtraction formula with a real-valued indicator. -/
theorem RealDb_cast_eq_D12Omega_sub_RealB_sub_real_indicator (b : ℝ) (N : ℕ) :
    (RealDb b N : ℝ) = (D12Omega N : ℝ) - (RealB b N : ℝ) -
      (if Nat.Prime (N - 1) then (1 : ℝ) else 0) := by
  classical
  by_cases hp : Nat.Prime (N - 1) <;>
    simpa [hp] using
      (RealDb_cast_eq_D12Omega_sub_RealB_sub_indicator b N)

/-- Finite transfer for a fixed arbitrary real exponent, with the exact unit
indicator still present in the conclusion. -/
theorem finite_real_transfer_of_omega_bounds
    {b : ℝ} {N : ℕ} {lower upper : ℝ}
    (hLowerOmega : lower ≤ (D12Omega N : ℝ))
    (hUpper : (RealB b N : ℝ) ≤ upper) :
    lower - upper - (if Nat.Prime (N - 1) then (1 : ℝ) else 0) ≤
      (RealDb b N : ℝ) := by
  rw [RealDb_cast_eq_D12Omega_sub_RealB_sub_real_indicator b N]
  linarith only [hLowerOmega, hUpper]

/-- A convenient finite consequence with the full possible unit loss.
This inequality does not assert that receiver one contributes to `RealDb`. -/
theorem finite_real_transfer_of_omega_bounds_sub_one
    {b : ℝ} {N : ℕ} {lower upper : ℝ}
    (hLowerOmega : lower ≤ (D12Omega N : ℝ))
    (hUpper : (RealB b N : ℝ) ≤ upper) :
    lower - upper - 1 ≤ (RealDb b N : ℝ) := by
  classical
  have hUnit : (if Nat.Prime (N - 1) then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hTransfer := finite_real_transfer_of_omega_bounds hLowerOmega hUpper
  linarith only [hUnit, hTransfer]

/-- Conditional eventual transfer from the manuscript omega count for a
fixed arbitrary real exponent. The existing absorption bridge converts the
omega lower estimate to the `D12` estimate before real-exponent transfer. -/
theorem eventually_real_transfer_of_omega_bounds
    {b : ℝ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (c - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) :
    ∀ᶠ N in Filter.atTop, Even N →
      delta * H N ≤ (RealDb b N : ℝ) := by
  exact ImbalancedChen.eventually_real_transfer_of_bounds
    (eventually_normalization_pos_of_unit_absorption hAbsorb)
    (eventually_D12_lower_of_omega_lower hAbsorb hLowerOmega) hUpper hdelta

/-- The concrete manuscript normalization supplies unit absorption through
the already proved singular-series result. Both analytic count bounds remain
hypotheses, and only a strict interior transfer coefficient is concluded. -/
theorem eventually_real_transfer_of_singular_omega_bounds
    {b : ℝ} {c k delta : ℝ}
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (c - epsilon) * singularNormalization N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤ (k + epsilon) * singularNormalization N)
    (hdelta : delta < c - k) :
    ∀ᶠ N in Filter.atTop, Even N →
      delta * singularNormalization N ≤ (RealDb b N : ℝ) := by
  exact eventually_real_transfer_of_omega_bounds
    eventuallyEven_singularNormalization_unit_absorption hLowerOmega hUpper hdelta

end

end ImbalancedChen.P6
