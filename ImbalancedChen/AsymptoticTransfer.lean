import ImbalancedChen.Counting
import ImbalancedChen.Multiplicity
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Conditional asymptotic transfer on even integers

This file upgrades the exact finite transfer inequality to an eventual lower
bound. All analytic input remains explicit: a normalization `H` that is
eventually positive on even integers, an eventual lower estimate for the actual
count `D12` for every positive epsilon, and an eventual upper estimate for the
actual count `B` for every positive epsilon.

The coefficients `c` and `k` and the normalization `H` are arbitrary parameters.
No Chen estimate, sieve estimate, numerical analytic coefficient, or particular
normalization is established here. The conclusion holds for every strict
interior coefficient `delta < c - k`; it makes no endpoint claim. The eventual
statements use implications with `Even N`, so they do not assume the estimates
hold on odd integers.

The first results use the prime-or-semiprime receiver convention of
`Counting.lean`, which excludes the receiver `1`. The later `omega` results
instead accept a lower estimate for the manuscript's actual `D12Omega` count.
They absorb its possible extra receiver `1` using the explicit hypothesis that
for every positive epsilon, eventually on even integers `1 ≤ epsilon * H N`.
This is the required growth input; it is not asserted for any particular `H`.
-/

namespace ImbalancedChen

/-- Eventual epsilon bounds for the actual counts imply every strict interior
transfer coefficient on sufficiently large even integers.

The hypotheses are the analytic work needed by an application, not conclusions
about `D12` or `B` proved by this theorem. No divergence assumption on `H` is
needed for this exact finite counting convention. -/
theorem eventually_transfer_of_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hH : ∀ᶠ N in Filter.atTop, Even N → 0 < H N)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) :
    ∀ᶠ N in Filter.atTop, Even N → delta * H N ≤ (Db num den N : ℝ) := by
  let epsilon : ℝ := (c - k - delta) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hcoefficient : delta ≤ (c - epsilon) - (k + epsilon) := by
    dsimp [epsilon]
    linarith
  refine (hH.and ((hLower epsilon hepsilon).and (hUpper epsilon hepsilon))).mono ?_
  rintro N ⟨hHN, hLowerN, hUpperN⟩ hEven
  calc
    delta * H N ≤ ((c - epsilon) - (k + epsilon)) * H N :=
      mul_le_mul_of_nonneg_right hcoefficient (le_of_lt (hHN hEven))
    _ = (c - epsilon) * H N - (k + epsilon) * H N :=
      sub_mul (c - epsilon) (k + epsilon) (H N)
    _ ≤ (Db num den N : ℝ) := finite_transfer (hLowerN hEven) (hUpperN hEven)

/-- A positive strict interior transfer coefficient makes the natural-number
count positive on all sufficiently large even integers. Both analytic estimates
and eventual positivity of the normalization are still explicit hypotheses. -/
theorem eventually_Db_pos_of_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hH : ∀ᶠ N in Filter.atTop, Even N → 0 < H N)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) (hdelta_pos : 0 < delta) :
    ∀ᶠ N in Filter.atTop, Even N → 0 < Db num den N := by
  have hTransfer := eventually_transfer_of_bounds hH hLower hUpper hdelta
  refine (hH.and hTransfer).mono ?_
  rintro N ⟨hHN, hTransferN⟩ hEven
  have hreal : (0 : ℝ) < (Db num den N : ℝ) :=
    lt_of_lt_of_le (mul_pos hdelta_pos (hHN hEven)) (hTransferN hEven)
  exact_mod_cast hreal

/-- The same conditional bounds give an actual prime-indexed imbalanced
representation for every sufficiently large even integer when the chosen
interior coefficient is positive. This is conditional on the stated estimates
for the actual finite counts, and does not establish those analytic estimates. -/
theorem eventually_exists_imbalanced_of_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hH : ∀ᶠ N in Filter.atTop, Even N → 0 < H N)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) (hdelta_pos : 0 < delta) :
    ∀ᶠ N in Filter.atTop, Even N →
      ∃ p : ℕ, p < N ∧ Nat.Prime p ∧ ImbalancedReceiver num den (N - p) := by
  refine (eventually_Db_pos_of_bounds hH hLower hUpper hdelta hdelta_pos).mono ?_
  intro N hN hEven
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (hN hEven)
  exact ⟨p, mem_imbalancedPrimes.mp hp⟩

/-- The explicit unit-absorption hypothesis entails eventual positivity of the
normalization on even integers. This does not assert growth of a particular
normalization. -/
theorem eventually_normalization_pos_of_unit_absorption
    {H : ℕ → ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N) :
    ∀ᶠ N in Filter.atTop, Even N → 0 < H N := by
  refine (hAbsorb 1 (by norm_num)).mono ?_
  intro N hN hEven
  have hOne : (1 : ℝ) ≤ H N := by
    simpa only [one_mul] using hN hEven
  linarith

/-- A lower estimate for the manuscript's `D12Omega` gives the corresponding
epsilon lower estimate for `D12` once the possible receiver-one contribution
can be absorbed into the normalization.

The hypothesis `hAbsorb` explicitly supplies the growth needed to discard an
additive constant. The proof uses the finite correction from `Multiplicity`;
the two counting conventions are never identified without this correction. -/
theorem eventually_D12_lower_of_omega_lower
    {H : ℕ → ℝ} {c : ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12Omega N : ℝ)) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12 N : ℝ) := by
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  refine ((hLowerOmega (epsilon / 2) hhalf).and
    (hAbsorb (epsilon / 2) hhalf)).mono ?_
  rintro N ⟨hLowerN, hAbsorbN⟩ hEven
  have hCorrection : (D12Omega N : ℝ) - 1 ≤ (D12 N : ℝ) := by
    have hCast : (D12Omega N : ℝ) ≤ (D12 N : ℝ) + 1 := by
      exact_mod_cast D12Omega_le_D12_add_one N
    linarith only [hCast]
  calc
    (c - epsilon) * H N =
        (c - epsilon / 2) * H N - (epsilon / 2) * H N := by ring
    _ ≤ (D12Omega N : ℝ) - 1 := sub_le_sub (hLowerN hEven) (hAbsorbN hEven)
    _ ≤ (D12 N : ℝ) := hCorrection

/-- Conditional asymptotic transfer from the manuscript's actual `D12Omega`
count, including the receiver-one correction.

Every analytic premise is explicit: the lower estimate for `D12Omega`, the
upper estimate for `B`, and eventual absorption of `1` by every positive
multiple of `H`. The last premise supplies both the growth needed by the
correction and eventual positivity of `H`. -/
theorem eventually_transfer_of_omega_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) :
    ∀ᶠ N in Filter.atTop, Even N → delta * H N ≤ (Db num den N : ℝ) := by
  exact eventually_transfer_of_bounds
    (eventually_normalization_pos_of_unit_absorption hAbsorb)
    (eventually_D12_lower_of_omega_lower hAbsorb hLowerOmega) hUpper hdelta

/-- The corrected manuscript-count transfer gives a positive natural-number
count for every sufficiently large even integer when the chosen strict
interior coefficient is positive. All analytic and growth inputs are stated
as hypotheses. -/
theorem eventually_Db_pos_of_omega_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) (hdelta_pos : 0 < delta) :
    ∀ᶠ N in Filter.atTop, Even N → 0 < Db num den N := by
  exact eventually_Db_pos_of_bounds
    (eventually_normalization_pos_of_unit_absorption hAbsorb)
    (eventually_D12_lower_of_omega_lower hAbsorb hLowerOmega) hUpper hdelta hdelta_pos

/-- Conditional existence of an imbalanced representation from lower bounds
for the manuscript's `D12Omega`, upper bounds for `B`, and explicit growth of
the normalization sufficient to absorb the receiver-one correction. -/
theorem eventually_exists_imbalanced_of_omega_bounds
    {num den : ℕ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hAbsorb : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → 1 ≤ epsilon * H N)
    (hLowerOmega : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (c - epsilon) * H N ≤ (D12Omega N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N → (B num den N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) (hdelta_pos : 0 < delta) :
    ∀ᶠ N in Filter.atTop, Even N →
      ∃ p : ℕ, p < N ∧ Nat.Prime p ∧ ImbalancedReceiver num den (N - p) := by
  exact eventually_exists_imbalanced_of_bounds
    (eventually_normalization_pos_of_unit_absorption hAbsorb)
    (eventually_D12_lower_of_omega_lower hAbsorb hLowerOmega) hUpper hdelta hdelta_pos

end ImbalancedChen
