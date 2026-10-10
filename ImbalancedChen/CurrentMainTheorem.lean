import ImbalancedChen.CurrentNumericalTransfer
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Current real-exponent main theorem interface

This file gives the exact finite complement count for an arbitrary real
exponent and states the 10 October 2026 main theorem with its literal
even-integer lower-limit quantifier.  The conclusion is conditional only on
the two analytic estimates still missing from the formalization: the current
`D12` lower bound and the real-exponent bad-count upper bound.

The lower limit is taken in `EReal`.  This avoids imposing an artificial global
boundedness hypothesis on the normalized count merely to use the conditionally
complete real-valued `Filter.liminf`.  Since the claimed lower bound is finite,
the statement has the standard mathematical meaning.
-/

namespace ImbalancedChen

noncomputable section

/-- The complement of the accepted real-exponent receiver condition inside
the prime-or-semiprime receivers. -/
def RealBadReceiver (b : ℝ) (m : ℕ) : Prop :=
  PrimeOrSemiprime m ∧ ¬ RealImbalancedReceiver b m

theorem RealImbalancedReceiver.primeOrSemiprime {b : ℝ} {m : ℕ}
    (h : RealImbalancedReceiver b m) : PrimeOrSemiprime m := by
  rcases h with hprime | ⟨r, q, hr, hq, hm, _⟩
  · exact Or.inl hprime
  · exact Or.inr ⟨r, q, hr, hq, hm⟩

/-- Additive primes in the real-exponent complement, indexed only by the
additive prime and hence counted without factor-witness multiplicity. -/
def realBadPrimes (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p =>
    Nat.Prime p ∧ RealBadReceiver b (N - p)

/-- Real-exponent bad-representation count. -/
def RealB (b : ℝ) (N : ℕ) : ℕ := (realBadPrimes b N).card

@[simp] theorem mem_realBadPrimes {b : ℝ} {N p : ℕ} :
    p ∈ realBadPrimes b N ↔
      p < N ∧ Nat.Prime p ∧ PrimeOrSemiprime (N - p) ∧
        ¬ RealImbalancedReceiver b (N - p) := by
  classical
  unfold realBadPrimes RealBadReceiver
  simp only [Finset.mem_filter, Finset.mem_range]

/-- At a rational exponent, the new arbitrary-real complement is exactly the
existing decidable integer-power complement. -/
theorem badPrimes_eq_realBadPrimes {num den N : ℕ} (hden : 0 < den) :
    badPrimes num den N =
      realBadPrimes ((num : ℝ) / (den : ℝ)) N := by
  classical
  ext p
  rw [mem_badPrimes, mem_realBadPrimes,
    ← imbalancedReceiver_iff_realImbalancedReceiver hden]

theorem B_eq_RealB {num den N : ℕ} (hden : 0 < den) :
    B num den N = RealB ((num : ℝ) / (den : ℝ)) N := by
  unfold B RealB
  rw [badPrimes_eq_realBadPrimes hden]

theorem realImbalancedPrimes_subset_chenPrimes (b : ℝ) (N : ℕ) :
    realImbalancedPrimes b N ⊆ chenPrimes N := by
  intro p hp
  rcases mem_realImbalancedPrimes.mp hp with ⟨hpN, hpprime, hreceiver⟩
  exact mem_chenPrimes.mpr ⟨hpN, hpprime, hreceiver.primeOrSemiprime⟩

theorem realBadPrimes_subset_chenPrimes (b : ℝ) (N : ℕ) :
    realBadPrimes b N ⊆ chenPrimes N := by
  intro p hp
  rcases mem_realBadPrimes.mp hp with ⟨hpN, hpprime, hreceiver, _⟩
  exact mem_chenPrimes.mpr ⟨hpN, hpprime, hreceiver⟩

theorem realImbalancedPrimes_disjoint_realBadPrimes (b : ℝ) (N : ℕ) :
    Disjoint (realImbalancedPrimes b N) (realBadPrimes b N) := by
  apply Finset.disjoint_left.mpr
  intro p hgood hbad
  exact (mem_realBadPrimes.mp hbad).2.2.2
    (mem_realImbalancedPrimes.mp hgood).2.2

/-- Exact finite partition for every real exponent. -/
theorem chenPrimes_eq_real_union (b : ℝ) (N : ℕ) :
    chenPrimes N = realImbalancedPrimes b N ∪ realBadPrimes b N := by
  classical
  ext p
  rw [Finset.mem_union, mem_chenPrimes, mem_realImbalancedPrimes,
    mem_realBadPrimes]
  constructor
  · rintro ⟨hpN, hpprime, hreceiver⟩
    by_cases hgood : RealImbalancedReceiver b (N - p)
    · exact Or.inl ⟨hpN, hpprime, hgood⟩
    · exact Or.inr ⟨hpN, hpprime, hreceiver, hgood⟩
  · rintro (⟨hpN, hpprime, hgood⟩ | ⟨hpN, hpprime, hreceiver, _⟩)
    · exact ⟨hpN, hpprime, hgood.primeOrSemiprime⟩
    · exact ⟨hpN, hpprime, hreceiver⟩

/-- The current count splits exactly for an arbitrary fixed real exponent. -/
theorem D12_eq_RealDb_add_RealB (b : ℝ) (N : ℕ) :
    D12 N = RealDb b N + RealB b N := by
  unfold D12 RealDb RealB
  rw [chenPrimes_eq_real_union b N]
  exact Finset.card_union_of_disjoint
    (realImbalancedPrimes_disjoint_realBadPrimes b N)

theorem RealDb_cast_eq_D12_sub_RealB (b : ℝ) (N : ℕ) :
    (RealDb b N : ℝ) = (D12 N : ℝ) - (RealB b N : ℝ) := by
  have h : (D12 N : ℝ) = (RealDb b N : ℝ) + (RealB b N : ℝ) := by
    exact_mod_cast D12_eq_RealDb_add_RealB b N
  linarith

/-- Finite real-exponent transfer with all analytic information supplied as
ordinary inequalities. -/
theorem finite_real_transfer {b : ℝ} {N : ℕ} {lower upper : ℝ}
    (hLower : lower ≤ (D12 N : ℝ))
    (hUpper : (RealB b N : ℝ) ≤ upper) :
    lower - upper ≤ (RealDb b N : ℝ) := by
  rw [RealDb_cast_eq_D12_sub_RealB b N]
  linarith

/-- Eventual transfer for an arbitrary fixed real exponent. -/
theorem eventually_real_transfer_of_bounds
    {b : ℝ} {H : ℕ → ℝ} {c k delta : ℝ}
    (hH : ∀ᶠ N in Filter.atTop, Even N → 0 < H N)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (c - epsilon) * H N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤ (k + epsilon) * H N)
    (hdelta : delta < c - k) :
    ∀ᶠ N in Filter.atTop, Even N →
      delta * H N ≤ (RealDb b N : ℝ) := by
  let epsilon : ℝ := (c - k - delta) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hcoefficient : delta ≤ (c - epsilon) - (k + epsilon) := by
    dsimp [epsilon]
    linarith
  refine (hH.and ((hLower epsilon hepsilon).and
    (hUpper epsilon hepsilon))).mono ?_
  rintro N ⟨hHN, hLowerN, hUpperN⟩ hEven
  calc
    delta * H N ≤ ((c - epsilon) - (k + epsilon)) * H N :=
      mul_le_mul_of_nonneg_right hcoefficient (hHN hEven).le
    _ = (c - epsilon) * H N - (k + epsilon) * H N := by ring
    _ ≤ (RealDb b N : ℝ) :=
      finite_real_transfer (hLowerN hEven) (hUpperN hEven)

/-- The filter for natural numbers tending to infinity through all even
values. -/
def evenNatAtTop : Filter ℕ :=
  Filter.atTop ⊓ Filter.principal {N : ℕ | Even N}

theorem evenNatAtTop_neBot : evenNatAtTop.NeBot := by
  rw [evenNatAtTop, Filter.inf_principal_neBot_iff]
  intro U hU
  obtain ⟨a, ha⟩ := (Filter.mem_atTop_sets.mp hU)
  refine ⟨2 * a, ha (2 * a) (by omega), ?_⟩
  exact ⟨a, by omega⟩

/-- The epsilon/eventual lower-bound formulation implies the literal extended
real lower limit along all even natural numbers. -/
theorem ereal_le_even_liminf_of_eventually_ge
    {u : ℕ → ℝ} {L : ℝ}
    (h : ∀ delta : ℝ, delta < L →
      ∀ᶠ N : ℕ in Filter.atTop, Even N → delta ≤ u N) :
    (L : EReal) ≤ Filter.liminf (fun N : ℕ => (u N : EReal)) evenNatAtTop := by
  rw [Filter.le_liminf_iff]
  intro y hy
  obtain ⟨delta, hy_delta, hdelta_L⟩ := EReal.exists_between_coe_real hy
  have hdelta : delta < L := EReal.coe_lt_coe_iff.mp hdelta_L
  rw [evenNatAtTop, Filter.eventually_inf_principal]
  filter_upwards [h delta hdelta] with N hN
  intro hEven
  exact hy_delta.trans_le (EReal.coe_le_coe_iff.mpr (hN hEven))

/-- Conditional exact form of Theorem 1.1 for the 10 October 2026 manuscript.

The hypotheses preserve the fixed-exponent quantifier: `b` is chosen first,
with `1/2 < b < 1`, and both analytic estimates hold along every sufficiently
large even `N` for every positive epsilon.  `RealDb` counts distinct additive
primes, `RealB` is its exact complement in `D12`, and the denominator is the
manuscript normalization without an extra factor two. -/
theorem current_theorem_1_1_of_manuscript_bounds
    {b : ℝ} (hbLower : (1 : ℝ) / 2 < b) (hbUpper : b < 1)
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (RealB b N : ℝ) ≤
          (currentK * Real.log (1 / b) + epsilon) *
            singularNormalization N) :
    ((currentC - currentK * Real.log (1 / b) : ℝ) : EReal) ≤
      Filter.liminf
        (fun N : ℕ =>
          (((RealDb b N : ℝ) / singularNormalization N : ℝ) : EReal))
        evenNatAtTop := by
  have _hb : (1 : ℝ) / 2 < b ∧ b < 1 := ⟨hbLower, hbUpper⟩
  apply ereal_le_even_liminf_of_eventually_ge
  intro delta hdelta
  have hTransfer := eventually_real_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    hLower hUpper hdelta
  refine (eventually_singularNormalization_pos.and hTransfer).mono ?_
  rintro N ⟨hH, hN⟩ hEven
  exact (le_div_iff₀ hH).2 (hN hEven)

end

end ImbalancedChen
