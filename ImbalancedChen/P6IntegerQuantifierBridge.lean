import ImbalancedChen.CurrentMainTheorem

/-!
# P6: the literal even-integer quantifier

SOURCEONLY / UNCOMPILED candidate, 2026-10-24.
Source anchor: ImbalancedChen/CurrentMainTheorem.lean
SHA256: 68A2A3AAD8CCDC73ED8E5076E31B9984BC659C307D71150920A71B5FC98F067D

These bridges concern arbitrary predicates on natural numbers.  They explain
why the existing `ImbalancedChen.evenNatAtTop` expresses all sufficiently
large even integers, and why the sequence `2 * k` gives the same eventual
quantifier.  No analytic estimate or lower-limit theorem is assumed here.
-/

namespace ImbalancedChen.P6

/-- Casting a natural number to the integers preserves and reflects parity. -/
theorem even_natCast_iff (n : ℕ) : Even (n : ℤ) ↔ Even n := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k.toNat, ?_⟩
    omega
  · rintro ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    omega

/-- On nonnegative integers, `toNat` preserves and reflects parity.
The sign hypothesis is essential because every negative integer has `toNat = 0`. -/
theorem even_toNat_iff_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    Even z.toNat ↔ Even z := by
  have hcast : (z.toNat : ℤ) = z := by omega
  calc
    Even z.toNat ↔ Even (z.toNat : ℤ) := (even_natCast_iff z.toNat).symm
    _ ↔ Even z := by rw [hcast]

/-- The natural threshold quantifier is exactly the manuscript's literal
integer threshold quantifier.  In the forward direction the chosen integer
threshold is nonnegative, so no truncation occurs in `toNat`. -/
theorem nat_even_threshold_iff_int_even_threshold (P : ℕ → Prop) :
    (∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N → P N) ↔
      (∃ Z0 : ℤ, ∀ Z : ℤ, Z0 ≤ Z → Even Z → P Z.toNat) := by
  constructor
  · rintro ⟨N0, hN0⟩
    refine ⟨(N0 : ℤ), ?_⟩
    intro Z hZ hEven
    have hnonneg : 0 ≤ Z := by omega
    have hbound : N0 ≤ Z.toNat := by omega
    exact hN0 Z.toNat hbound ((even_toNat_iff_of_nonneg hnonneg).mpr hEven)
  · rintro ⟨Z0, hZ0⟩
    refine ⟨Z0.toNat, ?_⟩
    intro N hN hEven
    have hbound : Z0 ≤ (N : ℤ) := by omega
    have hEvenInt : Even (N : ℤ) := (even_natCast_iff N).mpr hEven
    simpa using hZ0 (N : ℤ) hbound hEvenInt

/-- One may require the integer threshold itself to be nonnegative without
changing the meaning of 'all sufficiently large even integers'. -/
theorem nat_even_threshold_iff_nonneg_int_even_threshold (P : ℕ → Prop) :
    (∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N → P N) ↔
      (∃ Z0 : ℤ, 0 ≤ Z0 ∧
        ∀ Z : ℤ, Z0 ≤ Z → Even Z → P Z.toNat) := by
  constructor
  · rintro ⟨N0, hN0⟩
    refine ⟨(N0 : ℤ), by omega, ?_⟩
    intro Z hZ hEven
    have hnonneg : 0 ≤ Z := by omega
    have hbound : N0 ≤ Z.toNat := by omega
    exact hN0 Z.toNat hbound ((even_toNat_iff_of_nonneg hnonneg).mpr hEven)
  · rintro ⟨Z0, _, hZ0⟩
    exact (nat_even_threshold_iff_int_even_threshold P).mpr ⟨Z0, hZ0⟩

/-- Explicit cofinality of the even subsequence: a threshold for all even
naturals exists exactly when a threshold for the indices of `2 * k` exists. -/
theorem nat_even_threshold_iff_double_threshold (P : ℕ → Prop) :
    (∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N → P N) ↔
      (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → P (2 * k)) := by
  constructor
  · rintro ⟨N0, hN0⟩
    refine ⟨N0, ?_⟩
    intro k hk
    apply hN0 (2 * k) (by omega)
    exact ⟨k, by omega⟩
  · rintro ⟨k0, hk0⟩
    refine ⟨2 * k0, ?_⟩
    intro N hN hEven
    rcases hEven with ⟨k, hk⟩
    have hbound : k0 ≤ k := by omega
    have hdouble : N = 2 * k := by omega
    rw [hdouble]
    exact hk0 k hbound

/-- The existing filter has precisely the natural even-threshold quantifier. -/
theorem eventually_evenNatAtTop_iff_nat_threshold (P : ℕ → Prop) :
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, P N) ↔
      (∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → Even N → P N) := by
  rw [ImbalancedChen.evenNatAtTop, Filter.eventually_inf_principal]
  exact Filter.eventually_atTop

/-- Literal integer thresholds characterize eventual truth in `evenNatAtTop`. -/
theorem eventually_evenNatAtTop_iff_int_threshold (P : ℕ → Prop) :
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, P N) ↔
      (∃ Z0 : ℤ, ∀ Z : ℤ, Z0 ≤ Z → Even Z → P Z.toNat) := by
  exact (eventually_evenNatAtTop_iff_nat_threshold P).trans
    (nat_even_threshold_iff_int_even_threshold P)

/-- A nonnegative integer threshold may be used for the existing even filter. -/
theorem eventually_evenNatAtTop_iff_nonneg_int_threshold (P : ℕ → Prop) :
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, P N) ↔
      (∃ Z0 : ℤ, 0 ≤ Z0 ∧
        ∀ Z : ℤ, Z0 ≤ Z → Even Z → P Z.toNat) := by
  exact (eventually_evenNatAtTop_iff_nat_threshold P).trans
    (nat_even_threshold_iff_nonneg_int_even_threshold P)

/-- A threshold on the indices of the even subsequence characterizes the
existing filter. -/
theorem eventually_evenNatAtTop_iff_double_threshold (P : ℕ → Prop) :
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, P N) ↔
      (∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → P (2 * k)) := by
  exact (eventually_evenNatAtTop_iff_nat_threshold P).trans
    (nat_even_threshold_iff_double_threshold P)

/-- Ordinary eventual truth along `2 * k` is equivalent to eventual truth on
all even naturals; there is no restriction to a thinner subsequence. -/
theorem eventually_evenNatAtTop_iff_eventually_double (P : ℕ → Prop) :
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, P N) ↔
      (∀ᶠ k : ℕ in Filter.atTop, P (2 * k)) := by
  rw [Filter.eventually_atTop]
  exact eventually_evenNatAtTop_iff_double_threshold P

/-- The implication formulation on natural `atTop` agrees with the same
implication formulation on integer `atTop`. -/
theorem eventually_nat_even_iff_eventually_int_even (P : ℕ → Prop) :
    (∀ᶠ N : ℕ in Filter.atTop, Even N → P N) ↔
      (∀ᶠ Z : ℤ in Filter.atTop, Even Z → P Z.toNat) := by
  rw [Filter.eventually_atTop, Filter.eventually_atTop]
  exact nat_even_threshold_iff_int_even_threshold P

/-- The map of the full index filter under the even enumeration is exactly
the existing filter through all even naturals. -/
theorem map_double_atTop_eq_evenNatAtTop :
    Filter.map (fun k : ℕ => 2 * k) Filter.atTop =
      ImbalancedChen.evenNatAtTop := by
  apply Filter.ext
  intro s
  change (∀ᶠ N in Filter.map (fun k : ℕ => 2 * k) Filter.atTop, N ∈ s) ↔
    (∀ᶠ N in ImbalancedChen.evenNatAtTop, N ∈ s)
  rw [Filter.eventually_map]
  exact (eventually_evenNatAtTop_iff_eventually_double (fun N => N ∈ s)).symm

/-- The literal even lower limit and the lower limit of the ordinary even
sequence coincide for every extended-real function, without boundedness or
analytic hypotheses.  The pinned Mathlib map API is named `liminf_comp`. -/
theorem liminf_evenNatAtTop_eq_liminf_double (u : ℕ → EReal) :
    Filter.liminf u ImbalancedChen.evenNatAtTop =
      Filter.liminf (fun k : ℕ => u (2 * k)) Filter.atTop := by
  rw [← map_double_atTop_eq_evenNatAtTop]
  simpa only [Function.comp_def] using
    (Filter.liminf_comp u (fun k : ℕ => 2 * k) Filter.atTop).symm

end ImbalancedChen.P6
