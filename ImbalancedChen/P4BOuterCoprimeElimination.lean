import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4B: eliminate the outer-source coprime correction

SOURCE-ONLY / YELLOW / UNCOMPILED.

This supplies the exact hcoprime slot of P4BActualOuterUpperAssembly.
Roughness is required only where the actual outer weight is nonzero.
All finite identities permit signed weights and arbitrary zero extension.
No roughness of an arbitrary outer envelope is inferred from the roughness
of the smaller curved source; the outer-support premise is explicit.
-/

namespace ImbalancedChen.P4BOuterCoprimeElimination

noncomputable section
open Filter Topology
open scoped BigOperators

/-- Prime-divisor roughness excludes every prime in the actual sieve
product. No factorization model, positivity of m, or squarefreeness of m
is needed. -/
theorem coprime_sieveProduct_of_prime_divisor_rough
    (N z m : ℕ) (R : ℝ) (hgate : (z : ℝ) ≤ R)
    (hrough : ∀ ell : ℕ, Nat.Prime ell → ell ∣ m → R < (ell : ℝ)) :
    Nat.Coprime m (sieveProduct N z) := by
  classical
  unfold sieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro ell hell
  obtain ⟨hellz, hp, _hnot⟩ := mem_sievePrimes.mp hell
  apply (hp.coprime_iff_not_dvd.mpr ?_).symm
  intro hdvd
  have hellzR : (ell : ℝ) < (z : ℝ) := Nat.cast_lt.mpr hellz
  exact (not_lt_of_ge (hellzR.le.trans hgate)) (hrough ell hp hdvd)

/-- A coprime mask may be removed whenever it contains the nonzero
support of the weight. Signed weights and exterior zero values are allowed. -/
theorem finiteCoprimeMass_eq_sourceMass_of_weight_support
    (S : Finset ℕ) (weight : ℕ → ℝ) (d : ℕ)
    (hcoprime : ∀ m ∈ S, weight m ≠ 0 → Nat.Coprime m d) :
    finiteCoprimeMass S weight d = finiteSourceMass S weight := by
  classical
  simp only [finiteCoprimeMass, finiteSourceMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hzero : weight m = 0
  · simp only [hzero, ite_self]
  · rw [if_pos (hcoprime m hm hzero)]

/-- For a signed physical coefficient, only active coefficient moduli
need the support condition. Each corresponding correction term is zero. -/
theorem signed_coprime_sum_eq_zero_of_active_weight_support
    (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hcoprime : ∀ d ∈ Q, rho d ≠ 0 →
      ∀ m ∈ S, weight m ≠ 0 → Nat.Coprime m d) :
    (∑ d ∈ Q, rho d *
      ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
        (Nat.totient d : ℝ))) = 0 := by
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hzero : rho d = 0
  · simp only [hzero, zero_mul]
  · rw [finiteCoprimeMass_eq_sourceMass_of_weight_support S weight d
      (hcoprime d hd hzero)]
    simp only [sub_self, zero_div, mul_zero]

/-- The real roughness threshold controls every displayed attached
modulus through the proved exact sieve-product support inclusion. -/
theorem coprime_attachedModulus_of_prime_divisor_rough
    {nu r epsilon R : ℝ} (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N m d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ R)
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N)
    (hrough : ∀ ell : ℕ, Nat.Prime ell → ell ∣ m → R < (ell : ℝ)) :
    Nat.Coprime m d := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hdvd : d ∣ sieveProduct N (Nat.ceil ((N : ℝ) ^ (nu * r))) :=
    actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
      (Real.rpow_le_rpow_of_exponent_le hNreal
        (mul_le_mul_of_nonneg_left hepsilonR hnu.le)) hd
  exact (coprime_sieveProduct_of_prime_divisor_rough N _ m R hgate hrough).of_dvd_right hdvd

/-- Exact mass identity for the outer carrier, with roughness imposed
only on nonzero outer weights. The carrier may contain zero-weight points
with arbitrary prime divisors. -/
theorem outer_coprimeMass_eq_sourceMass_of_prime_divisor_rough
    {nu r epsilon R : ℝ} (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N d : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ R)
    (S : Finset ℕ) (weight : ℕ → ℝ)
    (hrough : ∀ m ∈ S, weight m ≠ 0 →
      ∀ ell : ℕ, Nat.Prime ell → ell ∣ m → R < (ell : ℝ))
    (hd : d ∈ attachedUpperModuli nu r epsilon retain cap N) :
    finiteCoprimeMass S weight d = finiteSourceMass S weight := by
  apply finiteCoprimeMass_eq_sourceMass_of_weight_support S weight d
  intro m hm hweight
  exact coprime_attachedModulus_of_prime_divisor_rough hnu hepsilonR
    retain cap hN hgate hd (hrough m hm hweight)

/-- The entire same-rho signed outer coprime sum vanishes exactly; no
absolute-value or density estimate is used to establish this identity. -/
theorem outer_signed_coprime_sum_eq_zero_of_prime_divisor_rough
    {nu r epsilon R : ℝ} (hnu : 0 < nu) (hepsilonR : epsilon ^ 2 ≤ r)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N : ℕ} (hN : 1 ≤ N)
    (hgate : (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) ≤ R)
    (S : Finset ℕ) (weight : ℕ → ℝ)
    (hrough : ∀ m ∈ S, weight m ≠ 0 →
      ∀ ell : ℕ, Nat.Prime ell → ell ∣ m → R < (ell : ℝ)) :
    (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ))) = 0 := by
  apply signed_coprime_sum_eq_zero_of_active_weight_support
    S (attachedUpperModuli nu r epsilon retain cap N) weight
    (attachedUpperCoefficient nu r epsilon retain cap N)
  intro d hd _hactive m hm hweight
  exact coprime_attachedModulus_of_prime_divisor_rough hnu hepsilonR
    retain cap hN hgate hd (hrough m hm hweight)

/-- The literal manuscript gate gives exact outer mass identities and
zero signed correction on all sufficiently large even targets, provided
the nonzero outer support obeys the same manuscript roughness threshold. -/
theorem eventually_outer_coprime_identities_of_manuscript_roughness
    {b kappa nu r epsilon : ℝ} (hb : 0 < b) (hnu : 0 < nu)
    (hr : 0 ≤ r) (hepsilonR : epsilon ^ 2 ≤ r)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (S : ℕ → Finset ℕ) (weight : ℕ → ℕ → ℝ)
    (hrough : ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S N, weight N m ≠ 0 →
        ∀ ell : ℕ, Nat.Prime ell → ell ∣ m →
          (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) < (ell : ℝ)) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (∀ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        finiteCoprimeMass (S N) (weight N) d = finiteSourceMass (S N) (weight N)) ∧
      (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          ((finiteCoprimeMass (S N) (weight N) d - finiteSourceMass (S N) (weight N)) /
            (Nat.totient d : ℝ))) = 0 := by
  filter_upwards [eventually_manuscript_sieve_gate hb (mul_nonneg hnu.le hr) hgap,
    eventually_ge_atTop (1 : ℕ), hrough] with N hgate hN hroughN
  intro hEven
  constructor
  · intro d hd
    exact outer_coprimeMass_eq_sourceMass_of_prime_divisor_rough hnu hepsilonR
      retain cap hN hgate.2 (S N) (weight N) (hroughN hEven) hd
  · exact outer_signed_coprime_sum_eq_zero_of_prime_divisor_rough hnu hepsilonR
      retain cap hN hgate.2 (S N) (weight N) (hroughN hEven)

/-- Drop-in supplier for the hcoprime argument of
P4B.eventually_RealB_le_of_actual_outer_primitive_inputs. It uses the same
delta-indexed S, weight, attached support, and attached coefficient.
The coprime estimate follows from an exact zero identity, not from a new
analytic hypothesis. -/
theorem actual_outer_hcoprime_of_manuscript_roughness
    {b kappa nu r : ℝ} (hb : 0 < b) (hnu : 0 < nu) (hr : 0 ≤ r)
    (hgap : nu * r < (1 - kappa) * (b / (1 + b)))
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (S : ℝ → ℕ → Finset ℕ) (weight : ℝ → ℕ → ℕ → ℝ)
    (hepsilonR : ∀ delta : ℝ, 0 < delta → (epsilon delta) ^ 2 ≤ r)
    (hrough : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S delta N, weight delta N m ≠ 0 →
        ∀ ell : ℕ, Nat.Prime ell → ell ∣ m →
          (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) < (ell : ℝ)) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (S delta N) (weight delta N) d -
              finiteSourceMass (S delta N) (weight delta N)) / (Nat.totient d : ℝ))| ≤
        delta * singularNormalization N := by
  intro delta hdelta
  filter_upwards [eventually_outer_coprime_identities_of_manuscript_roughness
    hb hnu hr (hepsilonR delta hdelta) hgap (retain delta) (cap delta)
    (S delta) (weight delta) (hrough delta hdelta)] with N hidentities
  intro hEven
  rw [(hidentities hEven).2, abs_zero]
  apply mul_nonneg hdelta.le
  have hseries := (singularSeries_pos N).le
  unfold singularNormalization
  positivity

end
end ImbalancedChen.P4BOuterCoprimeElimination
