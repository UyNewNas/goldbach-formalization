import ImbalancedChen.P5OriginalU5FrozenSource
import ImbalancedChen.Part5OriginalH430SameQCanonicalMains

/-! Arithmetic form of the ordinary upper sieve on the original prime
population. The excess has an explicit summand for each original prime
ell in the progression. Its contribution vanishes wherever the quotient
passes the actual sieve. The signed AP sum uses the same divisors and
the full modulus p*r, including the exact finite coprime mean. -/
namespace ImbalancedChen.Part5OriginalH430RootRosserSurplus
noncomputable section
open Finset Wu2008DoubleSieve MathlibNt.SieveTheory.LinearSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2ActualMarkedCountState (rootLevel)
open P2FrozenReceiverCountActions
open P5OriginalU5FrozenSource (receiver frozenCarrier_eq_original_labels
  frozenRemainder_eq_actual_signed_AP)
open Part5OriginalH430SameQCanonicalMains (model)
open scoped Classical BigOperators

def primeSurplus (N p : ℕ) (Q z : ℝ) (ell : ℕ) : ℝ :=
  let g := Nat.gcd (ordinarySievePrimeProduct (p * N) z) (N - ell)
  (∑ r ∈ g.divisors, ordinaryRosserWeight true N p (rootLevel Q p) z r) -
    (if g = 1 then 1 else 0)

def surplus (N p : ℕ) (Q z : ℝ) : ℝ :=
  ∑ ell ∈ (goldbachDivisible N p).filter (receiver N), primeSurplus N p Q z ell

def signedAP (N p : ℕ) (Q z : ℝ) : ℝ :=
  ∑ r ∈ (ordinarySievePrimeProduct (p * N) z).divisors,
    ordinaryRosserWeight true N p (rootLevel Q p) z r *
      (finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N (p*r) +
        (((chenAdditivePrimeCarrier N).card : ℝ) - logarithmicIntegral N -
          chenPrimeDivisorCount N (p*r)) / (Nat.totient (p*r) : ℝ))

theorem primeSurplus_nonneg {N p : ℕ} {Q z : ℝ} (hD : 1 < rootLevel Q p)
    (hz : z ≤ (rootLevel Q p : ℝ)) (ell : ℕ) : 0 ≤ primeSurplus N p Q z ell := by
  have hp : ∀ r ∈ (ordinarySievePrimeProduct (p*N) z).primeFactors, r < rootLevel Q p := by
    intro r hr
    rw [ordinarySievePrimeProduct, Nat.primeFactors_prod
      (fun q hq => (mem_primeWindow.mp hq).1)] at hr
    exact_mod_cast (mem_primeWindow.mp hr).2.2.2.trans_le hz
  have hcert := upperRosserWeight_certificate (ordinarySievePrimeProduct_squarefree _ _)
    (ordinarySievePrimeProduct_pos (p*N) z).ne' hD hp
  exact sub_nonneg.mpr (upperRosserWeight_divisor_sum hcert
    (Nat.gcd_dvd_left (ordinarySievePrimeProduct (p*N) z) (N-ell)))

theorem surplus_nonneg {N p : ℕ} {Q z : ℝ} (hD : 1 < rootLevel Q p)
    (hz : z ≤ (rootLevel Q p : ℝ)) : 0 ≤ surplus N p Q z :=
  Finset.sum_nonneg (fun ell _ => primeSurplus_nonneg hD hz ell)

/-- On each actual surviving quotient, the upper polynomial at its
original prime label is exactly one. Its local excess is exactly zero. -/
theorem true_quotient_zero_surplus {N p q : ℕ} {Q z : ℝ}
    (hD : 1 < rootLevel Q p) (hp : ChenPrimeRough z p)
    (hq : q ∈ chenSiftedQuotientPrimeSource N p z) :
    ∃ ell ∈ (goldbachDivisible N p).filter (receiver N),
      (N-ell)/p = q ∧ primeSurplus N p Q z ell = 0 := by
  have hq' := Finset.mem_filter.mp hq
  obtain ⟨ell, hell, rfl⟩ := Finset.mem_image.mp hq'.1
  obtain ⟨he, hd⟩ := mem_chenQuotientPrimeCarrier.mp hell
  have hf : ell ∈ frozenCarrier N p (receiver N) z := by
    rw [frozenCarrier_eq_original_labels N p z hp]
    exact Finset.mem_filter.mpr ⟨he, hd, hq'.2⟩
  have hg : ell ∈ (goldbachDivisible N p).filter (receiver N) ∧
      Nat.gcd (ordinarySievePrimeProduct (p*N) z) (N-ell) = 1 := by
    simp only [frozenCarrier, sourceSieveCarrier, goldbachDivisible, Finset.mem_filter,
      sifted_iff_product_coprime, Nat.coprime_iff_gcd_eq_one] at hf ⊢
    tauto
  refine ⟨ell, hg.1, rfl, ?_⟩
  simp [primeSurplus, hg.2, ordinaryRosserWeight, upperRosserWeight,
    UpperRosserAdmissible, UpperRosserAdmissibleSet, hD,
    (ordinarySievePrimeProduct_pos (p*N) z).ne']

/-- Finite double counting of actual prime labels. Both signed pieces on
the right use the same Rosser coefficients. No estimate for an individual
progression, an individual p, or its receiver cardinality is assumed. -/
theorem frozen_count_plus_surplus {N p : ℕ} (Q z : ℝ) (hp : p.Coprime N) :
    (frozenCount N p (receiver N) z : ℝ) + surplus N p Q z =
      model true N Q p z + signedAP N p Q z := by
  calc
    _ = frozenPolynomial true N p (rootLevel Q p) (receiver N) z := by
      rw [frozenCount_eq_gcd_indicator]
      unfold surplus frozenPolynomial
      rw [frozen_weighted_count_eq_gcd_sum N p _ (ordinarySievePrimeProduct_pos _ _).ne',
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ell _
      dsimp only [primeSurplus]
      ring
    _ = _ := by
      rw [frozenPolynomial_eq_model_add_remainder, frozenRemainder_eq_actual_signed_AP _ _ _ _ _ hp]
      rfl

end
end ImbalancedChen.Part5OriginalH430RootRosserSurplus
