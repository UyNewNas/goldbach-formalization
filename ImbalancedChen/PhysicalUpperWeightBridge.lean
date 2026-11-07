import ImbalancedChen.FiniteSieveModel
import ImbalancedChen.SignSensitiveAttachment

/-!
# Finite bridge for one physical positive upper weight

The manuscript uses one and the same signed coefficient `ρ_N` in three
places: the pointwise divisor-sum majorant, its reciprocal-totient density,
and the signed prime-product distribution estimate.  This file gives the
exact finite identity which keeps those uses tied to one function `rho`.

No density or distribution estimate is assumed here.  The coprime-main-mass
correction and the signed progression error remain separate visible terms;
in particular the exact coprime mass is not silently replaced by the total
source mass.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The divisor sum of one finitely supported physical coefficient. -/
def physicalDivisorSum (Q : Finset ℕ) (rho : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Q, if q ∣ n then rho q else 0

/-- Finite Fubini for the literal shifted half-product source.  The same
coefficient `rho` weights every moving residue-class count. -/
theorem sum_physicalDivisorSum_halfProductSource
    (num den N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ halfProductSource num den N T,
        physicalDivisorSum Q rho (N - m)) =
      ∑ q ∈ Q, rho q * halfProductCongruenceMass num den N T q := by
  classical
  unfold physicalDivisorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [halfProductSource_filter_dvd_eq_filter_modEq]
  unfold halfProductCongruenceMass
  ring

/-- The reciprocal-totient density of the displayed physical coefficient. -/
def physicalDensitySum (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q / (Nat.totient q : ℝ)

/-- The exact price for replacing the modulus-dependent coprime source mass
by the total source mass. -/
def physicalCoprimeCorrection
    (num den N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    ((halfProductCoprimeMass num den N T q -
        ((halfProductSource num den N T).card : ℝ)) /
      (Nat.totient q : ℝ))

/-- The signed primitive-residue distribution error for the same physical
coefficient.  It is intentionally not replaced by an absolute discrepancy
sum. -/
def physicalDistributionError
    (num den N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    (halfProductCongruenceMass num den N T q -
      halfProductCoprimeMass num den N T q / (Nat.totient q : ℝ))

/-- Exact three-term decomposition: density, coprime correction, and signed
distribution error.  All three terms contain the identical `rho`. -/
theorem sum_rho_mul_halfProductCongruenceMass_eq
    (num den N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ q ∈ Q, rho q * halfProductCongruenceMass num den N T q) =
      ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum Q rho +
        physicalCoprimeCorrection num den N T Q rho +
        physicalDistributionError num den N T Q rho := by
  unfold physicalDensitySum physicalCoprimeCorrection physicalDistributionError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- A pointwise upper divisor sum on every shifted receiver gives the actual
sifted source bound with the density, coprime correction, and signed
distribution terms all exposed.  This is a finite implication, not an
analytic estimate for any of its three right-hand terms. -/
theorem siftedHalfProductSource_card_le_same_rho_main_add_errors
    (num den N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((siftedHalfProductSource num den N T z).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum Q rho +
        physicalCoprimeCorrection num den N T Q rho +
        physicalDistributionError num den N T Q rho := by
  classical
  calc
    ((siftedHalfProductSource num den N T z).card : ℝ) =
        ∑ m ∈ halfProductSource num den N T,
          if Nat.Coprime (N - m) (sieveProduct N z) then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp [siftedHalfProductSource]
    _ ≤ ∑ m ∈ halfProductSource num den N T,
        physicalDivisorSum Q rho (N - m) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hmajor (N - m)
    _ = ∑ q ∈ Q, rho q * halfProductCongruenceMass num den N T q :=
      sum_physicalDivisorSum_halfProductSource num den N T Q rho
    _ = ((halfProductSource num den N T).card : ℝ) *
          physicalDensitySum Q rho +
        physicalCoprimeCorrection num den N T Q rho +
        physicalDistributionError num den N T Q rho :=
      sum_rho_mul_halfProductCongruenceMass_eq num den N T Q rho

end

end ImbalancedChen
