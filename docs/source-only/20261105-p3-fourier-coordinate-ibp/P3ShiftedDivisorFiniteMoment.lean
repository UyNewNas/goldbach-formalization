import ImbalancedChen.P3FullModulusShiftedMoment
import Mathlib.NumberTheory.Divisors

/-!
P3.6 fixed manuscript 9731290 §4, post-Fourier complete modulus sum.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

Finite, actual-rho arithmetic improvement: the OFF-diagonal congruence
sum is supported precisely on the natural divisors of the NONZERO
signed integer shift T - (complete original product). This replaces a
full Q-sum by an exact restricted divisor sum, and then a genuine
(nonzero-shift) weighted divisor moment. The exceptional product=T and
the true coprime mean remain separately in the predecessor ledger.

No analytic shifted-divisor moment is claimed. The optional uniform-rho
bound below is an ordinary pointwise bound, NOT a conjectural PP input.
-/

namespace ImbalancedChen.P3ShiftedDivisorFiniteMoment
noncomputable section
open scoped Classical BigOperators
open P3FullModulusShiftedMoment
open P3FullSignedModulusTail

/-- Absolute value of the actual signed shift, not a local or auxiliary
modulus; the full labelled original product is kept intact. -/
def shiftAbs {g : ℕ} (T : ℕ) (p : Fin g → ℕ) : ℕ :=
  ((T : ℤ) - ((∏ j, p j) : ℤ)).natAbs

/-- The original off-diagonal source gives a nonzero divisor argument. -/
theorem shiftAbs_ne_zero {g : ℕ} (T : ℕ) (p : Fin g → ℕ)
    (hne : (∏ j, p j) ≠ T) : shiftAbs T p ≠ 0 := by
  have hz : (T : ℤ) - ((∏ j, p j) : ℤ) ≠ 0 := by
    intro h
    apply hne
    exact_mod_cast (sub_eq_zero.mp h).symm
  simpa [shiftAbs] using hz

/-- Literal indicator identity. In particular, q=0 is not silently
admitted: 0 cannot divide a nonzero original integer shift. -/
theorem shiftedResidueKernel_eq_divisors {g : ℕ}
    (T q : ℕ) (p : Fin g → ℕ)
    (hne : (∏ j, p j) ≠ T) :
    shiftedResidueKernel T q p =
      if q ∈ (shiftAbs T p).divisors then 1 else 0 := by
  have hz : shiftAbs T p ≠ 0 := shiftAbs_ne_zero T p hne
  have hdvd :
      ((q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ)) ↔
        q ∣ shiftAbs T p := by
    constructor
    · intro h
      simpa [shiftAbs] using (Int.natAbs_dvd_natAbs.mp h)
    · intro h
      apply Int.natAbs_dvd_natAbs.mpr
      simpa [shiftAbs] using h
  have hmem :
      ((q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ)) ↔
        q ∈ (shiftAbs T p).divisors := by
    rw [Nat.mem_divisors]
    exact ⟨fun h => ⟨hdvd.mp h, hz⟩, fun h => hdvd.mpr h.1⟩
  by_cases h : (q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ)
  · have hm := hmem.mp h
    simp [shiftedResidueKernel, h, hm]
  · have hm : q ∉ (shiftAbs T p).divisors :=
      fun hh => h (hmem.mpr hh)
    simp [shiftedResidueKernel, h, hm]

/-- Finite original physical Q intersection with the *actual*
divisors. The real signed rho is made absolute only in this
majorant, not in the signed PP assertion. -/
def restrictedRhoDivisorMass {g : ℕ}
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℕ) (p : Fin g → ℕ) : ℝ :=
  ∑ q ∈ Q.filter (fun q => q ∈ (shiftAbs T p).divisors), |rho q|

/-- For every off-diagonal original source tuple, the q-congruence
mass is EXACTLY the restricted natural divisor sum. -/
theorem off_shifted_eq_restricted_divisor {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) :
    offShiftedResidueMass Q source rho coefficient T products =
      ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| * restrictedRhoDivisorMass Q rho T (products t) := by
  unfold offShiftedResidueMass
  calc
    _ = ∑ q ∈ Q,
          ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
            |rho q| * (|coefficient t| *
              shiftedResidueKernel T q (products t)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
    _ = ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
          ∑ q ∈ Q, |coefficient t| *
            (|rho q| * shiftedResidueKernel T q (products t)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      have hne : (∏ j, products t j) ≠ T := (Finset.mem_filter.mp ht).2
      have hq :
          (∑ q ∈ Q, |rho q| * shiftedResidueKernel T q (products t)) =
            restrictedRhoDivisorMass Q rho T (products t) := by
        unfold restrictedRhoDivisorMass
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro q hq
        rw [shiftedResidueKernel_eq_divisors T q (products t) hne]
        split_ifs <;> ring
      rw [← Finset.mul_sum, hq]

/-- Dropping the actual physical Q restriction only makes the
nonzero-shift divisor mass larger. No divisor estimate is assumed. -/
theorem restrictedRhoDivisorMass_le_full {g : ℕ}
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T : ℕ) (p : Fin g → ℕ) :
    restrictedRhoDivisorMass Q rho T p ≤
      ∑ q ∈ (shiftAbs T p).divisors, |rho q| := by
  unfold restrictedRhoDivisorMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq hnot
    exact abs_nonneg _

/-- Genuine full original-source reduction to a weighted divisor moment
over NONZERO shifts, without assuming a shifted-moment theorem. -/
theorem off_shifted_le_divisor_moment {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) :
    offShiftedResidueMass Q source rho coefficient T products ≤
      ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| *
          (∑ q ∈ (shiftAbs T (products t)).divisors, |rho q|) := by
  rw [off_shifted_eq_restricted_divisor]
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (restrictedRhoDivisorMass_le_full Q rho T (products t))
    (abs_nonneg _)

/-- A merely pointwise bound on the *same* rho converts its restricted
divisor mass into the classical tau of the genuinely nonzero shift.
This does NOT supply a uniform rho bound for the entire actual family. -/
theorem restrictedRhoDivisorMass_le_card {g : ℕ}
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℕ) (p : Fin g → ℕ) (R : ℝ)
    (hR : ∀ q ∈ Q, |rho q| ≤ R) (hRnonneg : 0 ≤ R) :
    restrictedRhoDivisorMass Q rho T p ≤
      R * ((shiftAbs T p).divisors.card : ℝ) := by
  let F := Q.filter (fun q => q ∈ (shiftAbs T p).divisors)
  have hsubset : F ⊆ (shiftAbs T p).divisors := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hcard : (F.card : ℝ) ≤ ((shiftAbs T p).divisors.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsubset)
  calc
    restrictedRhoDivisorMass Q rho T p =
        ∑ q ∈ F, |rho q| := rfl
    _ ≤ ∑ q ∈ F, R := by
      apply Finset.sum_le_sum
      intro q hq
      exact hR q (Finset.mem_filter.mp hq).1
    _ = R * (F.card : ℝ) := by simp [mul_comm]
    _ ≤ R * ((shiftAbs T p).divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcard hRnonneg

/-- Actual off-diagonal shifted congruence mass gets a tau-shift
majorant, not tau(0). The finite source still retains its labels,
coefficients and complete ORIGINAL products. -/
theorem off_shifted_le_tau_moment {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) (R : ℝ)
    (hR : ∀ q ∈ Q, |rho q| ≤ R) (hRnonneg : 0 ≤ R) :
    offShiftedResidueMass Q source rho coefficient T products ≤
      R * (∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| * ((shiftAbs T (products t)).divisors.card : ℝ)) := by
  rw [off_shifted_eq_restricted_divisor]
  calc
    _ ≤ ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| *
          (R * ((shiftAbs T (products t)).divisors.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (restrictedRhoDivisorMass_le_card Q rho T (products t) R hR hRnonneg)
        (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- The full same-rho mass now has a literal divisor-moment upper bound.
The b=T coefficient factor and the exact coprime-mean factor are NOT
declared small; those independent arithmetic obligations remain. -/
theorem full_mass_le_divisor_moment {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    fullModulusMass Q source rho coefficient T products ≤
      exactCoefficientMass source coefficient T products * exactRhoMass Q rho +
      (∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| *
          (∑ q ∈ (shiftAbs T (products t)).divisors, |rho q|)) +
      offCoefficientMass source coefficient T products * meanRhoMass Q rho := by
  have h0 := full_mass_le_shifted_and_exact
    Q source rho coefficient T products hcop
  have h1 := off_shifted_le_divisor_moment
    Q source rho coefficient T products
  linarith

end
end ImbalancedChen.P3ShiftedDivisorFiniteMoment
