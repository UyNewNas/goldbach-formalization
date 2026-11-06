import ImbalancedChen.P3FourierActualInversion
import Mathlib.Data.Nat.ModEq

/-!
P3.6 / manuscript §4 after (F): the SAME rho and full original
signed-source mass, now split into a genuine nonzero integer shift,
the exact complete-product=T term, and the exact coprime mean.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
No divisor moment, exceptional-product bound, PP estimate, or
additional analytic/distribution hypothesis is asserted here.
No tau(0) is formed: only off-diagonal source tuples enter the shifted
divisibility mass. The complete modulus Q remains outside source sums.
-/

namespace ImbalancedChen.P3FullModulusShiftedMoment
noncomputable section
open scoped Classical BigOperators
open P3FullSignedModulusTail

/-- The literal complete original-product congruence is equivalent
to divisibility by the ORIGINAL integer modulus, with signed shift T-b.
No auxiliary or coordinate modulus is introduced. -/
def shiftedResidueKernel {g : ℕ} (T q : ℕ)
    (p : Fin g → ℕ) : ℝ :=
  if (q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ) then 1 else 0

theorem kernelMass_eq_shifted {g : ℕ} (T q : ℕ)
    (p : Fin g → ℕ) :
    kernelMass T q p =
      shiftedResidueKernel T q p +
        (if Nat.Coprime (∏ j, p j) q
          then (Nat.totient q : ℝ)⁻¹ else 0) := by
  have hmod :
      ((∏ j, p j) % q = T % q) ↔
        (q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ) := by
    simpa only [Nat.ModEq] using
      (Nat.modEq_iff_dvd (n := q) (a := ∏ j, p j) (b := T))
  unfold kernelMass shiftedResidueKernel
  by_cases h : (∏ j, p j) % q = T % q
  · simp [h, hmod.mp h]
  · have hd : ¬ ((q : ℤ) ∣ (T : ℤ) - ((∏ j, p j) : ℤ)) :=
      fun hh => h (hmod.mpr hh)
    simp [h, hd]

/-- The exact-product coefficient mass on the actual finite source. -/
def exactCoefficientMass {ι : Type*} {g : ℕ}
    (source : Finset ι) (coefficient : ι → ℝ)
    (T : ℕ) (products : ι → Fin g → ℕ) : ℝ :=
  ∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
    |coefficient t|

/-- The off-product coefficient mass; it contains no exact T tuple. -/
def offCoefficientMass {ι : Type*} {g : ℕ}
    (source : Finset ι) (coefficient : ι → ℝ)
    (T : ℕ) (products : ι → Fin g → ℕ) : ℝ :=
  ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
    |coefficient t|

/-- Original complete-modulus signed-rho absolute mass at product=T,
with the exact totient mean still present. -/
def exactRhoMass (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, |rho q| * (1 + (Nat.totient q : ℝ)⁻¹)

/-- The mean-only modulus factor, before arithmetic bounds. -/
def meanRhoMass (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, |rho q| * (Nat.totient q : ℝ)⁻¹

/-- Divisibility by the nonzero signed ORIGINAL complete-product shift.
Only off-diagonal tuples are admitted, so no shifted divisor at zero. -/
def offShiftedResidueMass {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) : ℝ :=
  ∑ q ∈ Q, |rho q| *
    ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
      |coefficient t| * shiftedResidueKernel T q (products t)

/-- The exact coprime mean on the OFF-diagonal; no replacement
by an unrestricted mean is made until the last upper bound. -/
def offCoprimeMeanMass {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) : ℝ :=
  ∑ q ∈ Q, |rho q| *
    ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
      |coefficient t| *
        (if Nat.Coprime (∏ j, products t j) q
          then (Nat.totient q : ℝ)⁻¹ else 0)

/-- The off-diagonal shift really is nonzero in the integers. -/
theorem off_shift_ne_zero {ι : Type*} {g : ℕ}
    (source : Finset ι) (products : ι → Fin g → ℕ)
    (T : ℕ) (t : ι)
    (ht : t ∈ source.filter (fun t => (∏ j, products t j) ≠ T)) :
    (T : ℤ) - ((∏ j, products t j) : ℤ) ≠ 0 := by
  have hne : (∏ j, products t j) ≠ T := (Finset.mem_filter.mp ht).2
  intro heq
  have he : (T : ℤ) = ((∏ j, products t j) : ℤ) :=
    sub_eq_zero.mp heq
  exact hne (by exact_mod_cast he.symm)

/-- On exact b=T and original admissible (q,T)=1, the full kernel
is literally 1+1/phi(q). This does NOT eliminate the exception. -/
theorem exact_kernel_mass {g : ℕ} (T q : ℕ)
    (p : Fin g → ℕ)
    (hp : (∏ j, p j) = T)
    (hcop : Nat.Coprime T q) :
    kernelMass T q p = 1 + (Nat.totient q : ℝ)⁻¹ := by
  simp [kernelMass, hp, hcop]

/-- Exact b=T mass factors AFTER the full original modulus sum, for
the original coprime physical moduli. No tau(0), and no smallness claim. -/
theorem exact_mass_factor {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    (∑ q ∈ Q, |rho q| *
      ∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
        |coefficient t| * kernelMass T q (products t)) =
      exactCoefficientMass source coefficient T products * exactRhoMass Q rho := by
  unfold exactCoefficientMass exactRhoMass
  calc
    _ = ∑ q ∈ Q,
        (|rho q| * (1 + (Nat.totient q : ℝ)⁻¹)) *
          (∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
            |coefficient t|) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hi :
          (∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
            |coefficient t| * kernelMass T q (products t)) =
          (∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
            |coefficient t|) * (1 + (Nat.totient q : ℝ)⁻¹) := by
        calc
          _ = ∑ t ∈ source.filter (fun t => (∏ j, products t j) = T),
                |coefficient t| * (1 + (Nat.totient q : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [exact_kernel_mass T q (products t)
              (Finset.mem_filter.mp ht).2 (hcop q hq)]
          _ = _ := (Finset.sum_mul ..).symm
      rw [hi]
      ring
    _ = _ := by
      rw [← Finset.sum_mul]
      ring

/-- The OFF-diagonal full kernel is exactly shifted congruence mass
plus the still-exact coprime mean. Neither sum is discarded. -/
theorem off_mass_split {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) :
    (∑ q ∈ Q, |rho q| *
      ∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| * kernelMass T q (products t)) =
      offShiftedResidueMass Q source rho coefficient T products +
        offCoprimeMeanMass Q source rho coefficient T products := by
  unfold offShiftedResidueMass offCoprimeMeanMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [kernelMass_eq_shifted]
  ring

/-- The off-diagonal coprime mean is at most the original unrestricted
totient mean, with no distribution theorem and NO relative-Theta claim. -/
theorem off_mean_le {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ) :
    offCoprimeMeanMass Q source rho coefficient T products ≤
      offCoefficientMass source coefficient T products * meanRhoMass Q rho := by
  unfold offCoprimeMeanMass
  have hq (q : ℕ) :
      (∑ t ∈ source.filter (fun t => (∏ j, products t j) ≠ T),
        |coefficient t| *
          (if Nat.Coprime (∏ j, products t j) q
            then (Nat.totient q : ℝ)⁻¹ else 0)) ≤
        offCoefficientMass source coefficient T products *
          (Nat.totient q : ℝ)⁻¹ := by
    unfold offCoefficientMass
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro t ht
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases hc : Nat.Coprime (∏ j, products t j) q
    · simp [hc]
    · simp only [if_neg hc]
      positivity
  calc
    _ ≤ ∑ q ∈ Q, |rho q| *
          (offCoefficientMass source coefficient T products *
            (Nat.totient q : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro q hqmem
      exact mul_le_mul_of_nonneg_left (hq q) (abs_nonneg _)
    _ = offCoefficientMass source coefficient T products *
        meanRhoMass Q rho := by
      unfold meanRhoMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hqmem
      ring

/-- Arithmetic reduction of the SAME full rho-modulus mass:
1. exact complete-product T is explicit and nonzero-shift-free;
2. nonzero off-product congruences become literal integer divisors;
3. the off-product exact coprime mean is paid by its unrestricted
   totient mass. The remaining shifted divisor moment and exact
   coefficient mass are still UNPROVED arithmetic payments. -/
theorem full_mass_le_shifted_and_exact {ι : Type*} {g : ℕ}
    (Q : Finset ℕ) (source : Finset ι) (rho : ℕ → ℝ)
    (coefficient : ι → ℝ) (T : ℕ)
    (products : ι → Fin g → ℕ)
    (hcop : ∀ q ∈ Q, Nat.Coprime T q) :
    fullModulusMass Q source rho coefficient T products ≤
      exactCoefficientMass source coefficient T products * exactRhoMass Q rho +
        offShiftedResidueMass Q source rho coefficient T products +
        offCoefficientMass source coefficient T products * meanRhoMass Q rho := by
  calc
    fullModulusMass Q source rho coefficient T products =
        exactCoefficientMass source coefficient T products * exactRhoMass Q rho +
          (offShiftedResidueMass Q source rho coefficient T products +
            offCoprimeMeanMass Q source rho coefficient T products) := by
      rw [fullModulusMass_split,
        exact_mass_factor Q source rho coefficient T products hcop,
        off_mass_split]
    _ ≤ _ := by
      have h := off_mean_le Q source rho coefficient T products
      linarith

end
end ImbalancedChen.P3FullModulusShiftedMoment
