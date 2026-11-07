import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.ActualUpperCountingInputs

/-!
# Zero extension and supported outer carriers

SOURCE ONLY / YELLOW / UNCOMPILED.
An enumeration carrier may extend above N when its actual weight is zero
there. Restricting to its filter m ≤ N preserves every finite functional,
the literal source inclusion, and the outer pointwise inequality. The
natural-subtraction Fubini identity is used only on that restricted carrier.
No analytic mass, density, coprime, or primitive estimate is asserted here.
-/

namespace ImbalancedChen
namespace P4B

noncomputable section

open scoped BigOperators

/-- Zero extension preserves any signed weighted test sum. -/
theorem sum_weight_mul_eq_of_zero_extension
    (S R : Finset ℕ) (weight F : ℕ → ℝ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    (∑ m ∈ R, weight m * F m) = ∑ m ∈ S, weight m * F m := by
  symm
  apply Finset.sum_subset hSR
  intro m hm hnot
  rw [hzero m hm hnot, zero_mul]

/-- Total mass is unchanged, with no sign assumption on the weight. -/
theorem finiteSourceMass_eq_of_zero_extension
    (S R : Finset ℕ) (weight : ℕ → ℝ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    finiteSourceMass R weight = finiteSourceMass S weight := by
  simpa only [finiteSourceMass, mul_one] using
    sum_weight_mul_eq_of_zero_extension S R weight (fun _ => 1) hSR hzero

/-- The exact coprimality mask is preserved on the whole enlarged carrier. -/
theorem finiteCoprimeMass_eq_of_zero_extension
    (S R : Finset ℕ) (weight : ℕ → ℝ) (d : ℕ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    finiteCoprimeMass R weight d = finiteCoprimeMass S weight d := by
  classical
  simpa only [finiteCoprimeMass, Finset.sum_filter, mul_ite, mul_one, mul_zero] using
    sum_weight_mul_eq_of_zero_extension S R weight
      (fun m => if Nat.Coprime m d then 1 else 0) hSR hzero

/-- Congruence mass is preserved for every residue and modulus, including
zero modulus; primitive-residue assumptions are unnecessary. -/
theorem finiteCongruenceMass_eq_of_zero_extension
    (S R : Finset ℕ) (weight : ℕ → ℝ) (a d : ℕ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    finiteCongruenceMass R weight a d = finiteCongruenceMass S weight a d := by
  classical
  simpa only [finiteCongruenceMass, Finset.sum_filter, mul_ite, mul_one, mul_zero] using
    sum_weight_mul_eq_of_zero_extension S R weight
      (fun m => if Nat.ModEq d m a then 1 else 0) hSR hzero

/-- The existing primitive subset API supplies the fourth pointwise
functional. This wrapper records its use beside the other mass identities. -/
theorem finitePrimitiveDiscrepancy_eq_of_zero_extension
    (S R : Finset ℕ) (weight : ℕ → ℝ) (a d : ℕ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    finitePrimitiveDiscrepancy R weight a d =
      finitePrimitiveDiscrepancy S weight a d := by
  exact finitePrimitiveDiscrepancy_eq_of_subset S R weight a d hSR hzero

/-- Zero extension commutes with the complete signed modulus sum, before
absolute values. The residue may depend on the modulus. -/
theorem sum_rho_mul_primitive_eq_of_zero_extension
    (S R Q : Finset ℕ) (weight rho : ℕ → ℝ) (a : ℕ → ℕ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy R weight (a d) d) =
      ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight (a d) d := by
  apply Finset.sum_congr rfl
  intro d _hd
  rw [finitePrimitiveDiscrepancy_eq_of_subset S R weight (a d) d hSR hzero]

/-- The coprime correction is likewise unchanged as a full signed sum. -/
theorem sum_rho_mul_coprimeCorrection_eq_of_zero_extension
    (S R Q : Finset ℕ) (weight rho : ℕ → ℝ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    (∑ d ∈ Q, rho d *
      ((finiteCoprimeMass R weight d - finiteSourceMass R weight) /
        (Nat.totient d : ℝ))) =
      ∑ d ∈ Q, rho d *
        ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
          (Nat.totient d : ℝ)) := by
  rw [finiteSourceMass_eq_of_zero_extension S R weight hSR hzero]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [finiteCoprimeMass_eq_of_zero_extension S R weight d hSR hzero]

/-- The full main term plus signed correction and signed error has exactly
the same value. The physical carrier Q and arithmetic function rho are fixed. -/
theorem same_rho_outer_terms_eq_of_zero_extension
    (N : ℕ) (S R Q : Finset ℕ) (weight rho : ℕ → ℝ) (hSR : S ⊆ R)
    (hzero : ∀ m ∈ R, m ∉ S → weight m = 0) :
    finiteSourceMass R weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass R weight d - finiteSourceMass R weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy R weight N d) =
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) := by
  rw [sum_rho_mul_coprimeCorrection_eq_of_zero_extension S R Q weight rho hSR hzero,
    sum_rho_mul_primitive_eq_of_zero_extension S R Q weight rho (fun _ => N) hSR hzero,
    finiteSourceMass_eq_of_zero_extension S R weight hSR hzero]

/-- A bound only on points with nonzero actual weight licenses truncation.
No bound is imposed on the remaining points of the enumeration carrier. -/
theorem outerCarrier_filter_le_zero
    (N : ℕ) (R : Finset ℕ) (weight : ℕ → ℝ)
    (hsupported : ∀ m ∈ R, weight m ≠ 0 → m ≤ N) :
    ∀ m ∈ R, m ∉ R.filter (fun m => m ≤ N) → weight m = 0 := by
  intro m hm hnot
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hm, hsupported m hm hne⟩)

/-- Truncation preserves the full original source, the outer majorization,
and positivity. The source's inclusive endpoint supplies m ≤ N. -/
theorem outerCarrier_filter_le_geometry
    (b : ℝ) (N : ℕ) (T : ℝ) (R : Finset ℕ) (weight : ℕ → ℝ)
    (hsource : realHalfProductSource b N T ⊆ R)
    (houter : ∀ m ∈ R,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) :
    (∀ m ∈ R.filter (fun m => m ≤ N), m ≤ N) ∧
      realHalfProductSource b N T ⊆ R.filter (fun m => m ≤ N) ∧
      (∀ m ∈ R.filter (fun m => m ≤ N),
        (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) ∧
      (∀ m ∈ R.filter (fun m => m ≤ N), 0 ≤ weight m) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm
    exact (Finset.mem_filter.mp hm).2
  · intro m hm
    exact Finset.mem_filter.mpr ⟨hsource hm, (mem_realHalfProductSource.mp hm).1⟩
  · intro m hm
    exact houter m (Finset.mem_filter.mp hm).1
  · intro m hm
    have ho := houter m (Finset.mem_filter.mp hm).1
    by_cases hmem : m ∈ realHalfProductSource b N T
    · rw [if_pos hmem] at ho
      exact zero_le_one.trans ho
    · rw [if_neg hmem] at ho
      exact ho

/-- All four pointwise functionals survive the m ≤ N truncation. Bounds
stated on the large carrier therefore remain available after truncation. -/
theorem outerCarrier_filter_le_functionals
    (N : ℕ) (R : Finset ℕ) (weight : ℕ → ℝ)
    (hsupported : ∀ m ∈ R, weight m ≠ 0 → m ≤ N) :
    finiteSourceMass R weight = finiteSourceMass (R.filter (fun m => m ≤ N)) weight ∧
      (∀ d : ℕ, finiteCoprimeMass R weight d =
        finiteCoprimeMass (R.filter (fun m => m ≤ N)) weight d) ∧
      (∀ a d : ℕ, finiteCongruenceMass R weight a d =
        finiteCongruenceMass (R.filter (fun m => m ≤ N)) weight a d) ∧
      (∀ a d : ℕ, finitePrimitiveDiscrepancy R weight a d =
        finitePrimitiveDiscrepancy (R.filter (fun m => m ≤ N)) weight a d) := by
  have hz := outerCarrier_filter_le_zero N R weight hsupported
  have hsub : R.filter (fun m => m ≤ N) ⊆ R := Finset.filter_subset _ _
  refine ⟨finiteSourceMass_eq_of_zero_extension _ _ _ hsub hz, ?_, ?_, ?_⟩
  · intro d
    exact finiteCoprimeMass_eq_of_zero_extension _ _ _ d hsub hz
  · intro a d
    exact finiteCongruenceMass_eq_of_zero_extension _ _ _ a d hsub hz
  · intro a d
    exact finitePrimitiveDiscrepancy_eq_of_subset _ _ _ a d hsub hz

/-- Fubini and the exact signed decomposition are legal on the large
enumeration carrier once only its nonzero weighted points lie below N. -/
theorem sum_weight_mul_physicalDivisorSum_eq_same_rho_of_supported_carrier
    (N : ℕ) (R Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hsupported : ∀ m ∈ R, weight m ≠ 0 → m ≤ N) :
    (∑ m ∈ R, weight m * physicalDivisorSum Q rho (N - m)) =
      finiteSourceMass R weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass R weight d - finiteSourceMass R weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy R weight N d) := by
  have hz := outerCarrier_filter_le_zero N R weight hsupported
  have hsub : R.filter (fun m => m ≤ N) ⊆ R := Finset.filter_subset _ _
  rw [sum_weight_mul_eq_of_zero_extension _ R weight
    (fun m => physicalDivisorSum Q rho (N - m)) hsub hz,
    same_rho_outer_terms_eq_of_zero_extension N _ R Q weight rho hsub hz]
  apply sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors
  intro m hm
  exact (Finset.mem_filter.mp hm).2

/-- Complete finite outer-source bound with the relaxed supported-carrier
condition. All displayed masses and signed sums remain on the original R,
even when R has zero-weight enumeration points above N. -/
theorem RealB_cast_le_same_rho_outer_main_add_errors_of_supported_carrier
    {b T : ℝ} (N z : ℕ) (R Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hsupported : ∀ m ∈ R, weight m ≠ 0 → m ≤ N)
    (hsource : realHalfProductSource b N T ⊆ R)
    (houter : ∀ m ∈ R,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      finiteSourceMass R weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass R weight d - finiteSourceMass R weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy R weight N d) +
        (z : ℝ) + (T + 1) := by
  have hz := outerCarrier_filter_le_zero N R weight hsupported
  have hsub : R.filter (fun m => m ≤ N) ⊆ R := Finset.filter_subset _ _
  obtain ⟨hSN, hsourceS, houterS, _hnonnegS⟩ :=
    outerCarrier_filter_le_geometry b N T R weight hsource houter
  have hfinite := RealB_cast_le_same_rho_outer_main_add_errors N z
    (R.filter (fun m => m ≤ N)) Q weight rho hb hT hSN hsourceS houterS hmajor
  rw [same_rho_outer_terms_eq_of_zero_extension N _ R Q weight rho hsub hz]
  exact hfinite

/-- Literal actual-coefficient specialization. Its all-integer majorant is
proved by the attachment API; only the licensed positive outer geometry is
supplied. This is the finite input for the actual outer asymptotic assembly. -/
theorem RealB_cast_le_attachedUpper_outer_main_add_errors_of_supported_carrier
    {b T nu r epsilon : ℝ} (N : ℕ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (R : Finset ℕ) (weight : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T) (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon ≤ 1) (hepsilonR : epsilon ^ 2 ≤ r)
    (hN : 2 ≤ N) (hcap : (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hsupported : ∀ m ∈ R, weight m ≠ 0 → m ≤ N)
    (hsource : realHalfProductSource b N T ⊆ R)
    (houter : ∀ m ∈ R,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m) :
    (RealB b N : ℝ) ≤
      finiteSourceMass R weight *
          physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
            (attachedUpperCoefficient nu r epsilon retain cap N) +
        (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
          attachedUpperCoefficient nu r epsilon retain cap N d *
            ((finiteCoprimeMass R weight d - finiteSourceMass R weight) /
              (Nat.totient d : ℝ))) +
        (∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
          attachedUpperCoefficient nu r epsilon retain cap N d *
            finitePrimitiveDiscrepancy R weight N d) +
        (Nat.ceil ((N : ℝ) ^ (nu * r)) : ℝ) + (T + 1) := by
  exact RealB_cast_le_same_rho_outer_main_add_errors_of_supported_carrier
    N (Nat.ceil ((N : ℝ) ^ (nu * r))) R
    (attachedUpperModuli nu r epsilon retain cap N) weight
    (attachedUpperCoefficient nu r epsilon retain cap N) hb hT hsupported hsource houter
    (attachedUpperCoefficient_majorant hnu hepsilon hepsilonOne hepsilonR
      retain cap hN hcap)

end

end P4B
end ImbalancedChen
