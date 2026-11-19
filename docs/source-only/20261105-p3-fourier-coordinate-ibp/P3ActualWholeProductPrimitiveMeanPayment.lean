import ImbalancedChen.P3ActualWholeProductMixedTauTransfer
import ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
import Mathlib.Tactic

/-!
P3.6 — exact PHYSICAL reciprocal-totient mean payment on genuine
noninjective, labelled, three-prime-box × literal rough-HB sources.

Frozen manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§1,3(T),4(F).  Original integer signed rho,
original physical Q and EXACT coprime mean are kept.

Unlike the preceding shifted-divisor *count* ledger, the primitive MEAN
has a completely separate positive mass. It can be paid after the full
product-fibre regrouping, with no shift-divisor factor, no rho sign
assumption, no change of label multiplicities and no new analytic axiom.

This does NOT show that actual rho_N has polylog reciprocal-totient mass,
that W_T has the necessary uniform coefficient norm, or that the full
PP compiler sources are exhausted. SOURCE_ONLY / UNCOMPILED /
KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWholeProductFibreLedger
open ImbalancedChen.P3ActualWholeProductMixedTauTransfer
open ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox

/-- The mass of the ORIGINAL physical signed rho with its true
reciprocal Euler totient. No replacement density/auxiliary level. -/
def physicalReciprocalTotientMass
    (Q : Finset ℕ) (rho : ℕ → ℤ) : ℝ :=
  ∑ q ∈ Q, ‖(rho q : ℂ) *
    (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖

theorem physicalReciprocalTotientMass_nonneg
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    0 ≤ physicalReciprocalTotientMass Q rho := by
  unfold physicalReciprocalTotientMass
  exact Finset.sum_nonneg (fun q hq => norm_nonneg _)

/-- Keep the full product B in the primitive filter; in particular
no removal of the gcd(B,q)=1 restriction inside the exact mean. -/
def primitivePhysicalMean
    (B : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ) : ℂ :=
  ∑ q ∈ Q.filter (fun q => Nat.Coprime B q),
    (rho q : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)

/-- Exact physical coprime mean is bounded by original rho/phi mass.
There is NO assumption that rho is nonnegative. -/
theorem primitivePhysicalMean_norm_le
    (B : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ) :
    ‖primitivePhysicalMean B Q rho‖ ≤
      physicalReciprocalTotientMass Q rho := by
  unfold primitivePhysicalMean physicalReciprocalTotientMass
  calc
    ‖∑ q ∈ Q.filter (fun q => Nat.Coprime B q),
        (rho q : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖ ≤
      ∑ q ∈ Q.filter (fun q => Nat.Coprime B q),
        ‖(rho q : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
    _ ≤ ∑ q ∈ Q,
        ‖(rho q : ℂ) * (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖ := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum
          intro q hq
          by_cases hc : Nat.Coprime B q
          · simp [hc]
          · simp [hc]

/-- A true, unconditional finite-geometry L1 bound on the PHYSICAL
primitive mean, uniform in the complete product index B.  It does not
assume the conclusion of PP or a divisor moment. -/
theorem primitive_mean_weighted_l1
    (S : Finset ℕ) (c : ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) :
    ‖∑ B ∈ S, c B * primitivePhysicalMean B Q rho‖ ≤
      (∑ B ∈ S, ‖c B‖) *
        physicalReciprocalTotientMass Q rho := by
  calc
    _ ≤ ∑ B ∈ S, ‖c B * primitivePhysicalMean B Q rho‖ :=
      norm_sum_le _ _
    _ = ∑ B ∈ S, ‖c B‖ * ‖primitivePhysicalMean B Q rho‖ := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [norm_mul]
    _ ≤ ∑ B ∈ S,
          ‖c B‖ * physicalReciprocalTotientMass Q rho := by
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (primitivePhysicalMean_norm_le B Q rho) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

/-- No hidden multiplicity factor: the actual complete-product fibre
coefficients obey the same physical mean bound after grouping different
original ordered prime words that produce the same B. -/
theorem actualHBFullProduct_primitive_mean_bound
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ) :
    ‖∑ B ∈ (actualHBTriples N τ u v w).image (tripleFullProduct m),
      actualHBFullProductCoeff N m j τ z y u v w W B *
        primitivePhysicalMean B Q rho‖ ≤
      (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            ‖hbPositionalMass m j z y W a b d‖) *
              physicalReciprocalTotientMass Q rho := by
  have hcoeff :=
    actualHBFullProductCoeff_l1_le N m j τ z y u v w W
  exact (primitive_mean_weighted_l1
    ((actualHBTriples N τ u v w).image (tripleFullProduct m))
    (actualHBFullProductCoeff N m j τ z y u v w W) Q rho).trans
    (mul_le_mul_of_nonneg_right hcoeff
      (physicalReciprocalTotientMass_nonneg Q rho))

/-- This bound is on the SAME precise primitive mean as the earlier
three-box signed offshift ledger. The target B=N contributes 0 by the
literal strict rough-HB source theorem (even N, z >= 2), not by
passing the zero shift to Nat.divisors. -/
theorem actualHBFullProduct_primitive_mean_eq_offshift_ledger
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    (∑ B ∈ (actualHBTriples N τ u v w).image (tripleFullProduct m),
      actualHBFullProductCoeff N m j τ z y u v w W B *
        primitivePhysicalMean B Q rho) =
      fixedThreeHBOffshiftMean N m j τ z y u v w Q rho W := by
  calc
    _ = ∑ x ∈ actualHBTriples N τ u v w,
          hbPositionalMass m j z y W x.1.1 x.1.2 x.2 *
            primitivePhysicalMean (tripleFullProduct m x) Q rho := by
      simpa only [actualHBFullProductCoeff] using
        (weighted_sum_by_full_product_fibre
          (actualHBTriples N τ u v w) (tripleFullProduct m)
          (fun x => hbPositionalMass m j z y W x.1.1 x.1.2 x.2)
          (fun B => primitivePhysicalMean B Q rho))
    _ = _ := by
      simp only [actualHBTriples, Finset.sum_product]
      unfold fixedThreeHBOffshiftMean
      dsimp only
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      by_cases htarget : a.prod * b.prod * d.prod * m = N
      · have hzero := hbPositionalMass_zero_of_actual_target
          N m j τ z y u v w a b d W ha hb hd hz hN htarget
        simp [tripleFullProduct, primitivePhysicalMean, htarget, hzero]
      · simp [tripleFullProduct, primitivePhysicalMean, htarget]

/-- Exactly the existing OFFSHIFT physical mean, not an abstract
replacement, is paid by the actual original positional coefficient L1
and the original signed physical rho/phi mass. -/
theorem fixedThreeHBOffshiftMean_norm_le
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    ‖fixedThreeHBOffshiftMean N m j τ z y u v w Q rho W‖ ≤
      (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            ‖hbPositionalMass m j z y W a b d‖) *
              physicalReciprocalTotientMass Q rho := by
  rw [← actualHBFullProduct_primitive_mean_eq_offshift_ledger
    N m j τ z y u v w Q rho W hz hN]
  exact actualHBFullProduct_primitive_mean_bound
    N m j τ z y u v w Q rho W

end
end ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
