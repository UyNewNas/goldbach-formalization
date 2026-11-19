import ImbalancedChen.P3ActualPhysicalTotientConvolution
import ImbalancedChen.TotientReciprocalBudget
import Mathlib.Tactic

/-!
P3.6 — finite physical reciprocal-totient LOG budget for genuinely
one-bounded, signed, noninjective small/rough pair sources.

Frozen manuscript: chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b, PP completion
§1 and §3(T); the original physical modulus is the integer product.

This advances the previous pair-convolution majorant by PAYING its
component reciprocal-totient masses via the already installed finite
TotientReciprocalBudget theorem. The coefficient may be sign-dependent
on BOTH original factors, including a branch-selected Rosser small
coefficient; separation alpha(a)*beta(b) is NOT assumed.

It is NOT an identification of the frozen complete compiler rho_N:
its actual pair-source, source cap, global squarefree filter, and
restoring scalars must be supplied by further manuscript-internal work.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualSignedPairTotientCap
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualPhysicalTotientConvolution
open ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
open ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre

/-- The FINITE and already proved (in the pinned production source)
real reciprocal-totient cap, not an assumed analytic estimate. -/
def logTotientCap (D : ℕ) : ℝ :=
  4 * (1 + Real.log (max 1 (D : ℝ)))

theorem logTotientCap_nonneg (D : ℕ) : 0 ≤ logTotientCap D := by
  have hnonneg : 0 ≤
      ∑ d ∈ Finset.Icc 1 D, (Nat.totient d : ℝ)⁻¹ := by
    apply Finset.sum_nonneg
    intro d hd
    positivity
  exact hnonneg.trans (sum_reciprocal_totient_le_log D)

/-- An arbitrary SIGNED complex coefficient bounded by one on the
literal pair source has a two-log physical totient mass. In particular,
the small factor may depend on the SIGN of the rough factor. -/
theorem bounded_pair_physical_mass_le_log_caps
    (S : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℂ)
    (A B : ℕ)
    (hsource : S ⊆ (Finset.Icc 1 A).product (Finset.Icc 1 B))
    (hcoeff : ∀ x ∈ S, ‖c x‖ ≤ 1) :
    physicalComplexTotientMass (S.image pairModulus)
        (pairConvolution S c) ≤
      logTotientCap A * logTotientCap B := by
  classical
  have hpositive : ∀ x ∈ S, 0 < x.1 ∧ 0 < x.2 := by
    intro x hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hsource hx)
    exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp hb).1⟩
  have hA : (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) ≤
      logTotientCap A := sum_reciprocal_totient_le_log A
  have hB : (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) ≤
      logTotientCap B := sum_reciprocal_totient_le_log B
  calc
    _ ≤ ∑ x ∈ S, ‖c x‖ *
          ((Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹) :=
      pair_convolution_physical_mass_le S c hpositive
    _ ≤ ∑ x ∈ S,
          (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      have hweight : 0 ≤
          (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
        positivity
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hcoeff x hx) hweight
    _ ≤ ∑ x ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B),
          (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsource
        (fun x hx hxnot => by positivity)
    _ = (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) *
          (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap A *
          (∑ b ∈ Finset.Icc 1 B, (Nat.totient b : ℝ)⁻¹) := by
      exact mul_le_mul_of_nonneg_right hA
        (Finset.sum_nonneg (fun b hb => by positivity))
    _ ≤ logTotientCap A * logTotientCap B := by
      exact mul_le_mul_of_nonneg_left hB (logTotientCap_nonneg A)

/-- The original INTEGER-valued signed rho and exact physical phi
receive the same fully finite bound, not an alternative auxiliary rho. -/
theorem integer_pair_physical_mass_le_log_caps
    (S : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℤ)
    (A B : ℕ)
    (hsource : S ⊆ (Finset.Icc 1 A).product (Finset.Icc 1 B))
    (hcoeff : ∀ x ∈ S, ‖(c x : ℂ)‖ ≤ 1) :
    physicalReciprocalTotientMass
        (S.image pairModulus) (signedIntegerPairRho S c) ≤
      logTotientCap A * logTotientCap B := by
  rw [physicalIntegerMass_eq_complexMass]
  have hcast : (fun q => ((signedIntegerPairRho S c q : ℤ) : ℂ)) =
      pairConvolution S (fun x => (c x : ℂ)) := by
    funext q
    exact signedIntegerPairRho_cast S c q
  rw [hcast]
  exact bounded_pair_physical_mass_le_log_caps S
    (fun x => (c x : ℂ)) A B hsource hcoeff

/-- The PRECISE previous three-ordered-prime-box + literal HB
offshift primitive mean, on the same physical signed integer rho.
The two-log factor is now explicitly paid for this admitted pair
source; the original positional coefficient L1 remains independent. -/
theorem original_threeHB_mean_le_log_caps
    (N m j A B : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (S : Finset (ℕ × ℕ)) (c : (ℕ × ℕ) → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N)
    (hsource : S ⊆ (Finset.Icc 1 A).product (Finset.Icc 1 B))
    (hcoeff : ∀ x ∈ S, ‖(c x : ℂ)‖ ≤ 1) :
    ‖fixedThreeHBOffshiftMean N m j τ z y u v w
        (S.image pairModulus) (signedIntegerPairRho S c) W‖ ≤
      (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            ‖hbPositionalMass m j z y W a b d‖) *
        (logTotientCap A * logTotientCap B) := by
  have hmass_nonneg : 0 ≤
      (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            ‖hbPositionalMass m j z y W a b d‖) := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    exact Finset.sum_nonneg (fun d hd => norm_nonneg _)
  calc
    _ ≤ (∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
          ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
            ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
              ‖hbPositionalMass m j z y W a b d‖) *
          physicalReciprocalTotientMass
            (S.image pairModulus) (signedIntegerPairRho S c) :=
      fixedThreeHBOffshiftMean_norm_le N m j τ z y u v w
        (S.image pairModulus) (signedIntegerPairRho S c) W hz hN
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integer_pair_physical_mass_le_log_caps S c A B hsource hcoeff)
      hmass_nonneg

end
end ImbalancedChen.P3ActualSignedPairTotientCap
