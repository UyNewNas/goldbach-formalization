import ImbalancedChen.P2GammaJointUpperPayment
import ImbalancedChen.P2GammaOrderingStripPayment
import ImbalancedChen.P2OriginalChildPhysicalNormalization
import ImbalancedChen.P5PrimePairEndpointTransfer

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal old-pair family is pushed to the EXISTING manuscript Theta
using the EXISTING productWeight. Equal products keep the sum of their
original weights. The zero-mass branch is settled absolutely, using
positivity of the singular factor, totient and physical logarithm.

The positivity argument is the already used P zero_theta_units argument;
the new conversion here is its attachment to the joint Gamma source.
There is no division by Theta, no reciprocal-(p-1) replacement for the
singular factor, and no positive-mass relative-error conclusion.
The original rootLabels still use the t-dependent rootQ N t. This file
does not identify that value with Qphys on a selected policy family;
the actual common-Q selection and its source identity remain open.
-/

namespace ImbalancedChen.P2GammaPairThetaZero
noncomputable section
open scoped Classical BigOperators
open P2GammaJointLabels P2GammaJointUpperPayment
open P2GammaCompleteProductTrimPayment P2GammaLowerRejectedPayment
open P2GammaOrderingStripPayment
open P2EnhancedTwentyOneSameQWeighted (Theta Theta_pos)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P5OriginalU5CausalFinite (pairSupport)

/-- This is exactly the installed Theta on the product pushforward of
the original pair source, at ONE common physical Q. -/
def pairSourceTheta (N : ℕ) (Qphys : ℝ) (sigma : (ℕ × ℕ) → ℝ) : ℝ :=
  Theta N Qphys (P5PrimePairEndpoint.productImage (pairSupport N))
    (P5PrimePairEndpoint.productWeight (pairSupport N) sigma)

theorem pairSourceTheta_eq_label_sum (N : ℕ) (Qphys : ℝ)
    (sigma : (ℕ × ℕ) → ℝ) :
    pairSourceTheta N Qphys sigma =
      ∑ t ∈ pairSupport N,sigma t*thetaAtom N Qphys (t.1*t.2) := by
  rw [pairSourceTheta,Theta_eq_sum_atoms]
  exact P5PrimePairEndpoint.productWeight_sum (pairSupport N) sigma (thetaAtom N Qphys)

theorem pair_productWeight_nonneg (N : ℕ) (sigma : (ℕ × ℕ) → ℝ)
    (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t) (d : ℕ) :
    0 ≤ P5PrimePairEndpoint.productWeight (pairSupport N) sigma d := by
  apply Finset.sum_nonneg
  intro t ht
  exact hsigma t (Finset.mem_filter.mp ht).1

theorem pair_productWeight_pos_of_pos (N : ℕ) (sigma : (ℕ × ℕ) → ℝ)
    (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) (hpositive : 0 < sigma t) :
    0 < P5PrimePairEndpoint.productWeight (pairSupport N) sigma (t.1*t.2) := by
  apply Finset.sum_pos'
  · intro u hu
    exact hsigma u (Finset.mem_filter.mp hu).1
  · exact ⟨t,Finset.mem_filter.mpr ⟨ht,rfl⟩,hpositive⟩

/-- Positivity of the SAME original normalizer is obtained from a
positive actual pair weight; no count or distribution theorem is used. -/
theorem pairSourceTheta_pos {N : ℕ} (hN : 4 ≤ N) (Qphys : ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    (hlevel : ∀ t ∈ pairSupport N,1 < Qphys/((t.1*t.2 : ℕ) : ℝ))
    (hpositive : ∃ t ∈ pairSupport N,0 < sigma t) :
    0 < pairSourceTheta N Qphys sigma := by
  apply Theta_pos hN Qphys
  · intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    exact P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht
  · intro d hd
    exact pair_productWeight_nonneg N sigma hsigma d
  · intro d hd
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hd
    exact hlevel t ht
  · obtain ⟨t,ht,hpos⟩ := hpositive
    exact ⟨t.1*t.2,Finset.mem_image_of_mem _ ht,
      pair_productWeight_pos_of_pos N sigma hsigma ht hpos⟩

/-- The exact zero-mass alternative. It includes empty supports and
zero selectors. Positivity, rather than division by total mass, proves
that every original pair coefficient vanishes. -/
theorem pairSourceTheta_zero_iff {N : ℕ} (hN : 4 ≤ N) (Qphys : ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    (hlevel : ∀ t ∈ pairSupport N,1 < Qphys/((t.1*t.2 : ℕ) : ℝ)) :
    pairSourceTheta N Qphys sigma=0 ↔ ∀ t ∈ pairSupport N,sigma t=0 := by
  constructor
  · intro hzero t ht
    rcases eq_or_lt_of_le (hsigma t ht) with heq | hpos
    · exact heq.symm
    · have hp := pairSourceTheta_pos hN Qphys sigma hsigma hlevel ⟨t,ht,hpos⟩
      rw [hzero] at hp
      exact (lt_irrefl (0 : ℝ) hp).elim
  · intro hs0
    rw [pairSourceTheta_eq_label_sum]
    exact Finset.sum_eq_zero (fun t ht => by rw [hs0 t ht,zero_mul])

/-- Every subsequent arithmetic test vanishes on a zero-Theta family.
No smoothness, positivity or boundedness of that test is needed. -/
theorem outer_test_zero_of_Theta_zero {N : ℕ} (hN : 4 ≤ N) (Qphys : ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    (hlevel : ∀ t ∈ pairSupport N,1 < Qphys/((t.1*t.2 : ℕ) : ℝ))
    (hzero : pairSourceTheta N Qphys sigma=0) (F : (ℕ × ℕ) → ℝ) :
    (∑ t ∈ pairSupport N,sigma t*F t)=0 := by
  have hs0 := (pairSourceTheta_zero_iff hN Qphys sigma hsigma hlevel).mp hzero
  exact Finset.sum_eq_zero (fun t ht => by rw [hs0 t ht,zero_mul])

theorem originalJointUpperError_zero_of_Theta_zero {N : ℕ} (hN : 4 ≤ N)
    (Qphys : ℝ) (sigma : (ℕ × ℕ) → ℝ)
    (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    (hlevel : ∀ t ∈ pairSupport N,1 < Qphys/((t.1*t.2 : ℕ) : ℝ))
    (hzero : pairSourceTheta N Qphys sigma=0)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) :
    originalJointUpperError N moduli rho sigma T H δ K=0 := by
  rw [originalJointUpperError_eq_outer]
  exact outer_test_zero_of_Theta_zero hN Qphys sigma hsigma hlevel hzero _

/-- The lower-first plus upper/order rejected terms from Q16/Q17,
with precisely the same signed rho in all components. The original
low-product trim, which precedes this split, is a separate quantity. -/
def originalJointRejectedError (N : ℕ) (moduli : Finset ℕ) (rho : ℕ → ℝ)
    (sigma : (ℕ × ℕ) → ℝ) (T H δ : ℝ) (K : ℕ) : ℝ :=
  ∑ t ∈ pairSupport N,sigma t*
    ((∑ q ∈ moduli,rho q*originalLowerRejectedKernel N t T H δ K q)+
      originalRemainingRejectedError N t moduli rho T H δ K)

/-- Absolute zero for the complete Q rejected source at zero mass.
The conclusion is proved without a normalized quotient or asymptotic. -/
theorem originalJointRejectedError_zero_of_Theta_zero {N : ℕ} (hN : 4 ≤ N)
    (Qphys : ℝ) (sigma : (ℕ × ℕ) → ℝ)
    (hsigma : ∀ t ∈ pairSupport N,0 ≤ sigma t)
    (hlevel : ∀ t ∈ pairSupport N,1 < Qphys/((t.1*t.2 : ℕ) : ℝ))
    (hzero : pairSourceTheta N Qphys sigma=0)
    (moduli : Finset ℕ) (rho : ℕ → ℝ) (T H δ : ℝ) (K : ℕ) :
    |originalJointRejectedError N moduli rho sigma T H δ K|=0 := by
  rw [originalJointRejectedError,
    outer_test_zero_of_Theta_zero hN Qphys sigma hsigma hlevel hzero,abs_zero]

end
end ImbalancedChen.P2GammaPairThetaZero
