import ImbalancedChen.Part3ActualLambdaPrincipalDivisorBinding
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original (15), actual same-profile principal core. The q,d repetitions,
reciprocal totients and literal signed Lambda are proved finite costs;
the weighted variance is the actual output of (14), not a new premise.
-/

namespace ImbalancedChen.Part3.ActualPrincipalCoreFiniteBoundSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open OriginalSamePsiS1OwnedAtlas MediumActualPsiPreliminaryDispersion20261028
open OriginalGevreyFinalPsi20261028 OriginalMediumPrincipalFiniteCRT
open ActualFilteredPrimitiveSWSourceOnly ActualCrudeWeightedVarianceSourceOnly
open ActualLowConductorQuotientSumSourceOnly ActualMediumVarianceAtomBindingSourceOnly
open ActualPrincipalGramVarianceBoundSourceOnly ActualLambdaPrincipalDivisorBindingSourceOnly

/-- Exact diagonal insertion for one actual q,d fibre. -/
theorem actual_principal_point_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    {p : ℕ × ℕ} (hp : p ∈ actualQD atom k) :
    paperQWeight atom p.1 * ((p.1*p.2).totient : ℝ) *
      paperPrincipalVariance atom.alphaCarrier atom.alpha (p.1*p.2)
        (dyadicWindow k.w) (originalLambda atom z k p.2) ≤
      2/(keyY atom k*(roughNat k : ℝ))*
        ∑ r ∈ dyadicWindow k.w, tau (p.1*p.2)^4*tau r^4*filteredVariance atom (p.1*p.2) r := by
  let ell := p.1*p.2
  let G : ℝ := ∑ r ∈ dyadicWindow k.w,
    ‖originalLambda atom z k p.2 r‖^2*filteredVariance atom ell r/((ell*r).totient : ℝ)^2
  have he : 0 < ell := (actualQD_geometry hA k hp).2.2.1
  have hR : ∀ r ∈ dyadicWindow k.w, 0 < r := fun r hr => (rough_window_bounds k hr).1
  have hGram := actual_paperPrincipalVariance_bound atom he (dyadicWindow k.w) hR
    (originalLambda atom z k p.2)
  rw [rough_window_card] at hGram
  have hG : 0 ≤ G := Finset.sum_nonneg (fun r hr =>
    div_nonneg (mul_nonneg (sq_nonneg _) (filteredVariance_nonneg _ _ _)) (sq_nonneg _))
  have hw0 : 0 ≤ paperQWeight atom p.1 := paperPsi_nonneg _
  have hw1 : paperQWeight atom p.1 ≤ 1 := paperPsi_le_one _
  have hphi : 0 ≤ (ell.totient : ℝ) := Nat.cast_nonneg _
  have hRG : 0 ≤ (roughNat k : ℝ)*G := mul_nonneg (Nat.cast_nonneg _) hG
  have hY : 0 < keyY atom k := by
    dsimp only [keyY,keyD]
    have hq := hA.2.2.1
    positivity
  have hRR : (0 : ℝ) < roughNat k := by exact_mod_cast roughNat_pos k
  calc
    _ ≤ paperQWeight atom p.1*(ell.totient : ℝ)*((roughNat k : ℝ)*G) :=
      mul_le_mul_of_nonneg_left hGram (mul_nonneg hw0 hphi)
    _ ≤ (ell.totient : ℝ)*((roughNat k : ℝ)*G) := by
      have h := mul_le_mul_of_nonneg_right hw1 (mul_nonneg hphi hRG)
      simpa only [one_mul,mul_assoc] using h
    _ = ∑ r ∈ dyadicWindow k.w,
        ((ell.totient : ℝ)*(roughNat k : ℝ)*‖originalLambda atom z k p.2 r‖^2 /
          ((ell*r).totient : ℝ)^2)*filteredVariance atom ell r := by
      dsimp only [G]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ r ∈ dyadicWindow k.w,
        (2/(keyY atom k*(roughNat k : ℝ))*tau ell^4*tau r^4)*filteredVariance atom ell r :=
      Finset.sum_le_sum (fun r hr => mul_le_mul_of_nonneg_right
        (actual_lambda_phi_diagonal_le hA z k hp hr) (filteredVariance_nonneg _ _ _))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- This is the finite principal-core form of (15), with the independently
defined paperPsi q weight, actual Lambda and q,d carrier. Each repeated
ell is paid by its proved tau(ell) fibre multiplicity, producing weight 5. -/
theorem principalCore_le_weighted_variances {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (z : ℝ) (k : Key) :
    principalCore atom z k ≤
      2/(keyY atom k*(roughNat k : ℝ))*
        ∑ r ∈ dyadicWindow k.w, tau r^4*
          weightedVariance atom (actualVarianceCap atom k) r 5 := by
  have hY : 0 < keyY atom k := by
    dsimp only [keyY,keyD]
    have hq := hA.2.2.1
    positivity
  have hRR : (0 : ℝ) < roughNat k := by exact_mod_cast roughNat_pos k
  have hc : 0 ≤ 2/(keyY atom k*(roughNat k : ℝ)) := by positivity
  unfold principalCore
  calc
    _ ≤ ∑ p ∈ actualQD atom k, 2/(keyY atom k*(roughNat k : ℝ))*
        ∑ r ∈ dyadicWindow k.w, tau (p.1*p.2)^4*tau r^4*filteredVariance atom (p.1*p.2) r :=
      Finset.sum_le_sum (fun p hp => actual_principal_point_le hA z k hp)
    _ = 2/(keyY atom k*(roughNat k : ℝ))*
        ∑ r ∈ dyadicWindow k.w, tau r^4*
          ∑ p ∈ actualQD atom k, tau (p.1*p.2)^4*filteredVariance atom (p.1*p.2) r := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hc
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (tau_nonneg r) 4)
      have h := actual_qd_sum_le hA k (fun ell => tau ell^4*filteredVariance atom ell r)
        (fun ell => mul_nonneg (pow_nonneg (tau_nonneg ell) 4) (filteredVariance_nonneg _ _ _))
      refine h.trans_eq ?_
      unfold weightedVariance
      apply Finset.sum_congr rfl
      intro ell hell
      ring

/-- Direct original-SW insertion at the actual medium cap. This retains
the literal rough divisor mean, to be paid by its fixed ordinary moment. -/
theorem uniformAuxiliarySW_actual_principalCore_finite
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hsigma : 0 < sigma)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ z : ℝ, ∀ k ∈ originalNumericKeys (F i) z,
        principalCore (F i) z k ≤
          (2*C*(Nat.floor (2*(F i).U) : ℝ)^2 /
            (keyY (F i) k*(roughNat k : ℝ)*(Real.log (F i).scale)^A))*
              ∑ r ∈ dyadicWindow k.w, tau r^(4+2*C0) := by
  obtain ⟨C,hC,x0,hx0,hvariance⟩ :=
    uniformAuxiliarySW_actual_medium_atom_variance F B C0 sigma kappa c0 hadmissible hSW
      hsigma A hA 5
  refine ⟨C,hC,x0,hx0,?_⟩
  intro i hx z k hk
  have hY : 0 < keyY (F i) k := by
    dsimp only [keyY,keyD]
    have hq := (hadmissible i).2.2.1
    positivity
  have hRR : (0 : ℝ) < roughNat k := by exact_mod_cast roughNat_pos k
  have hX : 0 < (F i).scale := (zero_lt_one.trans hx0).trans_le hx
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  refine (principalCore_le_weighted_variances (hadmissible i) z k).trans ?_
  calc
    _ ≤ 2/(keyY (F i) k*(roughNat k : ℝ))*
        ∑ r ∈ dyadicWindow k.w, tau r^4*
          (C*tau r^(2*C0)*(Nat.floor (2*(F i).U) : ℝ)^2/(Real.log (F i).scale)^A) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hvariance i hx z k hk r
        (rough_window_bounds k hr).1) (pow_nonneg (tau_nonneg r) 4)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [pow_add]
      ring

end
end ImbalancedChen.Part3.ActualPrincipalCoreFiniteBoundSourceOnly
