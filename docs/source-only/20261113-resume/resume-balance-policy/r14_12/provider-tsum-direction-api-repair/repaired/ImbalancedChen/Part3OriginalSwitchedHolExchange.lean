import ImbalancedChen.Part3OriginalSameInfinityPeriodTrace
import ImbalancedChen.Part3OriginalSwitchedMaassExchange

/-! A single summable even-weight majorant for all period modes
and the weighted Petersson sector of both physical cutoffs. -/
namespace ImbalancedChen.Part3.OriginalSwitchedHolExchange20261113
noncomputable section
open Set Complex MeasureTheory Finset
open scoped BigOperators ComplexConjugate
open OriginalSwitchedCutoffModes20261113 OriginalSwitchedModeTransforms20261113
open OriginalSwitchedCutoffFamily20261113 (profile)
open OriginalSameInfinityWeightedHol20261113 (holSum basisTerm)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicBasisMass20261112 (basisCost)
open ActualPositiveHolomorphicWeights20261112
open OriginalFullModulusTestJets20261102 (spectralTest_div_q_integrable spectralTest_tsupport_strict)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open private cost from ImbalancedChen.Part3OriginalSameInfinityPeriodTrace
open private identical_norm from ImbalancedChen.Part3OriginalSwitchedModeTransforms
open private rectangle from ImbalancedChen.Part3OriginalSwitchedMaassExchange

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem joint_moments {V : ℝ} (vp : 0<V) :
    ∃ B : ℕ→ℝ,Summable B ∧ (∀ j,0≤B j) ∧ ∀ k : ℤ,∀ j : ℕ,
      ((2*j+1:ℕ):ℝ)*‖moment (2*j+1) (spectralTest (mode k) V)‖≤B j := by
  let F := fun q : ℝ => ‖spectralTest (mode 0) V q/(q:ℂ)‖
  let x := 8*V
  let K := expMass (16*V)*(∫ t in Ioi (0:ℝ),F t)
  have xp : 0≤x := by dsimp [x];positivity
  have kp : 0≤K := mul_nonneg (expMass_nonneg _) (integral_nonneg fun t => norm_nonneg _)
  have I := (spectralTest_div_q_integrable (mode 0) vp).norm.integrableOn (s:=Ioi (0:ℝ))
  have M (k : ℤ) (h : ℕ) : ‖moment h (spectralTest (mode k) V)‖≤K*x^h/(h.factorial:ℝ) := by
    let D := ((16*V/2)^h/(h.factorial:ℝ))*expMass (16*V)
    calc
      _ ≤ ∫ t in Ioi (0:ℝ),D*F t := by
        apply norm_integral_le_of_norm_le (I.const_mul D)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        by_cases z : spectralTest (mode k) V t=0
        · simp only [z,mul_zero,zero_div,norm_zero]
          dsimp only [D,F]
          exact mul_nonneg (mul_nonneg (by positivity) (expMass_nonneg _)) (norm_nonneg _)
        · rw [mul_div_assoc,norm_mul]
          have eq : ‖spectralTest (mode k) V t/(t:ℂ)‖=F t := by
            simp only [F,norm_div,identical_norm k V t]
          rw [eq]
          exact mul_le_mul_of_nonneg_right (intJ_bound h ht.le
            (spectralTest_tsupport_strict _ vp (subset_tsupport _ z)).2.le) (norm_nonneg _)
      _ = _ := by
        rw [integral_const_mul]
        dsimp only [D,K,x]
        rw [show 16*V/2=8*V by ring]
        ring
  let b := fun j : ℕ => (K*x)*(x^(2*j)/((2*j).factorial:ℝ))
  have S := (Real.summable_pow_div_factorial x).comp_injective
    (show Function.Injective (fun j : ℕ => 2*j) from fun _ _ h => by omega)
  refine ⟨b,S.mul_left _,fun _ => mul_nonneg (mul_nonneg kp xp) (div_nonneg (pow_nonneg xp _) (Nat.cast_nonneg _)),?_⟩
  intro k j
  apply (mul_le_mul_of_nonneg_left (M k (2*j+1)) (Nat.cast_nonneg _)).trans_eq
  rw [Nat.factorial_succ,pow_succ]
  dsimp only [b]
  push_cast
  field_simp [show (2*(j:ℝ)+1)≠0 by positivity,
    show ((2*j).factorial:ℝ)≠0 by exact_mod_cast Nat.factorial_ne_zero (2*j)] <;> ring

theorem hol_exchange (q m n : ℕ+) (s : Bool) (L Y : ℝ) (yp : 0<Y) :
    HasSum (fun k : ℤ => coefficient s L k*holSum q m n (spectralTest (mode k) Y⁻¹))
      (holSum q m n (fun x => profile s L (Y*x))) := by
  let c := coefficient s L
  let Φ := fun k : ℤ => spectralTest (mode k) Y⁻¹
  let f := fun x => profile s L (Y*x)
  let F := fun k (j : ℕ) => c k*∑ i,basisTerm q m n (Φ k) j i
  let D := (basisCost q.val m.val 1+basisCost q.val n.val 1)/Real.pi
  have dp : 0≤D := by dsimp [D,basisCost];positivity
  obtain ⟨B,S,nn,h⟩ := joint_moments (inv_pos.mpr yp)
  obtain ⟨_,_,b⟩ := mode_budget 0
  have Z : Summable (fun k => ‖c k‖) := by simpa only [pow_zero,one_mul,c] using (b s L).1
  have SF : Summable (Function.uncurry F) := by
    apply Summable.of_norm
    apply (rectangle Z (S.mul_left D) (fun _ => norm_nonneg _) (fun j => mul_nonneg dp (nn j))).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    rintro ⟨k,j⟩
    rw [Function.uncurry,F,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sum_le _ _).trans ((cost q m n (Φ k) j).trans (mul_le_mul_of_nonneg_left (h k j) dp))
  have lim (j : ℕ) (i : BasisIndex q.val (j+1)) :
      HasSum (fun k => c k*basisTerm q m n (Φ k) j i) (basisTerm q m n f j i) := by
    unfold basisTerm
    exact ((((tested_transforms s L Y yp).2.2.1 j).mul_left _).mul_right _).congr_fun
      (fun k => by dsimp only [Φ,c,f];ring)
  have row (j : ℕ) : (∑' k,F k j)=∑ i,basisTerm q m n f j i := by
    have T := hasSum_sum (s:=(univ:Finset (BasisIndex q.val (j+1)))) (fun i _ => lim j i)
    simpa only [F,Finset.mul_sum] using T.tsum_eq
  have H := SF.prod.hasSum
  rw [SF.tsum_comm.symm] at H
  simp_rw [row] at H
  simpa only [F,holSum,tsum_mul_left,c,Φ,f] using H

end
end ImbalancedChen.Part3.OriginalSwitchedHolExchange20261113
