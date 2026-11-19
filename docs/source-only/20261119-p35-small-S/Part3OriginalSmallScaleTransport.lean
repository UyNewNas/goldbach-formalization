import ImbalancedChen.Part3OriginalAllChartLossyPair
import ImbalancedChen.Part3OriginalMaskedOuterEnergy

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
On the physical subfamily S <= x^(δ/2), pay the existing 3/4 transport
loss by 6*x^δ. This is an additional, explicit squared-energy fee and
is not a sharp J estimate or the manuscript's 7/32 spectral gap.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalSmallScaleTransport20261119
open Finset
open scoped BigOperators MatrixGroups Classical
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalMaskedOuterEnergy20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalPostRemovalPair20261113
open OriginalAllChartLossyPair20261119 (transportedPrice all_chart_pair_with_transport)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- This physical subrange pays the transport factor at either of the
two original J lower endpoints, and for any larger positive endpoint. -/
theorem smallS_transport_factor {δ x Q : ℝ} (hδ : 0 ≤ δ) (hx : 1 ≤ x)
    (D : OriginalData) (upper : Bool) (j : ℕ)
    (hS : scaleS D.key ≤ x^(δ/2)) (hQ : fixedZ D upper/2 ≤ Q) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    (max 1 (threshold V Z/(Q+M)))^(3/4:ℝ) ≤ 6*x^δ := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  let S := scaleS D.key
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxp : 1 ≤ x^δ := Real.one_le_rpow hx hδ
  have hspos : 0 < S := scaleS_pos D.key
  have hhalf : 0 ≤ x^(δ/2) := Real.rpow_nonneg hxpos.le _
  have hpow : (x^(δ/2))^2 = x^δ := by
    rw [pow_two, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hs2 : S^2 ≤ x^δ := by
    have h := mul_nonneg (sub_nonneg.mpr hS) (add_nonneg hhalf hspos.le)
    nlinarith only [h, hpow]
  have hzpos : 0 < Z := fixedZ_pos D upper
  have hz2 : Z ≤ 2*S^2 := by
    cases upper <;> simp only [Z, fixedZ, Bool.false_eq_true, if_false, if_true] <;>
      nlinarith only [sq_nonneg S]
  have hzbound : Z ≤ 2*x^δ := by nlinarith only [hz2, hs2]
  have hvNat : 1 ≤ (2:ℕ)^j := pow_pos (by norm_num) j
  have hvone : 1 ≤ V := by dsimp only [V]; exact_mod_cast hvNat
  have hv : 0 < V := zero_lt_one.trans_le hvone
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hVM : V/2 ≤ M := (classicalMScale_bounds j).2.1
  have hqpos : 0 < Q := by linarith only [hQ, hzpos]
  have hden : 0 < Q+M := add_pos hqpos hm
  have hvfrac : V/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hVM, hqpos])
  have hzfrac : Z/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hQ, hm])
  have hzv : Z/V ≤ Z := (div_le_iff₀ hv).mpr (by
    have h := mul_nonneg hzpos.le (sub_nonneg.mpr hvone)
    nlinarith only [h])
  have hsecond : (Z^2/V)/(Q+M) ≤ 2*Z := by
    have h := mul_le_mul hzfrac hzv (div_nonneg hzpos.le hv.le)
      (by norm_num : (0:ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hw : threshold V Z/(Q+M) ≤ 2+2*Z := by
    apply (div_le_iff₀ hden).mpr
    unfold threshold
    apply max_le
    · have h := (div_le_iff₀ hden).mp hvfrac
      nlinarith only [h, mul_nonneg hzpos.le hden.le]
    · have h := (div_le_iff₀ hden).mp hsecond
      nlinarith only [h, hden.le]
  have hmax : max 1 (threshold V Z/(Q+M)) ≤ 6*x^δ := by
    apply max_le
    · nlinarith only [hxp]
    · nlinarith only [hw, hzbound, hxp]
  have hfactor := Real.rpow_le_rpow_of_exponent_le
    (le_max_left (1:ℝ) (threshold V Z/(Q+M)))
    (by norm_num : (3/4:ℝ) ≤ 1)
  have hfactor' : (max 1 (threshold V Z/(Q+M)))^(3/4:ℝ) ≤
      max 1 (threshold V Z/(Q+M)) := by
    simpa only [Real.rpow_one] using hfactor
  exact hfactor'.trans hmax

/-- Actual reduced pair on both original charts when S is small enough
to pay the transport charge. The previous common phase and n-side mass
are unchanged; epsilon and delta remain separate budget parameters. -/
theorem smallS_pair {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (x : ℝ) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ),
    1 ≤ x → scaleS D.key ≤ x^(δ/2) →
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    (∑ a : Slots D k upper, F a * G a)^2 ≤
      ((2+Real.log (4*V+1))^2 *
        (((6*x^δ)*(C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M) +
          (6*x^δ)*(C*((1+Z)*(1+M))^ε*(Z+M)*M))/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*
        ∑ z : ↥(levels D k upper), rowMass D r k z.val) := by
  obtain ⟨C, cp, hpair⟩ := all_chart_pair_with_transport hε
  refine ⟨C, cp, ?_⟩
  intro D x r k upper negativeM J j ell hx hS
  dsimp only
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hp1 : 0 ≤ C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M := by positivity
  have hp2 : 0 ≤ C*((1+Z)*(1+M))^ε*(Z+M)*M := by positivity
  have hf1 := smallS_transport_factor hδ hx D upper j hS (Q := Z/2) (le_refl _)
  have hf2 := smallS_transport_factor hδ hx D upper j hS (Q := Z) (by linarith only [hz])
  have h1 : transportedPrice C ε (Z/2) M W ≤
      (6*x^δ)*(C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M) := by
    exact mul_le_mul_of_nonneg_right hf1 hp1
  have h2 : transportedPrice C ε Z M W ≤
      (6*x^δ)*(C*((1+Z)*(1+M))^ε*(Z+M)*M) := by
    exact mul_le_mul_of_nonneg_right hf2 hp2
  have hmass : 0 ≤ ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    apply Finset.sum_nonneg
    intro z _
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hL : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hcost : 0 ≤ (4*sieveConstant*(1+rowLength k/Z))*
      ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) sieveConstant_pos.le)
      (by positivity)) hmass
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num : (0:ℝ) ≤ 4))
      (sq_nonneg (2+Real.log (4*V+1)))) hcost
  exact (hpair D r k upper negativeM J j ell).trans hbound

end ImbalancedChen.Part3.OriginalSmallScaleTransport20261119
end
