import ImbalancedChen.Part3OriginalLongMTransport

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Retain the existing 3/4 power instead of replacing it by the base.
This enlarges the physical long-m branch while keeping a separate x^δ
squared-energy fee. It does not supply the sharp J or a spectral gap.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalLongMSharpBudget20261119
open Finset
open scoped BigOperators MatrixGroups Classical
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalMaskedOuterEnergy20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalPostRemovalPair20261113
open OriginalAllChartLossyPair20261119 (transportedPrice all_chart_pair_with_transport)
open OriginalLongMTransport20261119 (occupied_longM_scale_limit)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- Keeping the 3/4 exponent allows Z/V up to x^(4δ/3) at the same
2*x^δ fee. Both actual level lower endpoints satisfy Q>=Z/2. -/
theorem longM_sharp_transport_factor {δ x Q : ℝ} (hδ : 0 ≤ δ) (hx : 1 ≤ x)
    (D : OriginalData) (upper : Bool) (j : ℕ)
    (hQ : fixedZ D upper/2 ≤ Q)
    (hcut : fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^(4*δ/3)) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    (max 1 (threshold V Z/(Q+M)))^(3/4:ℝ) ≤ 2*x^δ := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  let R : ℝ := x^(4*δ/3)
  have hz : 0 < Z := fixedZ_pos D upper
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hv : 0 < V := hm.trans_le (classicalMScale_bounds j).2.2
  have hVM : V/2 ≤ M := (classicalMScale_bounds j).2.1
  have hq : 0 < Q := by linarith only [hQ, hz]
  have hden : 0 < Q+M := add_pos hq hm
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hR : 1 ≤ R := Real.one_le_rpow hx (by positivity : 0 ≤ 4*δ/3)
  have hvfrac : V/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hVM, hq])
  have hzfrac : Z/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hQ, hm])
  have hzv : Z/V ≤ R := (div_le_iff₀ hv).mpr (by
    simpa only [R, mul_comm] using hcut)
  have hsecond : (Z^2/V)/(Q+M) ≤ 2*R := by
    have h := mul_le_mul hzfrac hzv (div_nonneg hz.le hv.le)
      (by norm_num : (0:ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hw : threshold V Z/(Q+M) ≤ 2*R := by
    apply (div_le_iff₀ hden).mpr
    unfold threshold
    apply max_le
    · have h := (div_le_iff₀ hden).mp hvfrac
      have hscale := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 2*R by
        nlinarith only [hR]) hden.le
      exact h.trans hscale
    · exact (div_le_iff₀ hden).mp hsecond
  have hbase : max 1 (threshold V Z/(Q+M)) ≤ 2*R :=
    max_le (by nlinarith only [hR]) hw
  have hpow := Real.rpow_le_rpow (zero_le_one.trans (le_max_left _ _)) hbase
    (by norm_num : (0:ℝ) ≤ 3/4)
  have htwo : (2:ℝ)^(3/4:ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
      (show (3/4:ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using h
  have hRpow : R^(3/4:ℝ) = x^δ := by
    dsimp only [R]
    rw [← Real.rpow_mul hxpos.le]
    congr 1
    ring
  calc
    _ ≤ (2*R)^(3/4:ℝ) := hpow
    _ = (2:ℝ)^(3/4:ℝ) * x^δ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (zero_le_one.trans hR), hRpow]
    _ ≤ 2*x^δ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hxpos.le δ)

/-- The enlarged branch is still restricted by the original occupied
global cutoff; the complementary S range is not covered. -/
theorem occupied_sharp_longM_scale_limit {δ η x : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hx : 1 ≤ x) (D : OriginalData) (upper : Bool) (j : ℕ)
    (hne : (commonMBlock (globalCutoff D x (η/2)) j).Nonempty)
    (hcut : fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^(4*δ/3)) :
    scaleS D.key ≤ 2*x^(4*δ/3+η/2) := by
  exact occupied_longM_scale_limit (δ := 4*δ/3) (by positivity) hη hx D upper j hne hcut

/-- The inherited actual reduced pair is paid on the wider occupied
frequency branch, preserving both level intervals and row mass. -/
theorem occupied_sharp_longM_pair {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (x : ℝ) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (j : ℕ) (ell : D4 → ℤ),
    1 ≤ x → (commonMBlock (globalCutoff D x (η/2)) j).Nonempty →
    fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^(4*δ/3) →
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let F := mFactor D k upper (globalCutoff D x (η/2)) j ell
    let G := nFactor D r k upper negativeM ell
    (∑ a : Slots D k upper, F a * G a)^2 ≤
      ((2+Real.log (4*V+1))^2 *
        (((2*x^δ)*(C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M) +
          (2*x^δ)*(C*((1+Z)*(1+M))^ε*(Z+M)*M))/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*
        ∑ z : ↥(levels D k upper), rowMass D r k z.val) := by
  obtain ⟨C, cp, hpair⟩ := all_chart_pair_with_transport hε
  refine ⟨C, cp, ?_⟩
  intro D x r k upper negativeM j ell hx hne hcut
  dsimp only
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hp1 : 0 ≤ C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M := by positivity
  have hp2 : 0 ≤ C*((1+Z)*(1+M))^ε*(Z+M)*M := by positivity
  have hf1 := longM_sharp_transport_factor hδ hx D upper j (Q := Z/2) (le_refl _) hcut
  have hf2 := longM_sharp_transport_factor hδ hx D upper j (Q := Z) (by linarith only [hz]) hcut
  have h1 : transportedPrice C ε (Z/2) M W ≤
      (2*x^δ)*(C*((1+Z/2)*(1+M))^ε*(Z/2+M)*M) := by
    exact mul_le_mul_of_nonneg_right hf1 hp1
  have h2 : transportedPrice C ε Z M W ≤
      (2*x^δ)*(C*((1+Z)*(1+M))^ε*(Z+M)*M) := by
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
  exact (hpair D r k upper negativeM (globalCutoff D x (η/2)) j ell).trans hbound

end ImbalancedChen.Part3.OriginalLongMSharpBudget20261119
end
