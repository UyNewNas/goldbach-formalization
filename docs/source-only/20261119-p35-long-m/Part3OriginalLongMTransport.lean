import ImbalancedChen.Part3OriginalAllChartLossyPair
import ImbalancedChen.Part3OriginalAdditionalSpectralCosts

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
An actual long-m Poisson block pays the inherited 3/4 transport by an
explicit x^δ squared-energy fee when Z<=V*x^δ. The physical cutoff also
places a necessary S bound on that branch. No full J or gap is proved.
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalLongMTransport20261119
open Finset
open scoped BigOperators MatrixGroups Classical
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalMaskedOuterEnergy20261102 OriginalCommonPoissonLanes20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalAdditionalSpectralCosts20261102
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalPostRemovalPair20261113
open OriginalAllChartLossyPair20261119 (transportedPrice all_chart_pair_with_transport)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- Explicit transport loss in the physical long-m branch, for both
actual level lower endpoints. This condition is not a spectral input. -/
theorem longM_transport_factor {δ x Q : ℝ} (hδ : 0 ≤ δ) (hx : 1 ≤ x)
    (D : OriginalData) (upper : Bool) (j : ℕ)
    (hQ : fixedZ D upper/2 ≤ Q)
    (hcut : fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^δ) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    (max 1 (threshold V Z/(Q+M)))^(3/4:ℝ) ≤ 2*x^δ := by
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let M := classicalMScale j
  have hz : 0 < Z := fixedZ_pos D upper
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have hv : 0 < V := hm.trans_le (classicalMScale_bounds j).2.2
  have hVM : V/2 ≤ M := (classicalMScale_bounds j).2.1
  have hq : 0 < Q := by linarith only [hQ, hz]
  have hden : 0 < Q+M := add_pos hq hm
  have hxp : 1 ≤ x^δ := Real.one_le_rpow hx hδ
  have hvfrac : V/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hVM, hq])
  have hzfrac : Z/(Q+M) ≤ 2 := (div_le_iff₀ hden).mpr (by
    linarith only [hQ, hm])
  have hzv : Z/V ≤ x^δ := (div_le_iff₀ hv).mpr (by
    simpa only [mul_comm] using hcut)
  have hsecond : (Z^2/V)/(Q+M) ≤ 2*x^δ := by
    have h := mul_le_mul hzfrac hzv (div_nonneg hz.le hv.le)
      (by norm_num : (0:ℝ) ≤ 2)
    convert h using 1 <;> ring
  have hw : threshold V Z/(Q+M) ≤ 2*x^δ := by
    apply (div_le_iff₀ hden).mpr
    unfold threshold
    apply max_le
    · have h := (div_le_iff₀ hden).mp hvfrac
      have hscale := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ 2*x^δ by
        nlinarith only [hxp]) hden.le
      exact h.trans hscale
    · exact (div_le_iff₀ hden).mp hsecond
  have hmax : max 1 (threshold V Z/(Q+M)) ≤ 2*x^δ :=
    max_le (by nlinarith only [hxp]) hw
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (le_max_left (1:ℝ) (threshold V Z/(Q+M)))
    (by norm_num : (3/4:ℝ) ≤ 1)
  have hpow' : (max 1 (threshold V Z/(Q+M)))^(3/4:ℝ) ≤
      max 1 (threshold V Z/(Q+M)) := by
    simpa only [Real.rpow_one] using hpow
  exact hpow'.trans hmax

/-- A necessary physical range for an occupied long-m block at the
original global cutoff. It explicitly prevents claiming all S. -/
theorem occupied_longM_scale_limit {δ η x : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hx : 1 ≤ x) (D : OriginalData) (upper : Bool) (j : ℕ)
    (hne : (commonMBlock (globalCutoff D x (η/2)) j).Nonempty)
    (hcut : fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^δ) :
    scaleS D.key ≤ 2*x^(δ+η/2) := by
  let S := scaleS D.key
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  have hs : 0 < S := scaleS_pos D.key
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hratio : D.cScale/D.bScale = S := by
    dsimp only [S]
    unfold OriginalData.cScale
    field_simp [D.bScale_pos.ne'] <;> ring
  have hv : V ≤ 2*x^(η/2)*S := by
    have h := commonMBlock_scale_le_twice_cutoff D hx (by positivity : 0 ≤ η/2) j hne
    rw [show 2*x^(η/2)*D.cScale/D.bScale =
      2*x^(η/2)*(D.cScale/D.bScale) by ring, hratio] at h
    exact h
  have hz : S^2 ≤ fixedZ D upper := by
    cases upper <;> simp only [fixedZ, Bool.false_eq_true, if_false, if_true] <;>
      nlinarith only [sq_nonneg S]
  have hpow : x^(η/2)*x^δ = x^(δ+η/2) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hprod := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hxpos.le δ)
  have hsquared : S^2 ≤ (2*x^(δ+η/2))*S := by
    calc
      S^2 ≤ fixedZ D upper := hz
      _ ≤ V*x^δ := hcut
      _ ≤ (2*x^(η/2)*S)*x^δ := hprod
      _ = (2*x^(δ+η/2))*S := by rw [← hpow]; ring
  by_contra hnot
  have hlt : 2*x^(δ+η/2) < S := lt_of_not_ge hnot
  have hprod' := mul_lt_mul_of_pos_right hlt hs
  nlinarith only [hsquared, hprod']

/-- The reduced Cauchy pair for an occupied long-m block at the same
global cutoff and same original m phase. The `2*x^δ` cost is retained. -/
theorem occupied_longM_pair {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (x : ℝ) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (j : ℕ) (ell : D4 → ℤ),
    1 ≤ x → (commonMBlock (globalCutoff D x (η/2)) j).Nonempty →
    fixedZ D upper ≤ (((2:ℕ)^j : ℕ) : ℝ)*x^δ →
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
  have hf1 := longM_transport_factor hδ hx D upper j (Q := Z/2) (le_refl _) hcut
  have hf2 := longM_transport_factor hδ hx D upper j (Q := Z) (by linarith only [hz]) hcut
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

end ImbalancedChen.Part3.OriginalLongMTransport20261119
end
