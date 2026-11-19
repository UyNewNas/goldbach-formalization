import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair
import ImbalancedChen.Part3OriginalNativeJInitialRegion

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
All physical Z charts with the explicit 3/4 weight-transport loss.
This is not the sharp J estimate, the spectral gap, or (24).
-/

noncomputable section
namespace ImbalancedChen.Part3.OriginalAllChartLossyPair20261119
open Finset
open scoped BigOperators MatrixGroups Classical
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102
open OriginalExceptionalJNativeCompletion20261110 (pascadiJ classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalNativeJInitialRegion20261113 (initial_region)
open OriginalFullPositiveInitialMean20261113 (transport)
open OriginalSwitchedNativePrefixEnergy20261113 (full_window)
open OriginalSwitchedTwistedBaseline20261113 (zero_frequency)
open OriginalExceptionalPostRemovalPair20261113
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)
open P3NativePeriod64SamplingSourceOnly (D4)

/-- The explicit 3/4 transport charge multiplies the initial J price.
It is not uniform in the physical scales. -/
def transportedPrice (C ε Q M X : ℝ) : ℝ :=
  (max 1 (X/(Q+M)))^(3/4:ℝ) *
    (C*((1+Q)*(1+M))^ε*(Q+M)*M)

/-- The actual complete m-side level energy at an arbitrary positive
weight, with the loss displayed rather than hidden in a constant. -/
theorem full_J_with_transport {ε : ℝ} (ep : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (Q X ω : ℝ), 0 < Q → 0 < X →
      pascadiJ (classicalLevels Q) X j ω ≤
        transportedPrice C ε Q (classicalMScale j) X := by
  obtain ⟨C, cp, hJ⟩ := initial_region ep 1 (by norm_num)
  refine ⟨C, cp, ?_⟩
  intro j Q X ω hq hx
  let M := classicalMScale j
  let X₀ := Q+M
  have hm : 0 < M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have h₀ : 0 < X₀ := add_pos hq hm
  have ha : 0 < (2:ℕ)^j := pow_pos (by norm_num) j
  have hmove := transport (classicalLevels Q) (X := X₀) (Y := X) h₀ hx ω
    ha (2^(j+1)) 0
  simp only [full_window,zero_frequency] at hmove
  have hbase := hJ (classicalLevels Q) j Q X₀ ω hq h₀ (fun _ h => h)
    (by simp only [one_mul, X₀])
  have hfactor : 0 ≤ (max 1 (X/X₀))^(3/4:ℝ) :=
    Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have h := hmove.trans (mul_le_mul_of_nonneg_left hbase hfactor)
  simpa only [transportedPrice, X₀, M] using h

/-- Unrestricted physical charts and both frequency signs, for the
already reduced n-side pair. The same original phase pays both terms. -/
theorem all_chart_pair_with_transport {ε : ℝ} (ep : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
      (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ),
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
    let M := classicalMScale j
    let W := threshold V Z
    let F := mFactor D k upper J j ell
    let G := nFactor D r k upper negativeM ell
    (∑ a : Slots D k upper, F a * G a)^2 ≤
      ((2+Real.log (4*V+1))^2 *
        ((transportedPrice C ε (Z/2) M W + transportedPrice C ε Z M W)/4)) *
      ((4*sieveConstant*(1+rowLength k/Z))*
        ∑ z : ↥(levels D k upper), rowMass D r k z.val) := by
  obtain ⟨C, cp, hJ⟩ := full_J_with_transport ep
  refine ⟨C, cp, ?_⟩
  intro D r k upper negativeM J j ell
  dsimp only
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ) : ℝ)
  let W := threshold V Z
  have hz : 0 < Z := fixedZ_pos D upper
  have hv : 0 < V := by dsimp [V]; positivity
  have hw : 0 < W := threshold_pos hv
  obtain ⟨ω, hp, hpair⟩ := original_pair_to_pascadi D r k upper negativeM J j ell
  have h1 := hJ j (Z/2) W ω (by linarith only [hz]) hw
  have h2 := hJ j Z W ω hz hw
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
  exact hp.trans (hpair.trans hbound)

end ImbalancedChen.Part3.OriginalAllChartLossyPair20261119
end
