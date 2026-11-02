import ImbalancedChen.P5UnroughMobiusSmoothed
import ImbalancedChen.Part3ActualRoughSharpUnsmoothing
import PrimeNumberTheoremAnd.SmoothExistence

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Zero-cutoff adaptation of the archived 20261027 GlobalClosure draft.
-- That draft's fixed roughZ x conclusion cannot supply unrestricted mu.
-- This copy consumes the actual zero-cutoff smoothed theorem, the existing
-- signed unsmoothing theorem and the primary SmoothExistence construction.
-- Every original modulus, nonprincipal character and endpoint stays uniform.

namespace ImbalancedChen.Part3.UnroughMobiusSharp20261102
noncomputable section
open Classical Set MeasureTheory Filter Topology
open scoped BigOperators
open RoughSlotSmoothedPerron20261026b
open RoughSlotPerronTruncation20261026b
open ActualRoughSharpUnsmoothing20261027
open UnroughMobiusSmoothed20261102
open ActualRoughContourParameters20261026b

def originalSmoothingKernel : ℝ → ℝ := Classical.choose SmoothExistence

theorem originalSmoothingKernel_properties :
    ContDiff ℝ 1 originalSmoothingKernel ∧
    (∀ x > 0, 0 ≤ originalSmoothingKernel x) ∧
    Function.support originalSmoothingKernel ⊆ Icc (1/2) 2 ∧
    (∫ x in Ioi (0 : ℝ), originalSmoothingKernel x/x) = 1 := by
  obtain ⟨hC,hpos,hsupp,hmass⟩ := Classical.choose_spec SmoothExistence
  refine ⟨hC.of_le (by simp), fun x _ => hpos x, hsupp, ?_⟩
  rw [← integral_Ici_eq_integral_Ioi]
  exact hmass

-- The sharp theorem uses the actual contour estimate directly. There is
-- no hypothesis asserting a smoothed, sharp or AP cancellation bound.
theorem exists_unrough_sharp_character_SW
    (A B L θ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x : ℝ, x0 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log x)^B →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (useMu : Bool) (τ U X : ℝ), |τ| ≤ (Real.log x)^L →
      0 < U → x^θ ≤ X → X ≤ x →
      ‖roughSharpSum useMu χ 0 τ U X‖ ≤
        K*X*(Real.log x)^(-A) := by
  obtain ⟨hν,hpos,hsupp,hmass⟩ := originalSmoothingKernel_properties
  obtain ⟨K,hK,xs,hxs,hsm⟩ := exists_actual_smoothed_unrough_character_SW
    A B L (A+1) θ hA hB hL (by linarith) hθ
      originalSmoothingKernel hν hpos hsupp hmass
  have hdecay : Tendsto (fun x : ℝ => (Real.log x)^A/x^θ)
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop A hθ).tendsto_div_nhds_zero
  have hpay := hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hlog : ∀ᶠ x : ℝ in atTop, 2 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)
  obtain ⟨r,hr⟩ := eventually_atTop.mp (hpay.and hlog)
  refine ⟨K+4*Real.log 2+4,by positivity,max xs (max r 2),?_,?_⟩
  · exact hxs.trans_le (le_max_left _ _)
  intro x hx q _ hq χ hχ useMu τ U X hτ hU hXlo hXhi
  have hxsm : xs ≤ x := (le_max_left _ _).trans hx
  have hxr : r ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hx2 : 2 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hg := hr x hxr
  have hlogpos : 0 < Real.log x := by linarith [hg.2]
  have hlogone : 1 ≤ Real.log x := by linarith [hg.2]
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < X := (Real.rpow_pos_of_pos hxpos θ).trans_le hXlo
  have hε : 0 < (Real.log x)^(-(A+1)) := Real.rpow_pos_of_pos hlogpos _
  have hε1 : (Real.log x)^(-(A+1)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith [hg.2]) (by linarith)
  have hεA : (Real.log x)^(-(A+1)) ≤ (Real.log x)^(-A) :=
    Real.rpow_le_rpow_of_exponent_le hlogone (by linarith)
  have hunit : 1 ≤ X*(Real.log x)^(-A) := by
    have hp : (Real.log x)^A ≤ X :=
      ((div_lt_one₀ (Real.rpow_pos_of_pos hxpos θ)).mp hg.1).le.trans hXlo
    rw [Real.rpow_neg hlogpos.le]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos A)).mpr (by simpa using hp)
  have hs := hsm x hxsm q hq χ hχ useMu τ U X hτ hU hXlo hXhi
  have hfinite := roughSmoothedSum_eq_finite useMu χ 0 τ U
    hsupp hε hε1 hXpos
  rw [← hfinite] at hs
  have hu := norm_roughSharpSum_le_smoothed useMu χ 0 τ U
    hpos hsupp hmass hε hε1 hXpos
  have he : 4*Real.log 2*((Real.log x)^(-(A+1)))*X ≤
      4*Real.log 2*(X*(Real.log x)^(-A)) := by
    have hh := mul_le_mul_of_nonneg_left hεA
      (show 0 ≤ 4*Real.log 2*X by positivity)
    nlinarith
  calc
    _ ≤ K*X*(Real.log x)^(-A) +
        4*Real.log 2*((Real.log x)^(-(A+1)))*X + 4 := by linarith
    _ ≤ K*X*(Real.log x)^(-A) +
        4*Real.log 2*(X*(Real.log x)^(-A)) + 4*(X*(Real.log x)^(-A)) := by
      linarith
    _ = _ := by ring

-- Both endpoints remain literal; the original individual interval is
-- represented by Ioc floor(X) floor(Y), now with no rough exclusion.
theorem exists_unrough_interval_character_SW
    (A B L θ : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ x : ℝ, x0 ≤ x → ∀ (q : ℕ) [NeZero q],
      (q : ℝ) ≤ (Real.log x)^B →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ (useMu : Bool) (τ U X Y : ℝ), |τ| ≤ (Real.log x)^L →
      0 < U → x^θ ≤ X → X ≤ Y → Y ≤ x →
      ‖∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊,
        coefficient useMu χ 0 τ U n‖ ≤
        K*(X+Y)*(Real.log x)^(-A) := by
  obtain ⟨K,hK,x0,hx0,hsharp⟩ :=
    exists_unrough_sharp_character_SW A B L θ hA hB hL hθ
  refine ⟨K,hK,x0,hx0,?_⟩
  intro x hx q _ hq χ hχ useMu τ U X Y hτ hU hXlo hXY hYhi
  rw [← roughSharpSum_sub_eq_Ioc useMu χ 0 τ U hXY]
  have hxbound := hsharp x hx q hq χ hχ useMu τ U X hτ hU hXlo (hXY.trans hYhi)
  have hybound := hsharp x hx q hq χ hχ useMu τ U Y hτ hU (hXlo.trans hXY) hYhi
  calc
    _ ≤ ‖roughSharpSum useMu χ 0 τ U Y‖ +
        ‖roughSharpSum useMu χ 0 τ U X‖ := norm_sub_le _ _
    _ ≤ K*Y*(Real.log x)^(-A) + K*X*(Real.log x)^(-A) := add_le_add hybound hxbound
    _ = _ := by ring

end
end ImbalancedChen.Part3.UnroughMobiusSharp20261102
