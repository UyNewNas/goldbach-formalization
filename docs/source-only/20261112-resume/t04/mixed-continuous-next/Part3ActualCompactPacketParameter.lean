import ImbalancedChen.Part3ActualMarkedHorocycleSupport
import ImbalancedChen.Part3ActualRegularEisensteinQuotient
import ImbalancedChen.Part3ActualNativeHorocycleParameter
import Batteries.Tactic.OpenPrivate

/-! Local parameter bounds for the actual continued cusp columns on
compact spatial supports. The derivative estimate integrates against
the norm of the original packet on the finite physical quotient. -/
namespace ImbalancedChen.Part3.ActualCompactPacketParameter20261112

noncomputable section
open Set Filter Topology Metric MeasureTheory Complex UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups Classical BigOperators
open ActualMarkedHorocycleSupport20261112 ActualRegularEisensteinQuotient20261110
open ActualCharacterCriticalFamily20261110 ActualCharacterCuspExpansion20261110
open ActualYoungCriticalCusps20261110 ActualYoungCriticalD20261110 ActualYoungDilationInverse20261110
open ActualYoungCuspCoefficients20261110 ActualYoungFormalClass20261110 ActualYoungCriticalProjection20261110
open ActualCuspDenominatorClasses20261110 ActualContinuousClassFourier20261110
open ActualOrdinaryContinuousModes20261110 ActualCompletedCurveMeans20261110
open FiniteMeasureCauchyParameterIntegral20261026b CompletedParameterDiskHeightValues20261026b
open CompletedAllLevelCompactParameterValues20261026b FiniteLevelEisensteinOldforms20261025a
open AllLevelContinuedMaass20261026a CompletedActualEisensteinIdentity20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0DegeneracyMapSourceOnly
open private Regular Regular.deriv coefficient_reg factor_principal factor_character dilate_cont
  from ImbalancedChen.Part3ActualNativeHorocycleParameter
open private envelope envelope_summable term_bound from ImbalancedChen.Part3ActualCompletedCurveMeans

private def LocalBound (F : ℂ → ℍ → ℂ) (s : ℂ) (K : Set ℍ) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in 𝓝 s, ∀ z ∈ K, ‖F w z‖ ≤ B

private theorem scale {s : ℂ} {K : Set ℍ} {c : ℂ → ℂ} {F : ℂ → ℍ → ℂ}
    (hc : ContinuousAt c s) (hF : LocalBound F s K) : LocalBound (fun w z => c w*F w z) s K := by
  obtain ⟨B,hB,HB⟩ := hF
  have J := hc.norm.tendsto.eventually_lt_const (lt_add_one ‖c s‖)
  refine ⟨(‖c s‖+1)*B,by positivity,?_⟩
  filter_upwards [J,HB] with w hw hv z hz
  rw [norm_mul]
  exact mul_le_mul hw.le (hv z hz) (norm_nonneg _) (by positivity)

private theorem sum_bound {ι : Type*} [Fintype ι] {s : ℂ} {K : Set ℍ} {F : ι → ℂ → ℍ → ℂ}
    (H : ∀ i, LocalBound (F i) s K) : LocalBound (fun w z => ∑ i,F i w z) s K := by
  choose B hB U using H
  refine ⟨∑ i,B i,Finset.sum_nonneg (fun i _ => hB i),?_⟩
  filter_upwards [Filter.eventually_all.mpr U] with w hw z hz
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hw i z hz))

private theorem ordinary_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) {K : Set ℍ} (hK : IsCompact K) : LocalBound (ordinary χ) s K := by
  rcases K.eq_empty_or_nonempty with e|ne
  · exact ⟨0,le_rfl,by simp [e]⟩
  obtain ⟨z₀,h₀,lo⟩ := hK.exists_isMinOn ne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨z₁,h₁,hi⟩ := hK.exists_isMaxOn ne UpperHalfPlane.continuous_im.continuousOn
  have band (z : ℍ) (hz : z ∈ K) : z.im ∈ Icc z₀.im z₁.im :=
    ⟨isMinOn_iff.mp lo z hz,isMaxOn_iff.mp hi z hz⟩
  by_cases e : q=1
  · simp only [ordinary,if_pos e,principalOrdinary]
    apply scale ((factor_principal.deriv s hs h1).continuousAt)
    have h0 : s ≠ 0 := by intro eq; simp [eq] at hs
    have hr : s ∈ completedRegularDomain 1 := by
      simp [completedRegularDomain,canonicalPrimeList,oldformNormalization,h0,h1]
    obtain ⟨R,hR,sub,circ⟩ := exists_regular_parameter_disk 1 s hr
    obtain ⟨B,hB,HB⟩ := exists_completedFourier_disk_height_bound s hR z₀.im_pos (isMinOn_iff.mp lo z₁ h₁)
      (fun w hw => ⟨(sub hw).1,(sub hw).2.1⟩) circ
    refine ⟨B,hB.le,?_⟩
    filter_upwards [Metric.closedBall_mem_nhds s hR] with w hw z hz
    exact HB w hw z.im (band z hz) z.re
  · simp only [ordinary,if_neg e,primitiveFamily]
    apply scale (((factor_character χ).deriv s hs h1).continuousAt)
    let M := Nat.ceil (‖s‖+1)
    let B := ∑' n : ℤ,envelope M z₀.im z₁.im n
    refine ⟨max B 0,le_max_right _ _,?_⟩
    filter_upwards [Metric.ball_mem_nhds s zero_lt_one] with w hw z hz
    have hW : |w.re| ≤ (M : ℝ) := (Complex.abs_re_le_norm w).trans ((by
      have ht := norm_add_le (w-s) s
      rw [sub_add_cancel] at ht
      have hd : ‖w-s‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hw
      linarith : ‖w‖ ≤ ‖s‖+1).trans (Nat.le_ceil _))
    exact (tsum_of_norm_bounded (envelope_summable M z₀.im_pos z₁.im).hasSum
      (fun n => term_bound χ n hW z₀.im_pos z (band z hz))).trans (le_max_left B 0)

theorem cusp_compact_bound (N : ℕ) [NeZero N] (a : NativeCusps N) {s : ℂ}
    (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) {K : Set ℍ} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in 𝓝 s, ∀ z ∈ K, ‖cuspFamily N a w z‖ ≤ B := by
  change LocalBound (parameterFamily ((youngCuspEquiv N).symm a)) s K
  generalize (youngCuspEquiv N).symm a = p
  rcases p with ⟨f,u⟩
  letI : NeZero (band N f.1) := ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩
  rw [show parameterFamily (N := N) ⟨f,u⟩ = _ from funext (fun w => funext (inverse_cusp f u w))]
  apply scale continuousAt_const
  apply sum_bound
  intro ξ
  apply scale continuousAt_const
  let i : CharacterSlots N := ⟨f,ξ⟩
  let S := originalSlot i
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  change LocalBound (fun w z => channelFunction i.1 i.2 w z) s K
  simp only [S.realized,D_as_dilations]
  apply sum_bound
  intro b
  apply scale (((coefficient_reg _ S.pos S.j b).deriv s hs h1).continuousAt)
  let d := dilation S.pos b
  let Z := fun z : ℍ => degeneracyDiagonal d d.pos • z
  obtain ⟨B,hB,HB⟩ := ordinary_bound ξ.primitiveCharacter hs h1 (hK.image (dilate_cont d))
  refine ⟨B,hB,?_⟩
  filter_upwards [HB] with w hw z hz
  exact hw (Z z) ⟨z,hz,rfl⟩

def column {N : ℕ} [NeZero N] (a : NativeCusps N) (s : ℂ) : Gamma0OrbitSpace N → ℂ :=
  if h : s ≠ 0 ∧ s ≠ 1 then descended a s h.1 h.2 else 0

theorem column_measurable {N : ℕ} [NeZero N] (a : NativeCusps N) (s : ℂ) : Measurable (column a s) := by
  unfold column
  split <;> rename_i h
  · exact (descended_continuous_measurable _ _ _ _).2
  · exact measurable_const

theorem column_up {N : ℕ} [NeZero N] (a : NativeCusps N) {s : ℂ} (h : s ≠ 0 ∧ s ≠ 1) (z : ℍ) :
    column a s (orbitProjection N z)=cuspFamily N a s z := by simp [column,h]

private theorem reg_event {s : ℂ} (h : s ≠ 0 ∧ s ≠ 1) : ∀ᶠ w in 𝓝 s, w ≠ 0 ∧ w ≠ 1 :=
  (eventually_ne_nhds h.1).and (eventually_ne_nhds h.2)

theorem column_deriv {N : ℕ} [NeZero N] (a : NativeCusps N) {s : ℂ} (hs : 1/2 ≤ s.re)
    (h1 : s ≠ 1) (q : Gamma0OrbitSpace N) : DifferentiableAt ℂ (fun w => column a w q) s := by
  induction q using Quotient.inductionOn with
  | _ z =>
    have h0 : s ≠ 0 := by intro eq; simp [eq] at hs
    apply (parameterFamily_differentiable _ z s hs h1).congr_of_eventuallyEq
    filter_upwards [reg_event ⟨h0,h1⟩] with w hw
    exact column_up a hw z

def spatial {N : ℕ} [NeZero N] (a : NativeCusps N) (V : Gamma0OrbitSpace N → ℂ) (s : ℂ) :=
  ∫ q,star (V q)*column a s q ∂carrierPushforward N

private theorem local_domination {N : ℕ} [NeZero N] (a : NativeCusps N) {V : Gamma0OrbitSpace N → ℂ}
    (hV : supportedInQuotientCompact N V) {s : ℂ} (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in 𝓝 s, ∀ q, ‖star (V q)*column a w q‖ ≤ B*‖V q‖ := by
  have h0 : s ≠ 0 := by intro e; simp [e] at hs
  obtain ⟨K,hK,S⟩ := hV
  obtain ⟨B,hB,H⟩ := cusp_compact_bound N a hs h1 hK
  refine ⟨B,hB,?_⟩
  filter_upwards [H,reg_event ⟨h0,h1⟩] with w hw hr q
  by_cases e : V q=0
  · simp [e]
  · obtain ⟨z,hz,rfl⟩ := S e
    rw [norm_mul,norm_star,column_up a hr,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hw z hz) (norm_nonneg _)

theorem spatial_continuousAt {N : ℕ} [NeZero N] (a : NativeCusps N) {V : Gamma0OrbitSpace N → ℂ}
    (hV : supportedInQuotientCompact N V) (hI : Integrable V (carrierPushforward N))
    {s : ℂ} (hs : 1/2 ≤ s.re) (h1 : s ≠ 1) : ContinuousAt (spatial a V) s := by
  obtain ⟨B,_,HB⟩ := local_domination a hV hs h1
  exact tendsto_integral_filter_of_dominated_convergence (fun q => B*‖V q‖)
    (Eventually.of_forall (fun w => hI.1.star.mul (column_measurable a w).aestronglyMeasurable))
    (HB.mono (fun w hw => ae_of_all _ hw)) (hI.norm.const_mul B)
    (ae_of_all _ (fun q => ((column_deriv a hs h1 q).continuousAt.tendsto.const_mul _)))

theorem spatial_differentiable {N : ℕ} [NeZero N] (a : NativeCusps N) {V : Gamma0OrbitSpace N → ℂ}
    (hV : supportedInQuotientCompact N V) (hI : Integrable V (carrierPushforward N))
    {s : ℂ} (hs : 1/2 < s.re) (h1 : s ≠ 1) : DifferentiableAt ℂ (spatial a V) s := by
  letI : IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩
  let F := fun w q => star (V q)*column a w q
  obtain ⟨B,hB,HB⟩ := local_domination a hV hs.le h1
  have H := (HB.and ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)).and (eventually_ne_nhds h1)
  obtain ⟨R,hR,HR⟩ := Metric.mem_nhds_iff.mp H
  have fm (w : ℂ) : AEStronglyMeasurable (F w) (carrierPushforward N) :=
    hI.1.star.mul (column_measurable a w).aestronglyMeasurable
  have fd (w : ℂ) (hw : w ∈ ball s R) (q : Gamma0OrbitSpace N) : DifferentiableAt ℂ (fun v => F v q) w :=
    (column_deriv a (HR hw).1.2.le (HR hw).2 q).const_mul _
  have hmem : s ∈ ball s R := mem_ball_self hR
  let D := fun w q => deriv (fun v => F v q) w
  have Bd : Integrable (fun q => (4/R)*(B*‖V q‖+1)) (carrierPushforward N) :=
    ((hI.norm.const_mul B).add (integrable_const _)).const_mul _
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    (ball_mem_nhds s (half_pos hR)) (Eventually.of_forall fm)
    ((hI.norm.const_mul B).mono' (fm s) (ae_of_all _ (HR hmem).1.1))
    (actual_parameter_derivative_aestronglyMeasurable F s fm (ae_of_all _ (fd s hmem)))
    _ Bd _).2.differentiableAt
  · exact ae_of_all _ (fun q w hw => by
      have J := disk_derivative_bound (fun v => F v q) hR (C := B*‖V q‖+1) (by positivity)
        (fun v hv => fd v hv q) (fun v hv => ((HR hv).1.1 q).trans (le_add_of_nonneg_right zero_le_one)) hw
      convert J using 1 <;> ring)
  · exact ae_of_all _ (fun q w hw => (fd w (Metric.ball_subset_ball (half_le_self hR.le) hw) q).hasDerivAt)

end
end ImbalancedChen.Part3.ActualCompactPacketParameter20261112
