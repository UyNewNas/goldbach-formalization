import ImbalancedChen.Part3RoughSlotMellinSeries
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLTwistedSmoothedPerron

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual rough one/Mobius smoothed Perron inversion in Re(s)>1, including
literal exp(i*t*log(n/U)). The infinite interchange is proved with the
actual bounded coefficient and the primary Smooth1 Mellin decay; no
weighted SW or generic Perron premise is assumed. The cutoff nu is a
fixed positive normalized C1 bump supported in [1/2,2]. This source does
not identify it with a previously unconstructed original HB atom chart.
-/

namespace ImbalancedChen.Part3.RoughSlotSmoothedPerron20261026b
noncomputable section
open Set Function Filter Complex Real MeasureTheory
open scoped LSeries.notation
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughSlotMellinSeries20261026b PrimeMellinProfileVariation20261026b

variable {q : ℕ} [NeZero q]
local notation "𝓜" => mellin

def coefficient (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (n : ℕ) : ℂ :=
  if n=0 then 0 else
    if useMu then roughMoebiusMellin χ z τ U n else roughOneMellin χ z τ U n

@[simp] theorem coefficient_zero (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) : coefficient useMu χ z τ U 0 = 0 := by simp [coefficient]

theorem coefficient_norm_le_one (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (n : ℕ) : ‖coefficient useMu χ z τ U n‖ ≤ 1 := by
  by_cases hn : n=0
  · simp [hn]
  · cases useMu
    · simp only [coefficient,hn,if_false,Bool.false_eq_true,roughOneMellin,norm_mul,
        phase_norm,one_mul]
      exact (mul_le_mul (χ.norm_le_one n) (roughOneSlot_norm_le z n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    · simp only [coefficient,hn,if_false,if_true,roughMoebiusMellin,norm_mul,
        phase_norm,one_mul]
      exact (mul_le_mul (χ.norm_le_one n) (roughMoebiusSlot_norm_le z n)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem coefficient_summable (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (coefficient useMu χ z τ U) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m:=1) _ hs
  intro n _
  exact coefficient_norm_le_one useMu χ z τ U n

def roughSmoothedSum (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X : ℝ) : ℂ :=
  ∑' n : ℕ, coefficient useMu χ z τ U n * Smooth1 ν ε (n/X)

def roughPerronSeriesIntegrand (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  LSeries (coefficient useMu χ z τ U) s *
    𝓜 (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ)^s
set_option backward.isDefEq.respectTransparency false in

lemma roughSmoothedPerron_aux_tsum_integral
    (useMu : Bool) (χ : DirichletCharacter ℂ q) (z τ U : ℝ) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ t : ℝ, ∑' n : ℕ,
      coefficient useMu χ z τ U n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) =
    ∑' n : ℕ, ∫ t : ℝ,
      coefficient useMu χ z τ U n / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun a : ℝ ↦
      𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re})
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffν suppν ⟨εpos, ε_lt_one⟩
        νpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re,
        mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]
      linarith
  have norm_nat_cpow_vertical : ∀ a : ℝ, ∀ n : ℕ,
      ‖(n : ℂ) ^ ((σ : ℂ) + a * I)‖₊ = n ^ σ := by
    intro a n
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero, ne_eq]
      linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero,
      Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := n) (by linarith)]
    norm_cast
  -- Absolute integrability separates into the coefficient series and Mellin decay.
  rw [MeasureTheory.integral_tsum]
  · have X_ne : X ≠ 0 := ne_of_gt X_pos
    intro n
    by_cases hn : n = 0
    · simpa [hn, coefficient] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [hn, X_ne])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, norm_nat_cpow_vertical]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
      I_im, mul_one, sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top
    conv =>
      arg 1
      arg 1
      intro n
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]
    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      have hsigma : 1 < (σ : ℂ).re := by simpa using σ_gt
      convert (coefficient_summable useMu χ z τ U hsigma).norm using 1
      funext n
      rw [LSeries.term_of_ne_zero' (Complex.ne_zero_of_one_lt_re hsigma),norm_div,
        Complex.norm_natCast_cpow_of_re_ne_zero n (by simp only [ofReal_re]; linarith)]
      simp only [ofReal_re]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
        εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

set_option backward.isDefEq.respectTransparency false in
/-- Smoothed Perron inversion for the actual bounded rough one/Mobius coefficients twisted by an
arbitrary Dirichlet character.  No nonprincipality assumption and no contour
shift are used. -/
theorem roughSmoothedPerron_series
    (useMu : Bool) (χ : DirichletCharacter ℂ q) (z τ U : ℝ) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X : ℝ} (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1)
    {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    roughSmoothedSum useMu χ z τ U ν ε X =
      VerticalIntegral' (roughPerronSeriesIntegrand useMu χ z τ U ν ε X) σ := by
  symm
  dsimp [roughSmoothedSum, roughPerronSeriesIntegrand,
    VerticalIntegral', VerticalIntegral]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ t : ℝ, ∑' n : ℕ,
        coefficient useMu χ z τ U n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr
      ext t
      rw [LSeries_def₀ (coefficient_zero useMu χ z τ U)]
      rw [← tsum_mul_right, ← tsum_mul_right]
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, ∫ t : ℝ,
        coefficient useMu χ z τ U n / (n : ℂ) ^ (σ + t * I) *
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X : ℂ) ^ (σ + t * I)) := by
      congr 2
      exact roughSmoothedPerron_aux_tsum_integral useMu χ z τ U diffν νpos suppν mass_one
        X_pos εpos ε_lt_one σ_gt σ_le
    _ = 1 / (2 * π * I) * (I * ∑' n : ℕ, coefficient useMu χ z τ U n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      field_simp
      congr 1
      ext n
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext t
      by_cases hn : n = 0
      · simp [hn, coefficient]
      rw [mul_div_assoc, mul_assoc]
      congr 1
      rw [(div_eq_iff (by simp [hn])).mpr]
      · have hmul := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ))
          (r := σ + I * t) (div_nonneg X_pos.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        push_cast at hmul ⊢
        rw [← hmul, div_mul_cancel₀]
        simp [hn]
    _ = 1 / (2 * π) * (∑' n : ℕ, coefficient useMu χ z τ U n *
        ∫ t : ℝ, 𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
          (X / (n : ℂ)) ^ (σ + t * I)) := by
      rw [← mul_assoc]
      congr 1
      field_simp
    _ = ∑' n : ℕ, coefficient useMu χ z τ U n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            (X / (n : ℂ)) ^ (σ + t * I)) := by
      simp_rw [← tsum_mul_left, ← mul_assoc, mul_comm]
    _ = ∑' n : ℕ, coefficient useMu χ z τ U n *
        (1 / (2 * π) * ∫ t : ℝ,
          𝓜 (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I) *
            ((n : ℂ) / X) ^ (-(σ + t * I))) := by
      have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
      have hninv (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
      have him (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
        simp [Complex.log_im, arg_eq_zero_iff,
          div_nonneg (Nat.cast_nonneg _) X_pos.le]
      have hpow (n : ℕ) (t : ℝ) :
          ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
            (((n : ℂ) / X) ^ (-1 : ℂ)) ^ (σ + t * I) := by
        rw [cpow_mul] <;> rw [him n] <;> simp [Real.pi_pos, Real.pi_nonneg]
      simp_rw [ht, hpow, hninv]
    _ = _ := by
      congr 1
      ext n
      by_cases hn : n = 0
      · simp [hn, coefficient]
      have n_pos : 0 < n := Nat.pos_of_ne_zero hn
      congr 1
      have h := mellinInv_mellin_eq σ
        (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X) ?_ ?_ ?_ ?_
      · beta_reduce at h
        dsimp [mellinInv, VerticalIntegral] at h
        convert! h using 4
        · norm_cast
        · rw [mul_comm]
          norm_cast
      · exact div_pos (by exact_mod_cast n_pos) X_pos
      · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νpos mass_one
        simp only [ofReal_re]
        linarith
      · dsimp [VerticalIntegrable]
        exact SmoothedChebyshevDirichlet_aux_integrable diffν νpos suppν mass_one
          εpos ε_lt_one σ_gt σ_le
      · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
        exact Smooth1ContinuousAt diffν νpos suppν εpos (by positivity)

/-- The genuine original-level L-function, including finite p<=z
corrections and the exact complex Mellin shift. -/
def roughTransform (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (s : ℂ) : ℂ :=
  phase (-τ) U *
    (if useMu then (χ.LFunction (shiftedExponent s τ))⁻¹ *
      (∏ p ∈ smallPrimes z, (1-χ p*(p : ℂ)^(-shiftedExponent s τ))⁻¹)
    else χ.LFunction (shiftedExponent s τ)*finiteCorrection χ z (shiftedExponent s τ))

theorem coefficient_LSeries_eq_transform (useMu : Bool) (χ : DirichletCharacter ℂ q)
    {z U : ℝ} (hz : 0 ≤ z) (hU : 0 < U) (τ : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (coefficient useMu χ z τ U) s = roughTransform useMu χ z τ U s := by
  have hshift : 1 < (shiftedExponent s τ).re := by simpa [shiftedExponent_re] using hs
  cases useMu
  · rw [show LSeries (coefficient false χ z τ U) s =
        LSeries (roughOneMellin χ z τ U) s from
      LSeries_congr (fun {n} hn => by simp [coefficient,hn]) s]
    change LSeries (fun n => phase τ ((n : ℝ)/U)*(χ n*roughOneSlot z n)) s = _
    rw [mellin_LSeries_shift _ hU s τ,roughOne_LSeries χ hz hshift]
    rfl
  · rw [show LSeries (coefficient true χ z τ U) s =
        LSeries (roughMoebiusMellin χ z τ U) s from
      LSeries_congr (fun {n} hn => by simp [coefficient,hn]) s]
    change LSeries (fun n => phase τ ((n : ℝ)/U)*(χ n*roughMoebiusSlot z n)) s = _
    rw [mellin_LSeries_shift _ hU s τ,roughMoebius_LSeries χ hz hshift]
    rfl

def roughPerronIntegrand (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  roughTransform useMu χ z τ U s *
    𝓜 (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ)^s

/-- Actual rough-slot inversion, with no weighted-SW/Perron premise.
Principal characters are allowed because this identity stays right of1.
The zero extension merely spells the positive-integer sum, including q=1. -/
theorem actual_rough_smoothed_Perron
    (useMu : Bool) (χ : DirichletCharacter ℂ q)
    {z U : ℝ} (hz : 0 ≤ z) (hU : 0 < U) (τ : ℝ) {ν : ℝ → ℝ}
    (diffν : ContDiff ℝ 1 ν) (νpos : ∀ x>0,0≤ν x)
    (suppν : support ν ⊆ Icc (1/2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x/x=1)
    {X : ℝ} (hX : 0<X) {ε : ℝ} (hε : 0<ε) (hε1 : ε<1)
    {σ : ℝ} (hσ : 1<σ) (hσ2 : σ≤2) :
    roughSmoothedSum useMu χ z τ U ν ε X =
      VerticalIntegral' (roughPerronIntegrand useMu χ z τ U ν ε X) σ := by
  rw [roughSmoothedPerron_series useMu χ z τ U diffν νpos suppν mass_one hX hε hε1 hσ hσ2]
  dsimp [VerticalIntegral',VerticalIntegral]
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  dsimp only [roughPerronSeriesIntegrand,roughPerronIntegrand]
  rw [coefficient_LSeries_eq_transform useMu χ hz hU τ (by simpa using hσ)]

end
end ImbalancedChen.Part3.RoughSlotSmoothedPerron20261026b

