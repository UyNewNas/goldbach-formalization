import ImbalancedChen.Part3RoughSlotSmoothedPerron
import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLRightHalfPlaneBounds
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite-carrier and finite-height inversion for the literal rough slots.
The right-line tails use absolute convergence, uniformly in the rough
cutoff, character, Mellin frequency and normalization U. The remainder is
retained explicitly and is at most C_nu X^sigma(1+1/(sigma-1))/(pi*epsilon*T).
This is a right-line truncation result, not a shifted-contour cancellation.
-/

namespace ImbalancedChen.Part3.RoughSlotPerronTruncation20261026b
noncomputable section
open Classical Set Function Filter Complex Real MeasureTheory
open RoughSlotSmoothedPerron20261026b
open AnalyticNumberTheory.LargeSieve

variable {q : ℕ} [NeZero q]

def smoothCarrier (ν : ℝ → ℝ) (ε X : ℝ) : Finset ℕ :=
  Finset.range (⌈(1+2*Real.log 2*ε)*X⌉₊+1)

theorem roughSmoothedSum_eq_finite (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) {ν : ℝ → ℝ} (hsupp : support ν ⊆ Icc (1/2) 2)
    {ε X : ℝ} (hε : 0<ε) (hε1 : ε<1) (hX : 0<X) :
    roughSmoothedSum useMu χ z τ U ν ε X =
      ∑ n ∈ smoothCarrier ν ε X, coefficient useMu χ z τ U n*Smooth1 ν ε (n/X) := by
  unfold roughSmoothedSum
  apply tsum_eq_sum
  intro n hn
  have hn' : ⌈(1+2*Real.log 2*ε)*X⌉₊+1 ≤ n := by
    simpa only [smoothCarrier,Finset.mem_range,not_lt] using hn
  have hy : (1+2*Real.log 2*ε)*X ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_of_succ_le hn'))
  obtain ⟨c,_hc,hc,hzero⟩ := Smooth1Properties_above hsupp
  have hcut : Smooth1 ν ε ((n : ℝ)/X)=0 := by
    apply hzero ε _ ⟨hε,hε1⟩
    rw [hc]
    exact (le_div_iff₀ hX).2 hy
  simp only [hcut,ofReal_zero,mul_zero]

theorem coefficient_LSeries_norm_le (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) {σ : ℝ} (hσ : 1<σ) (t : ℝ) :
    ‖LSeries (coefficient useMu χ z τ U) ((σ : ℂ)+t*I)‖ ≤ 1+1/(σ-1) := by
  have hs : 1 < ((σ : ℂ)+t*I).re := by simpa using hσ
  have hsum := coefficient_summable useMu χ z τ U hs
  have hterm (n : ℕ) :
      ‖LSeries.term (coefficient useMu χ z τ U) ((σ : ℂ)+t*I) n‖ ≤ (n : ℝ)^(-σ) := by
    by_cases hn : n=0
    · simp [LSeries.term,hn,Real.zero_rpow (by linarith : -σ≠0)]
    · rw [LSeries.term_of_ne_zero hn,norm_div,
        Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using ne_of_gt (zero_lt_one.trans hσ))]
      simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,add_zero]
      rw [Real.rpow_neg (Nat.cast_nonneg n)]
      simpa only [one_div] using div_le_div_of_nonneg_right
        (coefficient_norm_le_one useMu χ z τ U n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  exact (norm_tsum_le_tsum_norm hsum.norm).trans
    ((hsum.norm.tsum_le_tsum hterm
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))).trans
      (tsum_nat_rpow_neg_le σ hσ))

def rightFunction (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X σ : ℝ) (t : ℝ) : ℂ :=
  roughPerronSeriesIntegrand useMu χ z τ U ν ε X ((σ : ℂ)+t*I)

def rightSegment (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X σ T : ℝ) : ℂ :=
  ((1/(2*Real.pi) : ℝ) : ℂ) *
    ∫ t in Icc (-T) T, rightFunction useMu χ z τ U ν ε X σ t

def rightTail (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) (ν : ℝ → ℝ) (ε X σ T : ℝ) : ℂ :=
  ((1/(2*Real.pi) : ℝ) : ℂ) *
    ∫ t in (Icc (-T) T)ᶜ, rightFunction useMu χ z τ U ν ε X σ t

/-- The finite segment is literally the original-level L/Euler integrand
of the preceding actual inversion theorem, rather than a finite polynomial. -/
theorem rightSegment_eq_actual_LFunction (useMu : Bool) (χ : DirichletCharacter ℂ q)
    {z U : ℝ} (hz : 0≤z) (hU : 0<U) (τ : ℝ) (ν : ℝ → ℝ)
    (ε X σ T : ℝ) (hσ : 1<σ) :
    rightSegment useMu χ z τ U ν ε X σ T =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t in Icc (-T) T,
        roughPerronIntegrand useMu χ z τ U ν ε X ((σ : ℂ)+t*I) := by
  unfold rightSegment
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only [rightFunction,roughPerronSeriesIntegrand,roughPerronIntegrand]
  rw [coefficient_LSeries_eq_transform useMu χ hz hU τ (by simpa using hσ)]

theorem rightTail_eq_actual_LFunction (useMu : Bool) (χ : DirichletCharacter ℂ q)
    {z U : ℝ} (hz : 0≤z) (hU : 0<U) (τ : ℝ) (ν : ℝ → ℝ)
    (ε X σ T : ℝ) (hσ : 1<σ) :
    rightTail useMu χ z τ U ν ε X σ T =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t in (Icc (-T) T)ᶜ,
        roughPerronIntegrand useMu χ z τ U ν ε X ((σ : ℂ)+t*I) := by
  unfold rightTail
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc.compl
  intro t _
  dsimp only [rightFunction,roughPerronSeriesIntegrand,roughPerronIntegrand]
  rw [coefficient_LSeries_eq_transform useMu χ hz hU τ (by simpa using hσ)]

/-- The actual bounded L-series is continuous on every right vertical line. -/
theorem continuous_rightFunction (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) {ν : ℝ → ℝ} (hν : ContDiff ℝ 1 ν)
    (hnonneg : ∀ x>0,0≤ν x) (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ),ν x/x=1)
    {ε X σ : ℝ} (hε : 0<ε) (hε1 : ε<1) (hX : 0<X) (hσ : 1<σ) :
    Continuous (rightFunction useMu χ z τ U ν ε X σ) := by
  have habsc : LSeries.abscissaOfAbsConv (coefficient useMu χ z τ U) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const
      ⟨1,fun n _ => coefficient_norm_le_one useMu χ z τ U n⟩
  have hL : Continuous (fun t : ℝ => LSeries (coefficient useMu χ z τ U) ((σ : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : LSeries.abscissaOfAbsConv (coefficient useMu χ z τ U) < ((σ : ℂ)+t*I).re :=
      habsc.trans_lt (by exact_mod_cast (show (1 : ℝ)<((σ : ℂ)+t*I).re by simpa using hσ))
    exact (LSeries_hasDerivAt hs).continuousAt.comp (by fun_prop)
  have hM : Continuous (fun t : ℝ => mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Smooth1MellinDifferentiable hν hsupp ⟨hε,hε1⟩ hnonneg hmass
      (by simp; linarith : 0<((σ : ℂ)+t*I).re)).continuousAt.comp (by fun_prop)
  exact (hL.mul hM).mul (by fun_prop (disch := exact hX.ne'))

/-- The smoothing constant precedes character/cutoff/frequency/scale and
all truncation choices. No norm of an unknown transform is an input. -/
theorem exists_right_majorant {ν : ℝ → ℝ} (hν : ContDiff ℝ 1 ν)
    (hsupp : support ν ⊆ Icc (1/2) 2) :
    ∃ C : ℝ, 0<C ∧ ∀ (useMu : Bool) (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (z τ U ε X σ : ℝ),
      0<ε → ε<1 → 0<X → 1<σ → σ≤2 → ∀ t : ℝ,
      ‖rightFunction useMu χ z τ U ν ε X σ t‖ ≤
        ((1+1/(σ-1))*X^σ*(C/ε))*(1+t^2)⁻¹ := by
  obtain ⟨C,hC,hbound⟩ := MellinOfSmooth1b hν hsupp
  refine ⟨C,hC,?_⟩
  intro useMu q _ χ z τ U ε X σ hε hε1 hX hσ hσ2 t
  have hM : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ)+t*I)‖ ≤
      C/ε*(1+t^2)⁻¹ := by
    calc
      _ ≤ C/ε*1/(σ^2+t^2) := by
        convert hbound (σ/2) (by linarith) ((σ : ℂ)+t*I)
          (by simp; linarith) (by simpa using hσ2) ε hε hε1 using 1
        simp only [mul_one,Complex.sq_norm,Complex.normSq_apply,add_re,ofReal_re,
          mul_re,I_re,mul_zero,ofReal_im,I_im,sub_self,add_zero,add_im,mul_im,
          zero_add,mul_inv_rev]
        ring_nf
      _ ≤ _ := by
        change C/ε/(σ^2+t^2) ≤ C/ε/(1+t^2)
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  dsimp only [rightFunction,roughPerronSeriesIntegrand]
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [add_re,ofReal_re,mul_re,I_re,mul_zero,ofReal_im,I_im,mul_one,sub_self,add_zero]
  calc
    _ ≤ (1+1/(σ-1))*(C/ε*(1+t^2)⁻¹)*X^σ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (coefficient_LSeries_norm_le useMu χ z τ U hσ t) hM
          (norm_nonneg _) (by positivity)) (Real.rpow_nonneg hX.le σ)
    _ = _ := by ring

private theorem tail_cauchyKernel_le {T : ℝ} (hT : 0<T) :
    (∫ t in (Icc (-T) T)ᶜ, (1+t^2)⁻¹) ≤ 2/T := by
  rw [MeasureTheory.setIntegral_compl measurableSet_Icc integrable_inv_one_add_sq,
    integral_univ_inv_one_add_sq,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T≤T),
    integral_inv_one_add_sq,Real.arctan_neg]
  have hsmall : Real.arctan T⁻¹ ≤ T⁻¹ := by
    have hx : 0≤T⁻¹ := inv_nonneg.mpr hT.le
    have hi := intervalIntegral.integral_mono_on hx
      (integrable_inv_one_add_sq.intervalIntegrable)
      (continuous_const.intervalIntegrable (0 : ℝ) T⁻¹)
      (fun t _ => show (1+t^2)⁻¹ ≤ (1 : ℝ) from by
        change 1/(1+t^2)≤1
        exact (div_le_one (by positivity)).2 (by nlinarith [sq_nonneg t]))
    simpa only [integral_inv_one_add_sq,Real.arctan_zero,sub_zero,
      intervalIntegral.integral_const,smul_eq_mul,mul_one] using hi
  rw [Real.arctan_inv_of_pos hT] at hsmall
  simpa only [div_eq_mul_inv] using (show Real.pi-(Real.arctan T- -Real.arctan T)≤2*T⁻¹ by linarith)

/-- Explicit right-line remainder for the actual finite rough sum. The
constant precedes every arithmetic and Mellin-frequency parameter. -/
theorem exists_finite_rough_Perron_truncation {ν : ℝ → ℝ}
    (hν : ContDiff ℝ 1 ν) (hnonneg : ∀ x>0,0≤ν x)
    (hsupp : support ν ⊆ Icc (1/2) 2) (hmass : ∫ x in Ioi (0 : ℝ),ν x/x=1) :
    ∃ C : ℝ, 0<C ∧ ∀ (useMu : Bool) (q : ℕ) [NeZero q]
      (χ : DirichletCharacter ℂ q) (z τ U ε X σ T : ℝ),
      0<ε → ε<1 → 0<X → 1<σ → σ≤2 → 0<T →
      (∑ n ∈ smoothCarrier ν ε X, coefficient useMu χ z τ U n*Smooth1 ν ε (n/X)) =
          rightSegment useMu χ z τ U ν ε X σ T + rightTail useMu χ z τ U ν ε X σ T ∧
      ‖rightTail useMu χ z τ U ν ε X σ T‖ ≤
        (1+1/(σ-1))*X^σ*(C/ε)/(Real.pi*T) := by
  obtain ⟨C,hC,hmajor⟩ := exists_right_majorant hν hsupp
  refine ⟨C,hC,?_⟩
  intro useMu q _ χ z τ U ε X σ T hε hε1 hX hσ hσ2 hT
  let K := (1+1/(σ-1))*X^σ*(C/ε)
  have hK : 0≤K := by dsimp [K]; positivity
  have hmaj := hmajor useMu q χ z τ U ε X σ hε hε1 hX hσ hσ2
  have hi : Integrable (rightFunction useMu χ z τ U ν ε X σ) :=
    (integrable_inv_one_add_sq.const_mul K).mono'
      (continuous_rightFunction useMu χ z τ U hν hnonneg hsupp hmass hε hε1 hX hσ).aestronglyMeasurable
      (Eventually.of_forall hmaj)
  constructor
  · rw [← roughSmoothedSum_eq_finite useMu χ z τ U hsupp hε hε1 hX,
      roughSmoothedPerron_series useMu χ z τ U hν hnonneg hsupp hmass hX hε hε1 hσ hσ2]
    have hsplit := MeasureTheory.integral_add_compl measurableSet_Icc hi
    dsimp [rightSegment,rightTail,rightFunction,VerticalIntegral',VerticalIntegral] at *
    rw [← hsplit]
    push_cast
    field_simp
    ring
  · have hnorm : (∫ t in (Icc (-T) T)ᶜ,
        ‖rightFunction useMu χ z τ U ν ε X σ t‖) ≤ K*(2/T) := by
      calc
        _ ≤ ∫ t in (Icc (-T) T)ᶜ, K*(1+t^2)⁻¹ :=
          MeasureTheory.integral_mono_ae hi.norm.integrableOn
            (integrable_inv_one_add_sq.const_mul K).integrableOn (Eventually.of_forall hmaj)
        _ = K*(∫ t in (Icc (-T) T)ᶜ,(1+t^2)⁻¹) := integral_const_mul _ _
        _ ≤ K*(2/T) := mul_le_mul_of_nonneg_left (tail_cauchyKernel_le hT) hK
    dsimp only [rightTail]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0<(1/(2*Real.pi) : ℝ))]
    calc
      _ ≤ (1/(2*Real.pi))*
          (∫ t in (Icc (-T) T)ᶜ,‖rightFunction useMu χ z τ U ν ε X σ t‖) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ ≤ (1/(2*Real.pi))*(K*(2/T)) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = _ := by dsimp only [K]; ring

end
end ImbalancedChen.Part3.RoughSlotPerronTruncation20261026b
