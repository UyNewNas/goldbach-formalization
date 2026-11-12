import ImbalancedChen.Part3ActualPrescribedOppositeKL
import ImbalancedChen.Part3RealOrderKPositiveLaplace
import Batteries.Tactic.OpenPrivate

/-! Weights of the actual period-64 test on the two native spectral
branches. No bound uniform in the Fourier marking or scale is asserted. -/
namespace ImbalancedChen.Part3.ActualPrescribedTraceWeights20261112

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ContDiff
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)
open OriginalFullModulusTestJets20261102 ActualOppositeBesselTransform20261112
open ActualGreenResolventJumpSourceOnly ComplexOrderKBridgeSourceOnly RealOrderKPositiveLaplace
open RealOrderKExceptionalSourceOnly ActualOppositeBruhatCoordinates20261112
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLInversionBounds20261025a
open private logTest log_transform from ImbalancedChen.Part3ActualPrescribedOppositeKL

private theorem cosh_le_exp_pos {x : ℝ} (hx : 0≤x) : Real.cosh x≤Real.exp x := by
  rw [Real.cosh_eq]
  linarith only [Real.exp_le_exp.mpr (show -x≤x by linarith)]

private theorem weight_even (Φ : ℝ → ℂ) (s : ℝ) : oppositeWeight Φ (-s)=oppositeWeight Φ s := by
  simp only [oppositeWeight,mul_neg,Real.cosh_neg,kTransform,Complex.ofReal_neg,neg_mul,mul_neg,
    complexOrderK_neg_order]

theorem regular_measurable (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    StronglyMeasurable (oppositeWeight (spectralTest ell Y)) := by
  let P := logTest ell hY
  have E : oppositeWeight (spectralTest ell Y)=fun t : ℝ =>
      8*(Real.cosh (Real.pi*t):ℂ)*actualKtransform P.function (2*t) := by
    funext t
    rw [log_transform]
    rfl
  rw [E]
  exact (by fun_prop : Continuous (fun t : ℝ => 8*(Real.cosh (Real.pi*t):ℂ))).stronglyMeasurable.mul
    ((actualKtransform_stronglyMeasurable P).comp_measurable (by fun_prop))

/-- The third transfer of the actual log test gives five powers on
both tails, with a finite constant for the original scale and mark. -/
theorem regular_fifth_decay (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ D : ℝ,0≤D ∧ ∀ t : ℝ,‖oppositeWeight (spectralTest ell Y) t‖*(1+|t|)^5≤D := by
  let P := logTest ell hY
  obtain ⟨a,ha,S⟩ := exists_positive_physical_lower P
  let L := contourBudget P a
  let U := contourBudget (hamiltonianIterate 2 (hamiltonianTest P)) a
  have hL : 0≤L := contourBudget_nonneg _ _
  have hU : 0≤U := contourBudget_nonneg _ _
  let D := max (8*Real.cosh Real.pi*L*2^5) (8*U*(3/2)^5)
  refine ⟨D,(by positivity : 0≤8*Real.cosh Real.pi*L*2^5).trans (le_max_left _ _),?_⟩
  intro t
  let s := |t|
  have hs : 0≤s := abs_nonneg _
  have even : oppositeWeight (spectralTest ell Y) t=oppositeWeight (spectralTest ell Y) s := by
    by_cases h : t<0
    · simpa only [s,abs_of_neg h] using (weight_even (spectralTest ell Y) t).symm
    · rw [show s=t from abs_of_nonneg (le_of_not_gt h)]
  rw [even]
  change ‖oppositeWeight _ s‖*(1+s)^5≤D
  rw [oppositeWeight,← log_transform ell hY,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Real.cosh_pos _).le]
  norm_num only [Complex.norm_ofNat]
  by_cases small : 2*s≤1
  · have K : ‖actualKtransform P.function (2*s)‖≤L := actualKtransform_low_bound P ha S (by linarith) small
    have C : Real.cosh (Real.pi*s)≤Real.cosh Real.pi := Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hs),abs_of_pos Real.pi_pos]
      exact (mul_le_mul_of_nonneg_left (show s≤1 by linarith) Real.pi_pos.le).trans_eq (mul_one _))
    apply le_trans _ (le_max_left _ _)
    gcongr <;> first | exact K | exact C | linarith
  · have hτ : 1≤2*s := le_of_not_ge small
    have hp : 0<2*s := zero_lt_one.trans_le hτ
    have K := actualKtransform_third_transfer_bound P ha S hτ
    have xs : -Real.pi*(2*s)/2= -(Real.pi*s) := by ring
    rw [xs] at K
    have scaled := (le_div_iff₀ (pow_pos hp 5)).mp K
    have C := cosh_le_exp_pos (mul_nonneg Real.pi_pos.le hs)
    have X : Real.cosh (Real.pi*s)*Real.exp (-(Real.pi*s))≤1 := by
      simpa only [← Real.exp_add,add_neg_cancel,Real.exp_zero] using
        mul_le_mul_of_nonneg_right C (Real.exp_pos _).le
    have B : ‖actualKtransform P.function (2*s)‖*(2*s)^5*Real.cosh (Real.pi*s)≤U := by
      calc
        _ ≤ U*(Real.exp (-(Real.pi*s))*Real.cosh (Real.pi*s)) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right scaled (Real.cosh_pos _).le
        _ ≤ U*1 := mul_le_mul_of_nonneg_left (by rwa [mul_comm]) hU
        _ = U := mul_one _
    have five : (1+s)^5≤(3/2:ℝ)^5*(2*s)^5 := by
      rw [← mul_pow]
      gcongr <;> linarith
    apply le_trans _ (le_max_right _ _)
    nlinarith only [mul_le_mul_of_nonneg_right five
      (mul_nonneg (by positivity : (0:ℝ)≤8*Real.cosh (Real.pi*s)) (norm_nonneg (actualKtransform P.function (2*s)))),
      mul_le_mul_of_nonneg_left B (by norm_num : (0:ℝ)≤8*(3/2)^5)]

private theorem halfline_majorant {a q α : ℝ} (ha : 0<a) (hq : a≤q) (hα : α∈Icc (0:ℝ) (1/2)) :
    ‖complexOrderK (2*(α:ℂ)) q‖ ≤ ∫ u in Ioi (0:ℝ),tiltedCoshDensity 1 a u := by
  apply norm_integral_le_of_norm_le (tiltedCoshDensity_integrable 1 ha).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  apply (complexOrderIntegrand_norm_le_real (2*(α:ℂ)) q u).trans
  have κ : (2*(α:ℂ)).re=2*α := by simp only [Complex.mul_re,Complex.ofNat_re,Complex.ofReal_re,
    Complex.ofNat_im,Complex.ofReal_im,zero_mul,sub_zero]
  rw [realOrderIntegrand,κ,tiltedCoshDensity,one_mul,Real.exp_add]
  have hku : 0≤(2*α)*u := mul_nonneg (by linarith [hα.1]) hu.le
  have hu' : (2*α)*u≤u := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 2*α≤1 by linarith [hα.2]) hu.le
  exact mul_le_mul (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le]))
    ((cosh_le_exp_pos hku).trans (Real.exp_le_exp.mpr hu')) (Real.cosh_pos _).le (Real.exp_pos _).le

/-- The raw eight times the K transform is uniformly bounded on all
physically possible real orders, including both endpoints. -/
theorem exceptional_bound (ell : D4 → ℤ) {Y : ℝ} (hY : 0<Y) :
    ∃ D : ℝ,0≤D ∧ ∀ α∈Icc (0:ℝ) (1/2),
      Integrable (fun q => complexOrderK (2*(α:ℂ)) q*spectralTest ell Y q/(q:ℂ)) posMeasure ∧
      ‖8*kTransform (α:ℂ) (spectralTest ell Y)‖≤D := by
  let Φ := spectralTest ell Y
  let a := Y/16
  have ha : 0<a := div_pos hY (by norm_num)
  let B := ∫ u in Ioi (0:ℝ),tiltedCoshDensity 1 a u
  have b : 0≤B := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have S := spectralTest_tsupport_strict ell hY
  have cΦ := (spectralTest_contDiff ell Y).continuous
  have hc : HasCompactSupport Φ := HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc a (16*Y))) (fun q h => ⟨(S (subset_tsupport _ h)).1.le,(S (subset_tsupport _ h)).2.le⟩)
  have hΦ : Integrable (fun q => ‖Φ q‖) posMeasure := (cΦ.integrable_of_hasCompactSupport hc).norm.integrableOn
  let G := fun q : ℝ => (B/a)*‖Φ q‖
  have hG : Integrable G posMeasure := hΦ.const_mul _
  refine ⟨8*∫ q,G q ∂posMeasure,mul_nonneg (by norm_num) (integral_nonneg (fun q => mul_nonneg (div_nonneg b ha.le) (norm_nonneg _))),?_⟩
  intro α hα
  have mk : StronglyMeasurable (complexOrderK (2*(α:ℂ))) :=
    (by unfold complexOrderIntegrand; fun_prop : Continuous (fun p : ℝ×ℝ => complexOrderIntegrand (2*(α:ℂ)) p.1 p.2)).stronglyMeasurable.integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Ioi 0))
  have M : ∀ᵐ q ∂posMeasure,‖complexOrderK (2*(α:ℂ)) q*Φ q/(q:ℂ)‖≤G q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
    by_cases hz : Φ q=0
    · simp [hz,G]
    · have aq := (S (subset_tsupport _ hz)).1.le
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg hq.le]
      dsimp only [G]
      calc
        _ = (‖complexOrderK (2*(α:ℂ)) q‖/q)*‖Φ q‖ := by ring
        _ ≤ (B/a)*‖Φ q‖ := mul_le_mul_of_nonneg_right
          (div_le_div₀ b (halfline_majorant ha aq hα) ha aq) (norm_nonneg _)
  refine ⟨hG.mono' ((mk.mul cΦ.stronglyMeasurable).div Complex.continuous_ofReal.stronglyMeasurable).aestronglyMeasurable M,?_⟩
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hG M) (by norm_num)

end
end ImbalancedChen.Part3.ActualPrescribedTraceWeights20261112
