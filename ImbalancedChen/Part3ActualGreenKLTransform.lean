import ImbalancedChen.Part3ActualImaginaryKLeftJetBound
import ImbalancedChen.Part3ActualGreenForcingEnergy
import ImbalancedChen.Part3ActualKLCompactTestIntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The literal KL integral of actual positive-order Green compact forcing.
Every noncompact integral and both remote boundary terms are paid by
the actual I/K tails: positive-order I decays at the left, imaginary K
and its first log derivative are bounded there, and both K jets decay
at the right. Integration by parts gives the resolvent multiplier.
No Plancherel or assumed intertwining theorem is used.
-/
namespace ImbalancedChen.Part3.ActualGreenKLTransform20261025a
noncomputable section
open Set MeasureTheory Filter Topology
open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ActualGreenCompactForcing20261025a
open ActualGreenForcingRegularity20261025a ActualGreenForcingEnergy20261025a
open GeneralIRealPositiveEndpoint20261025a GeneralKRightEndpoint20261025a
open ActualImaginaryKLeftJetBound20261025a ActualKLCompactTestIntegrationByParts20261025a

private theorem legal_order {kappa : ℝ} (hkappa : 0 < kappa) :
    -1 < (kappa : ℂ).re := by simp only [Complex.ofReal_re]; linarith

theorem exists_greenForcing_left_jet_bound {kappa : ℝ} (hkappa : 0 < kappa)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r ≤ R,
      ‖greenForcing (kappa : ℂ) f r‖ ≤ C * Real.exp (kappa*r) ∧
      ‖deriv (greenForcing (kappa : ℂ) f) r‖ ≤ C * Real.exp (kappa*r) := by
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  have hz : ∀ s ≤ a-1, f s = 0 := by
    intro s hs
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := ha hmem
    linarith
  obtain ⟨C, R, hC, hb⟩ := exists_left_exponential_bound hkappa
  let A : ℂ := ∫ s : ℝ, radialK (kappa : ℂ) s * f s
  refine ⟨C * ‖A‖ + 1, min (a-1) R, by positivity, ?_⟩
  intro r hr
  have hI : ‖radialI (kappa : ℂ) r‖ ≤ C * Real.exp (kappa*r) ∧
      ‖deriv (radialI (kappa : ℂ)) r‖ ≤ C * Real.exp (kappa*r) := by
    simpa only [radialI, realILogMode] using hb r (hr.trans (min_le_right _ _))
  rw [greenForcing_left_tail (legal_order hkappa) hf hc hz (hr.trans (min_le_left _ _)),
    greenForcing_deriv_left_tail (legal_order hkappa) hf hc hz (hr.trans (min_le_left _ _)),
    norm_mul, norm_mul]
  constructor
  · have h := mul_le_mul_of_nonneg_right hI.1 (norm_nonneg A)
    dsimp only [A] at h ⊢
    nlinarith [Real.exp_pos (kappa*r)]
  · have h := mul_le_mul_of_nonneg_right hI.2 (norm_nonneg A)
    dsimp only [A] at h ⊢
    nlinarith [Real.exp_pos (kappa*r)]

private theorem exists_radialK_right_jet_bound (nu : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 ≤ r →
      ‖radialK nu r‖ ≤ C * Real.exp (-(r/2)) ∧
      ‖deriv (radialK nu) r‖ ≤ C * Real.exp (-(r/2)) := by
  let C := momentMass 0 nu + 2 * Real.exp 1 * momentMass 1 nu + 1
  have h0 := momentMass_nonneg 0 nu
  have h1 := momentMass_nonneg 1 nu
  have hD : 0 ≤ 2 * Real.exp 1 * momentMass 1 nu := by positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro r hr
  constructor
  · apply (radialK_norm_exp_bound nu hr).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [C]
    linarith
  · apply (radialK_deriv_norm_exp_bound nu hr).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [C]
    linarith

theorem exists_greenForcing_right_jet_bound {kappa : ℝ} (hkappa : 0 < kappa)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ C R : ℝ, 0 < C ∧ ∀ r : ℝ, R ≤ r →
      ‖greenForcing (kappa : ℂ) f r‖ ≤ C * Real.exp (-(r/2)) ∧
      ‖deriv (greenForcing (kappa : ℂ) f) r‖ ≤ C * Real.exp (-(r/2)) := by
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  have hz : ∀ s : ℝ, b+1 ≤ s → f s = 0 := by
    intro s hs
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hb hmem
    linarith
  obtain ⟨C, hC, hbound⟩ := exists_radialK_right_jet_bound (kappa : ℂ)
  let A : ℂ := ∫ s : ℝ, radialI (kappa : ℂ) s * f s
  refine ⟨C * ‖A‖ + 1, max (b+1) 0, by positivity, ?_⟩
  intro r hr
  have hK := hbound r ((le_max_right _ _).trans hr)
  rw [greenForcing_right_tail (legal_order hkappa) hf hc hz ((le_max_left _ _).trans hr),
    greenForcing_deriv_right_tail (legal_order hkappa) hf hc hz ((le_max_left _ _).trans hr),
    norm_mul, norm_mul]
  constructor
  · have h := mul_le_mul_of_nonneg_right hK.1 (norm_nonneg A)
    dsimp only [A] at h ⊢
    nlinarith [Real.exp_pos (-(r/2))]
  · have h := mul_le_mul_of_nonneg_right hK.2 (norm_nonneg A)
    dsimp only [A] at h ⊢
    nlinarith [Real.exp_pos (-(r/2))]

private theorem two_end_control {g : ℝ → ℂ} (hg : Continuous g)
    {kappa : ℝ} (hkappa : 0 < kappa) (A B L R : ℝ)
    (hL : ∀ r ≤ L, ‖g r‖ ≤ A * Real.exp (kappa*r))
    (hR : ∀ r : ℝ, R ≤ r → ‖g r‖ ≤ B * Real.exp (-r)) :
    Integrable g ∧ Tendsto g atBot (𝓝 0) ∧ Tendsto g atTop (𝓝 0) := by
  have hiL : IntegrableOn g (Iic L) := by
    apply ((integrableOn_exp_mul_Iic hkappa L).const_mul A).mono'
      hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
    exact hL r hr
  have hiR : IntegrableOn g (Ioi R) := by
    apply ((integrableOn_exp_neg_Ioi R).const_mul B).mono' hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hR r hr.le
  have hiC : IntegrableOn g (Icc L R) := hg.continuousOn.integrableOn_compact isCompact_Icc
  have hcover : Iic L ∪ Icc L R ∪ Ioi R = (univ : Set ℝ) := by
    ext r
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases h : r ≤ L
    · exact Or.inl (Or.inl h)
    · by_cases h' : r ≤ R
      · exact Or.inl (Or.inr ⟨(lt_of_not_ge h).le, h'⟩)
      · exact Or.inr (lt_of_not_ge h')
  refine ⟨by simpa only [hcover, integrableOn_univ] using (hiL.union hiC).union hiR, ?_, ?_⟩
  · apply squeeze_zero_norm' (by
      filter_upwards [eventually_le_atBot L] with r hr
      exact hL r hr)
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hkappa)).const_mul A
  · apply squeeze_zero_norm' (by
      filter_upwards [eventually_ge_atTop R] with r hr
      exact hR r hr)
    simpa only [mul_zero] using
      (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul B

private theorem forcing_K_jet_product_control {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (tau : ℝ) (htau : tau ≠ 0) (x y : ℝ → ℂ)
    (hx : x = greenForcing (kappa : ℂ) f ∨ x = deriv (greenForcing (kappa : ℂ) f))
    (hy : y = radialK ((tau : ℂ)*Complex.I) ∨ y = deriv (radialK ((tau : ℂ)*Complex.I))) :
    Integrable (fun r => x r*y r) ∧ Tendsto (fun r => x r*y r) atBot (𝓝 0) ∧
      Tendsto (fun r => x r*y r) atTop (𝓝 0) := by
  have hU := greenForcing_C2 (by simpa using hkappa) (by simpa using hkappaUpper) hf hc
  have hK := radialK_C2 ((tau : ℂ)*Complex.I)
  have hxc : Continuous x := by
    rcases hx with rfl | rfl
    · exact hU.continuous
    · exact hU.continuous_deriv (by norm_num)
  have hyc : Continuous y := by
    rcases hy with rfl | rfl
    · exact hK.continuous
    · exact hK.continuous_deriv (by norm_num)
  obtain ⟨CL, L, hCL, hbL⟩ := exists_greenForcing_left_jet_bound hkappa hf hc
  obtain ⟨DL, L', hDL, hbL'⟩ := exists_imaginaryK_left_jet_bound tau htau
  obtain ⟨CR, R, hCR, hbR⟩ := exists_greenForcing_right_jet_bound hkappa hf hc
  obtain ⟨DR, hDR, hbR'⟩ := exists_radialK_right_jet_bound ((tau : ℂ)*Complex.I)
  apply two_end_control (hxc.mul hyc) hkappa (CL*DL) (CR*DR) (min L L') (max R 0)
  · intro r hr
    have hx' : ‖x r‖ ≤ CL*Real.exp(kappa*r) := by
      rcases hx with rfl | rfl
      · exact (hbL r (hr.trans (min_le_left _ _))).1
      · exact (hbL r (hr.trans (min_le_left _ _))).2
    have hy' : ‖y r‖ ≤ DL := by
      rcases hy with rfl | rfl
      · exact (hbL' r (hr.trans (min_le_right _ _))).1
      · exact (hbL' r (hr.trans (min_le_right _ _))).2
    rw [norm_mul]
    calc
      _ ≤ (CL*Real.exp(kappa*r))*DL := mul_le_mul hx' hy' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · intro r hr
    have hx' : ‖x r‖ ≤ CR*Real.exp(-(r/2)) := by
      rcases hx with rfl | rfl
      · exact (hbR r ((le_max_left _ _).trans hr)).1
      · exact (hbR r ((le_max_left _ _).trans hr)).2
    have hy' : ‖y r‖ ≤ DR*Real.exp(-(r/2)) := by
      rcases hy with rfl | rfl
      · exact (hbR' r ((le_max_right _ _).trans hr)).1
      · exact (hbR' r ((le_max_right _ _).trans hr)).2
    rw [norm_mul]
    calc
      _ ≤ (CR*Real.exp(-(r/2)))*(DR*Real.exp(-(r/2))) :=
        mul_le_mul hx' hy' (norm_nonneg _) (by positivity)
      _ = (CR*DR)*Real.exp(-r) := by
        rw [show (CR*Real.exp(-(r/2)))*(DR*Real.exp(-(r/2))) =
          (CR*DR)*(Real.exp(-(r/2))*Real.exp(-(r/2))) by ring, ← Real.exp_add]
        congr 2
        ring

theorem actualKtransform_greenForcing_integrable {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (tau : ℝ) (htau : tau ≠ 0) :
    Integrable (fun r : ℝ => greenForcing (kappa : ℂ) f r *
      radialK ((tau : ℂ)*Complex.I) r) :=
  (forcing_K_jet_product_control hkappa hkappaUpper hf hc tau htau _ _
    (Or.inl rfl) (Or.inl rfl)).1

theorem greenForcing_K_flux_endpoints {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (tau : ℝ) (htau : tau ≠ 0) :
    Tendsto (flux (greenForcing (kappa : ℂ) f) (radialK ((tau : ℂ)*Complex.I))) atBot (𝓝 0) ∧
    Tendsto (flux (greenForcing (kappa : ℂ) f) (radialK ((tau : ℂ)*Complex.I))) atTop (𝓝 0) := by
  have h1 := forcing_K_jet_product_control hkappa hkappaUpper hf hc tau htau _ _
    (Or.inr rfl) (Or.inl rfl)
  have h2 := forcing_K_jet_product_control hkappa hkappaUpper hf hc tau htau _ _
    (Or.inl rfl) (Or.inr rfl)
  exact ⟨by simpa only [flux, sub_zero] using h1.2.1.sub h2.2.1,
    by simpa only [flux, sub_zero] using h1.2.2.sub h2.2.2⟩

/-- Literal integral intertwining, including convergence and the actual
remote endpoint calculation. Every nonzero real tau is covered. -/
theorem actualKtransform_greenForcing_mul {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (tau : ℝ) (htau : tau ≠ 0) :
    ((kappa : ℂ)^2 + (tau : ℂ)^2) * actualKtransform (greenForcing (kappa : ℂ) f) tau =
      actualKtransform f tau := by
  let U := greenForcing (kappa : ℂ) f
  let K := radialK ((tau : ℂ)*Complex.I)
  have hU : ContDiff ℝ 2 U :=
    greenForcing_C2 (by simpa using hkappa) (by simpa using hkappaUpper) hf hc
  have hK : ContDiff ℝ 2 K := radialK_C2 _
  have hprod : Integrable (fun r : ℝ => U r*K r) :=
    actualKtransform_greenForcing_integrable hkappa hkappaUpper hf hc tau htau
  have hfK : Integrable (fun r : ℝ => f r*K r) := actualKtransform_integrable f hf hc tau
  have hderiv (r : ℝ) : deriv (flux U K) r =
      ((kappa : ℂ)^2+(tau : ℂ)^2)*(U r*K r)-f r*K r := by
    rw [flux_derivative U K hU hK]
    have hu : deriv (deriv U) r = potential (kappa : ℂ) r*U r-f r :=
      congrFun (greenForcing_second_deriv (by simpa using hkappa)
        (by simpa using hkappaUpper) hf hc) r
    rw [hu]
    have hk := actual_radialK_homogeneous ((tau : ℂ)*Complex.I) r
    change -deriv (deriv K) r + potential ((tau : ℂ)*Complex.I) r*K r = 0 at hk
    simp only [potential, mul_pow, Complex.I_sq, mul_neg, mul_one] at hk ⊢
    linear_combination U r * hk
  have hd (r : ℝ) : HasDerivAt (flux U K)
      (((kappa : ℂ)^2+(tau : ℂ)^2)*(U r*K r)-f r*K r) r := by
    rw [← hderiv r]
    exact ((flux_C1 U K hU hK).differentiable_one r).hasDerivAt
  have hi := (hprod.const_mul ((kappa : ℂ)^2+(tau : ℂ)^2)).sub hfK
  obtain ⟨hbot, htop⟩ := greenForcing_K_flux_endpoints hkappa hkappaUpper hf hc tau htau
  have hint := integral_of_hasDerivAt_of_tendsto hd hi hbot htop
  rw [integral_sub (hprod.const_mul _) hfK, integral_const_mul] at hint
  simpa only [actualKtransform, U, K, sub_zero, sub_eq_zero] using hint

theorem actualKtransform_greenForcing {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (tau : ℝ) (htau : tau ≠ 0) :
    actualKtransform (greenForcing (kappa : ℂ) f) tau =
      actualKtransform f tau / ((kappa : ℂ)^2 + (tau : ℂ)^2) := by
  have hpos : 0 < kappa^2+tau^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hkappa) (sq_nonneg tau)
  have hn : (kappa : ℂ)^2+(tau : ℂ)^2 ≠ 0 := by exact_mod_cast hpos.ne'
  apply (eq_div_iff hn).mpr
  rw [mul_comm]
  exact actualKtransform_greenForcing_mul hkappa hkappaUpper hf hc tau htau

end
end ImbalancedChen.Part3.ActualGreenKLTransform20261025a
