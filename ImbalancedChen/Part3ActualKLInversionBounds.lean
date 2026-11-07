import ImbalancedChen.Part3ActualKLCompactTestWeightedL2

/-!
Actual bounds for the KL inversion integrand. One additional genuine
Hamiltonian transfer improves the existing transform tail by tau^-2.
Combined with the actual adaptive contour bound for K, this gives tau^-3
after the exponential KL weight cancels. The spatial lower bound q>=a>0
is retained, so this estimate is uniform on every radial compact set.
No Plancherel or inversion hypothesis is used.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLInversionBounds20261025a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactTestWeightedL220261025a ImaginaryKAdaptiveContourBound20261025a

def physicalKernelBudget (a : ℝ) : ℝ :=
  Real.exp 1 * (max 0 (Real.log (4 / a)) + 2)

theorem physicalKernelBudget_nonneg (a : ℝ) : 0 ≤ physicalKernelBudget a := by
  unfold physicalKernelBudget
  positivity

private theorem log_linear {tau : ℝ} (htau : 0 ≤ tau) :
    Real.log (1 + tau) ≤ tau := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + tau)
  linarith

theorem actualK_low_order_bound {a q tau : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    ‖complexOrderK ((tau : ℂ) * Complex.I) q‖ ≤ physicalKernelBudget a := by
  have h := complexOrderK_imaginary_norm_le_adaptive ha haq tau
  rw [abs_of_nonneg htau] at h
  have he : Real.exp (-Real.pi * tau / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hl : Real.log (1 + tau) ≤ 1 := (log_linear htau).trans htau1
  have hb : 0 ≤ Real.log (1 + tau) + max 0 (Real.log (4 / a)) + 1 := by
    have := Real.log_nonneg (show 1 ≤ 1 + tau by linarith)
    positivity
  apply h.trans
  unfold physicalKernelBudget
  calc
    _ ≤ Real.exp 1 * 1 * (Real.log (1 + tau) + max 0 (Real.log (4 / a)) + 1) := by
      gcongr
    _ ≤ _ := by nlinarith [Real.exp_pos (1 : ℝ)]

theorem actualK_high_order_bound {a q tau : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (htau : 1 ≤ tau) :
    ‖complexOrderK ((tau : ℂ) * Complex.I) q‖ ≤
      physicalKernelBudget a * tau * Real.exp (-Real.pi * tau / 2) := by
  have htau0 : 0 ≤ tau := zero_le_one.trans htau
  have h := complexOrderK_imaginary_norm_le_adaptive ha haq tau
  rw [abs_of_nonneg htau0] at h
  have hl := log_linear htau0
  have hm : 0 ≤ max 0 (Real.log (4 / a)) := le_max_left _ _
  have hb : Real.log (1 + tau) + max 0 (Real.log (4 / a)) + 1 ≤
      (max 0 (Real.log (4 / a)) + 2) * tau := by nlinarith
  apply h.trans
  calc
    _ ≤ Real.exp 1 * Real.exp (-Real.pi * tau / 2) *
        ((max 0 (Real.log (4 / a)) + 2) * tau) := by gcongr
    _ = _ := by unfold physicalKernelBudget; ring

/-- The third true Hamiltonian transfer needed for absolute inversion. -/
theorem actualKtransform_third_transfer_bound (T : RadialTest) {a : ℝ}
    (ha : 0 < a) (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {tau : ℝ} (htau : 1 ≤ tau) :
    ‖actualKtransform T.function tau‖ ≤
      contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
        Real.exp (-Real.pi * tau / 2) / tau ^ 5 := by
  have hp : 0 < tau := zero_lt_one.trans_le htau
  have hs : ∀ r ∈ tsupport (hamiltonianTest T).function, a ≤ Real.exp r :=
    fun r hr => hsupport r (hamiltonianTest_support_subset T hr)
  have h := actualKtransform_high_bound (hamiltonianTest T) ha hs htau
  have he := congrArg norm (actualKtransform_hamiltonian T tau)
  have hn : ‖actualKtransform (hamiltonianTest T).function tau‖ =
      tau ^ 2 * ‖actualKtransform T.function tau‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hp] using he
  have hh := (le_div_iff₀ (pow_pos hp 3)).mp h
  rw [hn] at hh
  apply (le_div_iff₀ (pow_pos hp 5)).mpr
  convert hh using 1 <;> ring

/-- Same literal K and same 2/pi^2 normalization as the compact KL energy. -/
def actualKLInversionIntegrand (T : RadialTest) (r tau : ℝ) : ℂ :=
  (actualKLWeight tau : ℂ) * actualKtransform T.function tau *
    radialK ((tau : ℂ) * Complex.I) r

private theorem sinh_le_exp (x : ℝ) : Real.sinh x ≤ Real.exp x := by
  rw [Real.sinh_eq]
  linarith [Real.exp_pos x, Real.exp_pos (-x)]

theorem actualKLInversionIntegrand_low_bound (T : RadialTest) {a : ℝ}
    (ha : 0 < a) (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {r tau : ℝ} (hr : a ≤ Real.exp r) (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    ‖actualKLInversionIntegrand T r tau‖ ≤
      normalization * Real.exp Real.pi * contourBudget T a * physicalKernelBudget a := by
  have hf := actualKtransform_low_bound T ha hsupport htau htau1
  have hk := actualK_low_order_bound ha hr htau htau1
  have hCB := contourBudget_nonneg T a
  have hKB := physicalKernelBudget_nonneg a
  have hN := normalization_pos.le
  have hw : actualKLWeight tau ≤ normalization * Real.exp Real.pi := by
    have hs : Real.sinh (Real.pi * tau) ≤ Real.exp Real.pi :=
      (sinh_le_exp _).trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos]))
    have hmul := mul_le_mul htau1 hs
      (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le htau)) zero_le_one
    have hm := mul_le_mul_of_nonneg_left hmul normalization_pos.le
    simpa only [one_mul, actualKLWeight, mul_assoc] using hm
  unfold actualKLInversionIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (actualKLWeight_nonneg htau)]
  exact mul_le_mul (mul_le_mul hw hf (norm_nonneg _) (by positivity)) hk
    (norm_nonneg _) (by positivity)

/-- The exponential cancellation leaves a locally uniform integrable
tau^-3 tail, without any assumed inverse-transform convergence. -/
theorem actualKLInversionIntegrand_high_bound (T : RadialTest) {a : ℝ}
    (ha : 0 < a) (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {r tau : ℝ} (hr : a ≤ Real.exp r) (htau : 1 ≤ tau) :
    ‖actualKLInversionIntegrand T r tau‖ ≤
      (normalization * contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
        physicalKernelBudget a) * (tau ^ 3)⁻¹ := by
  have hp : 0 < tau := zero_lt_one.trans_le htau
  have hf := actualKtransform_third_transfer_bound T ha hsupport htau
  have hk := actualK_high_order_bound ha hr htau
  have hCB := contourBudget_nonneg (hamiltonianIterate 2 (hamiltonianTest T)) a
  have hKB := physicalKernelBudget_nonneg a
  have hN := normalization_pos.le
  have hw : actualKLWeight tau ≤ normalization * tau * Real.exp (Real.pi * tau) :=
    mul_le_mul_of_nonneg_left (sinh_le_exp _) (mul_nonneg normalization_pos.le hp.le)
  have he : Real.exp (Real.pi * tau) * Real.exp (-Real.pi * tau / 2) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  unfold actualKLInversionIntegrand
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (actualKLWeight_nonneg hp.le)]
  calc
    _ ≤ (normalization * tau * Real.exp (Real.pi * tau)) *
        (contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
          Real.exp (-Real.pi * tau / 2) / tau ^ 5) *
        (physicalKernelBudget a * tau * Real.exp (-Real.pi * tau / 2)) := by
      exact mul_le_mul (mul_le_mul hw hf (norm_nonneg _) (by positivity)) hk
        (norm_nonneg _) (by positivity)
    _ = (normalization * contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
        physicalKernelBudget a) *
        (Real.exp (Real.pi * tau) * Real.exp (-Real.pi * tau / 2) ^ 2) / tau ^ 3 := by
      field_simp [hp.ne']
      <;> ring
    _ = _ := by rw [he]; ring

end
end ImbalancedChen.Part3.ActualKLInversionBounds20261025a
