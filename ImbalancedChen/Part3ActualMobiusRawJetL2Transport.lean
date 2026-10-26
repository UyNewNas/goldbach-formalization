import ImbalancedChen.Part3ActualMobiusCompactLpTransport

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Actual transpose-Jacobian transport of two RAW complex coordinate jets.
The coefficients are the real/imaginary parts of (cz+d)^(-2), computed
from the native actual Mobius map.  Pure real-linear algebra and the true
Jacobian give exact two-dimensional Dirichlet L2 mass transport.  Raw
MemLp jets remain MemLp on every positive compact chart.  No hypothesis
identifies these raw fields as weak derivatives: that closure step is
owned by the genuine weak-test argument.
-/
namespace ImbalancedChen.Part3.ActualMobiusRawJetL2Transport20261026b
noncomputable section
open Set MeasureTheory Matrix
open scoped MatrixGroups UpperHalfPlane
open ActualMobiusConformalTwoJet20261025a ActualMobiusLocalJacobian20261026b
open ActualMobiusCompactLpTransport20261026b

def rawJetX (g : SL(2, ℤ)) (U V : ℂ → ℂ) (z : ℂ) : ℂ :=
  (factor g z).re • U (actualMobius g z)+(factor g z).im • V (actualMobius g z)

def rawJetY (g : SL(2, ℤ)) (U V : ℂ → ℂ) (z : ℂ) : ℂ :=
  (-(factor g z).im) • U (actualMobius g z)+(factor g z).re • V (actualMobius g z)

/-- Genuine conformal transpose-Jacobian algebra for arbitrary raw jets. -/
theorem conformal_raw_jet_norm_sq (a U V : ℂ) :
    ‖a.re • U+a.im • V‖^2+‖(-a.im) • U+a.re • V‖^2 =
      Complex.normSq a*(‖U‖^2+‖V‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.real_smul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  ring

theorem rawJet_norm_sq (g : SL(2, ℤ)) (U V : ℂ → ℂ) (z : ℂ) :
    ‖rawJetX g U V z‖^2+‖rawJetY g U V z‖^2 =
      rawJacobian g z*(‖U (actualMobius g z)‖^2+‖V (actualMobius g z)‖^2) := by
  unfold rawJetX rawJetY
  rw [rawJacobian_eq_normSq_factor]
  exact conformal_raw_jet_norm_sq _ _ _

/-- Exact RAW first-jet energy transport: the conformal factor is the
native two-dimensional Jacobian, and therefore cancels under integration. -/
theorem rawJet_lintegral_norm_sq (g : SL(2, ℤ)) {K : Set ℂ}
    (hKm : MeasurableSet K) (hKp : ∀ z ∈ K, 0 < z.im) (U V : ℂ → ℂ) :
    (∫⁻ z in K, ENNReal.ofReal (‖rawJetX g U V z‖^2+‖rawJetY g U V z‖^2)) =
      ∫⁻ w in actualMobius g '' K, ENNReal.ofReal (‖U w‖^2+‖V w‖^2) := by
  rw [actualMobius_lintegral_image g hKm hKp]
  apply setLIntegral_congr_fun hKm
  intro z hz
  rw [rawJet_norm_sq,ENNReal.ofReal_mul (rawJacobian_pos g (hKp z hz)).le]

/-- Compactness produces bounded actual first-jet coefficients. -/
theorem rawJet_coefficients_memLp_top (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) :
    MemLp (fun z => (factor g z).re) ∞ ((volume : Measure ℂ).restrict K) ∧
      MemLp (fun z => (factor g z).im) ∞ ((volume : Measure ℂ).restrict K) := by
  have hfactor : ContinuousOn (factor g) K := fun z hz =>
    (factor_hasDerivAt g ⟨z,hKp z hz⟩).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := hK.bddAbove_image hfactor.norm
  have hreal : AEStronglyMeasurable (fun z => (factor g z).re)
      ((volume : Measure ℂ).restrict K) := (Complex.continuous_re.comp_continuousOn hfactor).aestronglyMeasurable hK.measurableSet
  have himag : AEStronglyMeasurable (fun z => (factor g z).im)
      ((volume : Measure ℂ).restrict K) := (Complex.continuous_im.comp_continuousOn hfactor).aestronglyMeasurable hK.measurableSet
  constructor
  · apply memLp_top_of_bound hreal (max 1 B)
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    calc
      ‖(factor g z).re‖ = |(factor g z).re| := Real.norm_eq_abs _
      _ ≤ ‖factor g z‖ := Complex.abs_re_le_norm _
      _ ≤ B := hB ⟨z,hz,rfl⟩
      _ ≤ max 1 B := le_max_right _ _
  · apply memLp_top_of_bound himag (max 1 B)
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    calc
      ‖(factor g z).im‖ = |(factor g z).im| := Real.norm_eq_abs _
      _ ≤ ‖factor g z‖ := Complex.abs_im_le_norm _
      _ ≤ B := hB ⟨z,hz,rfl⟩
      _ ≤ max 1 B := le_max_right _ _

/-- True target L2 jets produce true source L2 transformed jets. -/
theorem rawJet_memLp (g : SL(2, ℤ)) {K : Set ℂ}
    (hK : IsCompact K) (hKp : ∀ z ∈ K, 0 < z.im) {U V : ℂ → ℂ}
    (hU : MemLp U 2 ((volume : Measure ℂ).restrict (actualMobius g '' K)))
    (hV : MemLp V 2 ((volume : Measure ℂ).restrict (actualMobius g '' K))) :
    MemLp (rawJetX g U V) 2 ((volume : Measure ℂ).restrict K) ∧
      MemLp (rawJetY g U V) 2 ((volume : Measure ℂ).restrict K) := by
  have hUc := memLp_comp_actualMobius g hK hKp hU
  have hVc := memLp_comp_actualMobius g hK hKp hV
  obtain ⟨ha,hb⟩ := rawJet_coefficients_memLp_top g hK hKp
  exact ⟨(hUc.smul ha).add (hVc.smul hb), (hUc.smul hb.neg).add (hVc.smul ha)⟩

end
end ImbalancedChen.Part3.ActualMobiusRawJetL2Transport20261026b
