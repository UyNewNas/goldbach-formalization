import ImbalancedChen.Part3ActualGreenSmoothFormInverse
import ImbalancedChen.Part3ActualGreenColumnL2
import ImbalancedChen.Part3ActualRadialGreenSchur
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual kernel integral is defined on every L2 vector. Its pointwise
action is a continuous Hilbert functional, because every actual Green
column belongs to L2. Smooth compact approximation and an a.e. subsequence
of the actual form-inverse outputs identify this literal integral with
the form inverse for arbitrary L2 forcing. The native toLp integral is
then packaged as a continuous linear map, with its actual Schur bound.
-/
namespace ImbalancedChen.Part3.ActualGreenL2IntegralInverse20261025a
noncomputable section
open Set MeasureTheory Filter Topology
open RadialSchrodingerL2Form20261025a GeneralActualRadialGreenSourceOnly
open ActualGreenCompactForcing20261025a ActualGreenSmoothFormInverse20261025a
open ActualGreenColumnL220261025a ActualRadialGreenMassBound20261025a
open ActualRadialGreenSchur20261025a

/-- Literal integration against the same normalized I/K kernel. The
input is the canonical measurable representative of an L2 vector. -/
def actualL2GreenIntegral (kappa : ℝ) (F : RadialL2) (r : ℝ) : ℂ :=
  ∫ s : ℝ, actualRadialGreen (kappa : ℂ) r s * F s

def actualGreenColumnL2 (kappa : ℝ) (hkappa : 0 < kappa) (r : ℝ) : RadialL2 :=
  (actualRadialGreen_memLp_two hkappa r).toLp (actualRadialGreen (kappa : ℂ) r)

private theorem actualGreen_star {kappa : ℝ} (hkappa : 0 < kappa) (r s : ℝ) :
    star (actualRadialGreen (kappa : ℂ) r s) = actualRadialGreen (kappa : ℂ) r s := by
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
  · simp only [Complex.star_def, Complex.conj_im, actualGreen_real_im_zero hkappa, neg_zero]

theorem actualL2GreenIntegral_eq_inner {kappa : ℝ} (hkappa : 0 < kappa)
    (F : RadialL2) (r : ℝ) :
    actualL2GreenIntegral kappa F r = inner ℂ (actualGreenColumnL2 kappa hkappa r) F := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(actualRadialGreen_memLp_two hkappa r).coeFn_toLp] with s hs
  rw [hs]
  simp only [RCLike.inner_apply', actualGreen_star hkappa]

/-- Every pointwise integral is a genuine absolutely integrable L2
pairing; no a.e. pointwise action is silently totalized from divergence. -/
theorem actualL2GreenIntegral_integrable {kappa : ℝ} (hkappa : 0 < kappa)
    (F : RadialL2) (r : ℝ) :
    Integrable (fun s : ℝ => actualRadialGreen (kappa : ℂ) r s * F s) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (actualGreenColumnL2 kappa hkappa r) F).congr
  filter_upwards [(actualRadialGreen_memLp_two hkappa r).coeFn_toLp] with s hs
  rw [hs]
  simp only [RCLike.inner_apply', actualGreen_star hkappa]

theorem actualL2GreenIntegral_point_continuous {kappa : ℝ} (hkappa : 0 < kappa) (r : ℝ) :
    Continuous (fun F : RadialL2 => actualL2GreenIntegral kappa F r) := by
  have he : (fun F : RadialL2 => actualL2GreenIntegral kappa F r) =
      innerSL ℂ (actualGreenColumnL2 kappa hkappa r) :=
    funext (fun F => actualL2GreenIntegral_eq_inner hkappa F r)
  rw [he]
  exact (innerSL ℂ (actualGreenColumnL2 kappa hkappa r)).continuous

theorem actualL2GreenIntegral_core (kappa : ℝ) (T : RadialTest) (r : ℝ) :
    actualL2GreenIntegral kappa (radialCoreL2 T) r =
      greenForcing (kappa : ℂ) T.function r := by
  apply integral_congr_ae
  filter_upwards [T.function_memLp.coeFn_toLp] with s hs
  rw [hs, actualGreen_symmetric (kappa : ℂ) r s]

private theorem exists_core_sequence (F : RadialL2) :
    ∃ T : ℕ → RadialTest, Tendsto (fun n => radialCoreL2 (T n)) atTop (𝓝 F) := by
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp (radialCoreL2_range_dense F)
  choose T hT using hf
  exact ⟨T, by simpa only [hT] using hlim⟩

/-- Identification on arbitrary L2 forcing. Pointwise convergence of
actual kernel pairings and a.e. convergence of the same form outputs
have a common limit. No density of L(C_c^infty) is invoked. -/
theorem actualL2GreenIntegral_eq_form_inverse {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    actualL2GreenIntegral kappa F =ᵐ[(volume : Measure ℝ)]
      (radialShiftedVariationalInverse kappa F : ℝ → ℂ) := by
  obtain ⟨T, hT⟩ := exists_core_sequence F
  have hR := (radialShiftedVariationalInverse kappa).continuous.tendsto F |>.comp hT
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hR).exists_seq_tendsto_ae
  have hall : ∀ᵐ r ∂(volume : Measure ℝ), ∀ n : ℕ,
      actualL2GreenIntegral kappa (radialCoreL2 (T n)) r =
        radialShiftedVariationalInverse kappa (radialCoreL2 (T n)) r := by
    apply ae_all_iff.mpr
    intro n
    have h := actualGreen_eq_form_inverse_smooth hkappa hkappaUpper (T n)
    simpa only [actualL2GreenIntegral_core] using h
  filter_upwards [hae, hall] with r hr hrow
  have hpoint := ((actualL2GreenIntegral_point_continuous hkappa r).tendsto F).comp
    (hT.comp hns.tendsto_atTop)
  have he : (fun i => actualL2GreenIntegral kappa (radialCoreL2 (T (ns i))) r) =
      (fun i => radialShiftedVariationalInverse kappa (radialCoreL2 (T (ns i))) r) :=
    funext (fun i => hrow (ns i))
  rw [he] at hpoint
  exact tendsto_nhds_unique hpoint hr

theorem actualL2GreenIntegral_memLp {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    MemLp (actualL2GreenIntegral kappa F) 2 (volume : Measure ℝ) :=
  (memLp_congr_ae (actualL2GreenIntegral_eq_form_inverse hkappa hkappaUpper F)).mpr
    (Lp.memLp (radialShiftedVariationalInverse kappa F))

theorem actualL2GreenIntegral_toLp_eq_form_inverse {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    (actualL2GreenIntegral_memLp hkappa hkappaUpper F).toLp (actualL2GreenIntegral kappa F) =
      radialShiftedVariationalInverse kappa F := by
  apply Lp.ext
  exact (actualL2GreenIntegral_memLp hkappa hkappaUpper F).coeFn_toLp.trans
    (actualL2GreenIntegral_eq_form_inverse hkappa hkappaUpper F)

/-- Native L2 integral operator. The copied function is literally the
toLp class of the actual integral; equality with the already constructed
form map is a preceding theorem, not a supplied inverse hypothesis. -/
def actualGreenL2Operator (kappa : ℝ) (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    RadialL2 →L[ℂ] RadialL2 :=
  (radialShiftedVariationalInverse kappa).copy
    (fun F => (actualL2GreenIntegral_memLp hkappa hkappaUpper F).toLp
      (actualL2GreenIntegral kappa F))
    (funext (actualL2GreenIntegral_toLp_eq_form_inverse hkappa hkappaUpper))

theorem actualGreenL2Operator_eq_form_inverse {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    actualGreenL2Operator kappa hkappa hkappaUpper = radialShiftedVariationalInverse kappa :=
  ContinuousLinearMap.copy_eq _ _ _

private theorem inverse_core_norm_bound {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (T : RadialTest) :
    ‖radialShiftedVariationalInverse kappa (radialCoreL2 T)‖ ≤
      (1 / kappa ^ 2) * ‖radialCoreL2 T‖ := by
  have haction : greenAction kappa T.function = greenForcing (kappa : ℂ) T.function := by
    funext r
    rw [greenAction_eq_actualKernel hkappa]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by rw [actualGreen_symmetric (kappa : ℂ) r s])
  have he : ((actualGreen_schur_energy hkappa hkappaUpper T.function T.smooth.continuous
      T.compact).1).toLp (greenAction kappa T.function) =
      radialShiftedVariationalInverse kappa (radialCoreL2 T) := by
    apply Lp.ext
    have h := (actualGreen_schur_energy hkappa hkappaUpper T.function
      T.smooth.continuous T.compact).1.coeFn_toLp
    exact h.trans ((Eventually.of_forall (fun r => congrFun haction r)).trans
      (actualGreen_eq_form_inverse_smooth hkappa hkappaUpper T))
  have hb := actualGreen_schur_toLp_norm hkappa hkappaUpper
    T.function T.smooth.continuous T.compact
  rw [he] at hb
  exact hb

theorem actualGreenL2Operator_norm_bound {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) (F : RadialL2) :
    ‖actualGreenL2Operator kappa hkappa hkappaUpper F‖ ≤ (1 / kappa ^ 2) * ‖F‖ := by
  rw [actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper]
  have hclosed : IsClosed {G : RadialL2 |
      ‖radialShiftedVariationalInverse kappa G‖ ≤ (1 / kappa ^ 2) * ‖G‖} :=
    isClosed_le (radialShiftedVariationalInverse kappa).continuous.norm
      (continuous_const.mul continuous_norm)
  have hsub : Set.range radialCoreL2 ⊆ {G : RadialL2 |
      ‖radialShiftedVariationalInverse kappa G‖ ≤ (1 / kappa ^ 2) * ‖G‖} := by
    rintro _ ⟨T, rfl⟩
    exact inverse_core_norm_bound hkappa hkappaUpper T
  exact (closure_minimal hsub hclosed) (radialCoreL2_range_dense F)

theorem actualGreenL2Operator_opNorm_bound {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1) :
    ‖actualGreenL2Operator kappa hkappa hkappaUpper‖ ≤ 1 / kappa ^ 2 := by
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (actualGreenL2Operator_norm_bound hkappa hkappaUpper)

/-- The arbitrary-L2 kernel operator solves the actual completed radial
weak equation, including its derivative and unbounded exponential energy
coordinates. These are the coordinates of its proved form-domain lift. -/
theorem actualGreenL2Operator_variational {kappa : ℝ}
    (hkappa : 0 < kappa) (hkappaUpper : kappa < 1)
    (F : RadialL2) (v : radialClosedEnergyDomain kappa) :
    (kappa ^ 2 : ℂ) * inner ℂ (actualGreenL2Operator kappa hkappa hkappaUpper F)
        (radialPhysicalEmbedding kappa v) +
      inner ℂ (radialClosedDerivative kappa (radialFormRieszSolution kappa F))
        (radialClosedDerivative kappa v) +
      inner ℂ (radialClosedExponential kappa (radialFormRieszSolution kappa F))
        (radialClosedExponential kappa v) =
      inner ℂ F (radialPhysicalEmbedding kappa v) := by
  rw [actualGreenL2Operator_eq_form_inverse hkappa hkappaUpper]
  exact radialFormRieszSolution_variational kappa hkappa F v

end
end ImbalancedChen.Part3.ActualGreenL2IntegralInverse20261025a
