import ImbalancedChen.Part3GammaKernelPlanarWeakEquation
import ImbalancedChen.Part3Gamma0ActualConstantMode
import Mathlib.Analysis.Complex.RealDeriv

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
The actual native Gamma0 Friedrichs kernel consists of scalar constants.
This is the missing kernel-to-constant direction: it uses the ORIGINAL
kernel weak equation, actual quotient local L², proved rectangle rigidity,
positive-overlap gluing, and descent to the original quotient measure.
No constancy, regular representative, Poincare inequality, or final kernel
identification is supplied as a hypothesis. The reverse inclusion is separate. -/
namespace ImbalancedChen.Part3.GammaFriedrichsKernelConstantRigidity20261026a
noncomputable section
open Set Function MeasureTheory Filter
open scoped ContDiff UpperHalfPlane
open ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
open ImbalancedChen.Part3.WeakGradientUpperHalfPlaneRigidity20261026a
open ImbalancedChen.Part3.GammaQuotientPlanarLocalL220261026a
open ImbalancedChen.Part3.GammaKernelPlanarWeakEquation20261026a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a

theorem real_tensor_gradient_horizontal (T : SmoothPositiveTensor) (p : ℝ × ℝ) :
    tensorGradient false (toMaassTensor T) p = ((deriv T.horizontal p.1 * T.vertical p.2 : ℝ) : ℂ) := by
  have hd : deriv (Complex.ofRealCLM ∘ T.horizontal) p.1 = (deriv T.horizontal p.1 : ℂ) :=
    (((T.horizontal_smooth.differentiable (by simp)) p.1).hasDerivAt.ofReal_comp).deriv
  change deriv (Complex.ofRealCLM ∘ T.horizontal) p.1 * (T.vertical p.2 : ℂ) = _
  rw [hd,Complex.ofReal_mul]

theorem real_tensor_gradient_vertical (T : SmoothPositiveTensor) (p : ℝ × ℝ) :
    tensorGradient true (toMaassTensor T) p = ((T.horizontal p.1 * deriv T.vertical p.2 : ℝ) : ℂ) := by
  have hd : deriv (Complex.ofRealCLM ∘ T.vertical) p.2 = (deriv T.vertical p.2 : ℂ) :=
    (((T.vertical_smooth.differentiable (by simp)) p.2).hasDerivAt.ofReal_comp).deriv
  change (T.horizontal p.1 : ℂ) * deriv (Complex.ofRealCLM ∘ T.vertical) p.2 = _
  rw [hd,Complex.ofReal_mul]

theorem tensorPairing_eq_global_of_support {a b c d : ℝ}
    (f : (ℝ × ℝ) → ℂ) {g h : ℝ → ℝ}
    (hgs : tsupport g ⊆ Ioo a b) (hhs : tsupport h ⊆ Ioo c d) :
    tensorPairing (openRectangle a b c d) f g h = ∫ p : ℝ × ℝ, tensorTest g h p • f p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  by_cases hx : p.1 ∈ Ioo a b
  · have hy : p.2 ∉ Ioo c d := fun hy => hp ⟨hx,hy⟩
    simp [tensorTest,image_eq_zero_of_notMem_tsupport (fun ht => hy (hhs ht))]
  · simp [tensorTest,image_eq_zero_of_notMem_tsupport (fun ht => hx (hgs ht))]

/-- Every real smooth local tensor is an actual admissible complex core tensor;
its complex derivative is proved to be the coercion of its real derivative. -/
theorem native_kernel_zero_weak_rectangle (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0)
    (a b c d : ℝ) (hc : 0 < c) :
    ZeroWeakPartialsOnRectangle (quotientPlanarRepresentative N (u : QuotientL2 N)) a b c d := by
  constructor
  · intro g h hg hgc hgs hh hhc hhs
    let T : SmoothPositiveTensor :=
      { horizontal := g, vertical := h, horizontal_smooth := hg, vertical_smooth := hh,
        horizontal_compact := hgc, vertical_compact := hhc,
        vertical_positive := fun y hy => lt_trans hc (hhs hy).1 }
    have hz := native_kernel_planar_tensor N u hu false (toMaassTensor T)
    rw [tensorPairing_eq_global_of_support _ (tsupport_deriv_subset.trans hgs) hhs]
    calc
      _ = ∫ p : ℝ × ℝ, star (tensorGradient false (toMaassTensor T) p) *
          quotientPlanarRepresentative N (u : QuotientL2 N) p := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          rw [real_tensor_gradient_horizontal]
          simp [T,tensorTest,Complex.real_smul]
      _ = 0 := hz
  · intro g h hg hgc hgs hh hhc hhs
    let T : SmoothPositiveTensor :=
      { horizontal := g, vertical := h, horizontal_smooth := hg, vertical_smooth := hh,
        horizontal_compact := hgc, vertical_compact := hhc,
        vertical_positive := fun y hy => lt_trans hc (hhs hy).1 }
    have hz := native_kernel_planar_tensor N u hu true (toMaassTensor T)
    rw [tensorPairing_eq_global_of_support _ hgs (tsupport_deriv_subset.trans hhs)]
    calc
      _ = ∫ p : ℝ × ℝ, star (tensorGradient true (toMaassTensor T) p) *
          quotientPlanarRepresentative N (u : QuotientL2 N) p := by
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          rw [real_tensor_gradient_vertical]
          simp [T,tensorTest,Complex.real_smul]
      _ = 0 := hz

/-- The original native kernel vector is ONE ae constant on the actual quotient. -/
theorem native_friedrichs_kernel_ae_constant (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0) :
    ∃ C : ℂ, ∀ᵐ q ∂carrierPushforward N, (u : QuotientL2 N) q = C := by
  obtain ⟨C,hC⟩ := ae_eq_one_const_of_zero_weak_gradient
    (quotientPlanarRepresentative_memLp_exhaustion N (u : QuotientL2 N))
    (fun n => native_kernel_zero_weak_rectangle N u hu _ _ _ _
      (one_div_pos.mpr (exhaustionRadius_pos n)))
  exact ⟨C,quotient_ae_const_of_planar_ae_const N (u : QuotientL2 N) C hC⟩

/-- The requested kernel-subset-constants conclusion is equality in the original
quotient Hilbert space, with its existing constant-one vector. -/
theorem native_friedrichs_kernel_eq_scalar_constant (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0) :
    ∃ C : ℂ, (u : QuotientL2 N) = C • Gamma0ActualConstantMode20261025a.constantL2 N := by
  obtain ⟨C,hC⟩ := native_friedrichs_kernel_ae_constant N u hu
  refine ⟨C,Lp.ext ?_⟩
  filter_upwards [hC,Gamma0ActualConstantMode20261025a.constantL2_ae N,
    Lp.coeFn_smul C (Gamma0ActualConstantMode20261025a.constantL2 N)] with q hq hc hs
  rw [hq,hs]
  simp [hc]

theorem native_friedrichs_kernel_mem_constant_line (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0) :
    (u : QuotientL2 N) ∈ Submodule.span ℂ {Gamma0ActualConstantMode20261025a.constantL2 N} := by
  obtain ⟨C,hC⟩ := native_friedrichs_kernel_eq_scalar_constant N u hu
  rw [hC]
  exact Submodule.smul_mem _ C (Submodule.subset_span (by simp))

end
end ImbalancedChen.Part3.GammaFriedrichsKernelConstantRigidity20261026a
