import ImbalancedChen.Part3Gamma0EnergyGeometricWeakGradient
import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The SHARP core local-gradient bound propagates through the genuine dense
energy completion with the unshifted Dirichlet energy retained. The
native actual Friedrichs form association then makes every kernel vector
have zero gradient in every compact local vector L2 space. Its physical
orbit pullback therefore has zero weak coordinate partials against ALL
finite compact tensor tests with closed support containers in interior K.
This does not prove the weak fundamental lemma that such a function is
constant. No adjoint-defect vector is assumed to belong to the form domain.
-/

namespace ImbalancedChen.Part3.Gamma0FriedrichsKernelZeroWeakGradient20261025a
noncomputable section
open Set Filter Function MeasureTheory
open UniformSpace
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.ActualGamma0CoreDirichletForm20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0PhysicalClosedDirichletForm20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactCoreGradient20261025a
open ImbalancedChen.Part3.Gamma0EnergyCompactGradientExtension20261025a
open ImbalancedChen.Part3.OneCompactFirstGradientIBP20261025a
open ImbalancedChen.Part3.Gamma0EnergyGeometricWeakGradient20261025a

theorem completedCompactGradient_sharp_energy_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖completedCompactGradient N hK e‖^2 ≤
      (compactOverlapBound N K : ℝ)*(‖e‖^2-‖physicalProjection N e‖^2) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_le ((completedCompactGradient N hK).continuous.norm.pow 2)
      (continuous_const.mul ((continuous_id.norm.pow 2).sub
        ((physicalProjection N).continuous.norm.pow 2)))
  · intro u
    rw [completedCompactGradient_core,coreEmbedding_norm,physicalProjection_core]
    have hdiff : ‖u‖^2-‖physicalCore N u‖^2=(coreDirichletForm N u u).re := by
      rw [coreDirichletForm_eq_operatorPair]
      change ‖u‖^2-‖physicalCore N u‖^2=
        (inner ℂ (physicalCore N u) (coreLaplacian N u)).re
      linarith [energy_norm_sq N u]
    rw [hdiff,coreGradientL2_norm_sq]
    exact weightedCoreGradient_compact_integral_le N hK u

theorem actualDirichletPair_self_re_eq_energy_defect (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    (actualDirichletPair N e e).re=‖e‖^2-‖physicalProjection N e‖^2 := by
  rw [actualDirichletPair,Complex.sub_re,
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
    ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- The local gradient is controlled by the ACTUAL unshifted closed
form, not just by the larger shifted completion norm. -/
theorem completedCompactGradient_sharp_Dirichlet_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N) :
    ‖completedCompactGradient N hK e‖^2 ≤
      (compactOverlapBound N K : ℝ)*(actualDirichletPair N e e).re := by
  rw [actualDirichletPair_self_re_eq_energy_defect]
  exact completedCompactGradient_sharp_energy_bound N hK e

theorem completedCompactGradient_eq_zero_of_Dirichlet_zero (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (e : EnergyCompletion N)
    (he : (actualDirichletPair N e e).re=0) : completedCompactGradient N hK e=0 := by
  have hb := completedCompactGradient_sharp_Dirichlet_bound N hK e
  rw [he,mul_zero] at hb
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hb (sq_nonneg _)))

/-- The native operator domain is included in the ALREADY existing
physical form domain; the energy lift is its original injective J inverse. -/
def friedrichsFormPoint (N : ℕ) [NeZero N] (u : (actualGammaFriedrichs N).domain) :
    actualEnergyFormDomain N :=
  ⟨(u : QuotientL2 N),actualGammaFriedrichs_domain_le_formDomain N u.property⟩

def friedrichsEnergyLift (N : ℕ) [NeZero N] (u : (actualGammaFriedrichs N).domain) :
    EnergyCompletion N := actualEnergyLift N (friedrichsFormPoint N u)

theorem friedrichsEnergyLift_projection (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    physicalProjection N (friedrichsEnergyLift N u)=(u : QuotientL2 N) :=
  actualEnergyLift_projection N (friedrichsFormPoint N u)

theorem native_friedrichs_form_testing (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (d : EnergyCompletion N) :
    actualDirichletPair N d (friedrichsEnergyLift N u)=
      inner ℂ (physicalProjection N d) (actualGammaFriedrichs N u) := by
  obtain ⟨e,he,ht⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    (LinearPMap.mem_graph _ u)
  have heq : e=friedrichsEnergyLift N u := (physicalProjection_injective N)
    (he.trans (friedrichsEnergyLift_projection N u).symm)
  simpa only [heq] using ht d

theorem native_friedrichs_kernel_Dirichlet_zero (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u=0) :
    actualDirichletPair N (friedrichsEnergyLift N u) (friedrichsEnergyLift N u)=0 := by
  rw [native_friedrichs_form_testing,hu,inner_zero_right]

theorem native_friedrichs_kernel_compactGradient_zero (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u=0)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    completedCompactGradient N hK (friedrichsEnergyLift N u)=0 :=
  completedCompactGradient_eq_zero_of_Dirichlet_zero N hK _
    (by rw [native_friedrichs_kernel_Dirichlet_zero N u hu,Complex.zero_re])

/-- All finite compact C2 tensor tests, in particular the actual smooth
tensor tests, see zero weak coordinate partials of a native kernel vector.
The subsequent weak-fundamental-lemma / constant conclusion is separate. -/
theorem native_friedrichs_kernel_zero_weak_partial (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u=0)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (hTK : finiteCompactTensorSupportK s T ⊆ interior K) :
    (∫ z in K, star (sliceFirst vertical (finiteChartFunction s T) (z.re,z.im))*
      (u : QuotientL2 N) (orbitProjection N z)*(z.im : ℂ)^2)=0 := by
  have h := completed_finite_tensor_weak_derivative N hK vertical s T hTK
    (friedrichsEnergyLift N u)
  rw [friedrichsEnergyLift_projection,native_friedrichs_kernel_compactGradient_zero N u hu hK] at h
  have hz : (∫ z in K, star (finiteCoreFunction s T z)*
      ((0 : CompactGradientL2 K) z (firstCoordinate vertical))*(z.im : ℂ))=0 := by
    calc
      _ = ∫ _z in K, (0 : ℂ) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero GradientFiber 2 ((volume : Measure UpperHalfPlane).restrict K)]
          with z hz
        rw [hz]
        simp
      _ = 0 := integral_zero
  simpa only [hz,neg_zero] using h

end
end ImbalancedChen.Part3.Gamma0FriedrichsKernelZeroWeakGradient20261025a
