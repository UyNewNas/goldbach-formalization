import ImbalancedChen.Part3GammaQuotientPlanarLocalL2
import ImbalancedChen.Part3Gamma0FriedrichsKernelZeroWeakGradient
import Mathlib.Topology.Compactness.LocallyCompact

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
The original native Friedrichs kernel equation gives zero pairing with
EVERY genuine compact tensor derivative on the whole plane. A compact
neighborhood removes the support-container condition; the actual y² and
canonical y⁻² density cancel by the existing canonical integral theorem. -/
namespace ImbalancedChen.Part3.GammaKernelPlanarWeakEquation20261026a
noncomputable section
open Set Function MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.GammaQuotientPlanarLocalL220261026a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.OneCompactDirichletGreen20261025a
open ImbalancedChen.Part3.OneCompactFirstGradientIBP20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0EnergyGeometricWeakGradient20261025a
open ImbalancedChen.Part3.Gamma0FriedrichsKernelZeroWeakGradient20261025a

/-- Genuine compact support supplies the compact neighborhood needed by the
original weak-gradient theorem. No compact-container premise survives. -/
theorem native_kernel_global_weighted_tensor (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0)
    (vertical : Bool) (T : CompactTensor) :
    (∫ z : UpperHalfPlane, star (testDerivative vertical T z) *
      (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2) = 0 := by
  obtain ⟨K,hK,hTK⟩ := exists_compact_superset (compactTensorSupportK_isCompact T)
  let s : Finset (Fin 1) := Finset.univ
  let Ts : Fin 1 → CompactTensor := fun _ => T
  have hfinite : finiteCompactTensorSupportK s Ts ⊆ interior K := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact hTK hi
  have hlocal := native_friedrichs_kernel_zero_weak_partial N u hu hK vertical s Ts hfinite
  have hder (z : UpperHalfPlane) :
      sliceFirst vertical (finiteChartFunction s Ts) (z.re,z.im) = testDerivative vertical T z := by
    cases vertical
    · simpa [sliceFirst,s,Ts,testDerivative,tensorGradient,tensorDx] using
        sliceDx_finiteChartFunction s Ts (z.re,z.im)
    · simpa [sliceFirst,s,Ts,testDerivative,tensorGradient,tensorDy] using
        sliceDy_finiteChartFunction s Ts (z.re,z.im)
  simp_rw [hder] at hlocal
  have hsupp : ∀ z ∉ K, star (testDerivative vertical T z) *
      (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2 = 0 := by
    intro z hz
    have hd : testDerivative vertical T z = 0 := by
      by_contra hn
      exact hz (interior_subset (hTK (testDerivative_support_subset vertical T hn)))
    simp [hd]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp] at hlocal
  exact hlocal

/-- The original kernel equation, now in literal unweighted planar coordinates.
Its source is the native form association; there is no weak-equation premise. -/
theorem native_kernel_planar_tensor (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : actualGammaFriedrichs N u = 0)
    (vertical : Bool) (T : CompactTensor) :
    (∫ p : ℝ × ℝ, star (tensorGradient vertical T p) *
      quotientPlanarRepresentative N (u : QuotientL2 N) p) = 0 := by
  have hcancel := canonical_heightSquared_pairing (tensorGradient vertical T)
    (quotientPlanarRepresentative N (u : QuotientL2 N)) (by
      intro p hp
      simp [quotientPlanarRepresentative,chartPullback,hp])
  rw [← hcancel]
  calc
    _ = ∫ z : UpperHalfPlane, star (testDerivative vertical T z) *
        (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simp only [heightSquaredLift,quotientPlanarRepresentative,chartPullback_at_upper,
          testDerivative]
        ring
    _ = 0 := native_kernel_global_weighted_tensor N u hu vertical T

end
end ImbalancedChen.Part3.GammaKernelPlanarWeakEquation20261026a
