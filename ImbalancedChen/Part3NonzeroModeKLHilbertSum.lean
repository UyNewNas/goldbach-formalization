import ImbalancedChen.Part3NonzeroCircleFourierUnitary
import ImbalancedChen.Part3ActualKLOntoUnitary

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The already-proved ACTUAL onto radial KL map assembles to an onto unitary
on the countable Hilbert sum indexed by nonzero integers. Both directions
are coordinatewise the actual native KL unitary, not unknown modal maps.
Membership in the two Hilbert sums is proved by the actual norm equality.
The target uses counting in n and EXACTLY the existing positive tauMeasure
with density (2/pi^2) tau sinh(pi tau). No automorphic measure is substituted.

This is the modal assembly, not yet the cylinder theorem: identifying an
arbitrary zero-horizontal-mean cylinder L2 function with this modal radial
Hilbert sum still requires the actual cylinder Fourier/Fubini equivalence
and the separate mode-dependent Liouville unitary. Neither is assumed or
claimed here. No boundary operator or Gamma quotient is covered.
-/

namespace ImbalancedChen.Part3.NonzeroModeKLHilbertSum20261026a

noncomputable section
open MeasureTheory
open NonzeroCircleFourierUnitary20261026a
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a

abbrev NonzeroRadialModes := lp (fun _ : NonzeroMode => RadialL2) 2
abbrev NonzeroSpectralModes := lp (fun _ : NonzeroMode => RawTauL2) 2

private def forward (f : NonzeroRadialModes) : NonzeroSpectralModes :=
  ⟨fun n => actualKLUnitary (f n),
    (lp.memℓp f).mono' (fun n => (actualKLUnitary.norm_map (f n)).le)⟩

private def inverse (a : NonzeroSpectralModes) : NonzeroRadialModes :=
  ⟨fun n => actualKLUnitary.symm (a n),
    (lp.memℓp a).mono' (fun n => (actualKLUnitary.symm.norm_map (a n)).le)⟩

/-- Genuine onto assembly on the complete countable Hilbert sums. -/
def nonzeroModeKL : NonzeroRadialModes ≃ₗᵢ[ℂ] NonzeroSpectralModes where
  toFun := forward
  invFun := inverse
  left_inv f := by
    ext n
    exact actualKLUnitary.symm_apply_apply (f n)
  right_inv a := by
    ext n
    exact actualKLUnitary.apply_symm_apply (a n)
  map_add' f g := by
    ext n
    exact actualKLUnitary.map_add (f n) (g n)
  map_smul' c f := by
    ext n
    exact actualKLUnitary.map_smul c (f n)
  norm_map' f := by
    apply le_antisymm
    · exact lp.norm_mono (by norm_num)
        (fun n => (actualKLUnitary.norm_map (f n)).le)
    · exact lp.norm_mono (by norm_num)
        (fun n => (actualKLUnitary.norm_map (f n)).ge)

theorem nonzeroModeKL_apply (f : NonzeroRadialModes) (n : NonzeroMode) :
    nonzeroModeKL f n = actualKLUnitary (f n) := rfl

theorem nonzeroModeKL_symm_apply (a : NonzeroSpectralModes) (n : NonzeroMode) :
    nonzeroModeKL.symm a n = actualKLUnitary.symm (a n) := rfl

theorem nonzeroModeKL_surjective : Function.Surjective nonzeroModeKL :=
  nonzeroModeKL.surjective

theorem nonzeroModeKL_inverse_reconstruction (a : NonzeroSpectralModes) :
    nonzeroModeKL (nonzeroModeKL.symm a) = a :=
  nonzeroModeKL.apply_symm_apply a

/-- No normalization is lost in countable assembly: the energy sum in
the existing raw tau L2 spaces equals the full modal physical energy. -/
theorem nonzeroModeKL_hasSum_energy (f : NonzeroRadialModes) :
    HasSum (fun n : NonzeroMode => ‖nonzeroModeKL f n‖ ^ 2) ‖f‖ ^ 2 := by
  have h : HasSum (fun n : NonzeroMode => ‖nonzeroModeKL f n‖ ^ 2)
      ‖nonzeroModeKL f‖ ^ 2 := by
    apply_mod_cast lp.hasSum_norm (by norm_num) (nonzeroModeKL f)
  simpa only [nonzeroModeKL.norm_map] using h

theorem nonzeroModeKL_tsum_energy (f : NonzeroRadialModes) :
    (∑' n : NonzeroMode, ‖nonzeroModeKL f n‖ ^ 2) =
      ∑' n : NonzeroMode, ‖f n‖ ^ 2 := by
  apply tsum_congr
  intro n
  rw [nonzeroModeKL_apply, actualKLUnitary.norm_map]

/-- Exact literal K integral on a compact smooth coordinate. The measure
is the SAME tauMeasure used in the independently proved KL onto theorem. -/
theorem nonzeroModeKL_compact_coordinate_ae (f : NonzeroRadialModes)
    (n : NonzeroMode) (T : RadialTest) (hT : f n = radialCoreL2 T) :
    (nonzeroModeKL f n : ℝ → ℂ) =ᵐ[tauMeasure]
      ActualKLCompactTestIntegrationByParts20261025a.actualKtransform T.function := by
  rw [nonzeroModeKL_apply, hT]
  exact actualKLUnitary_on_test_ae T

end
end ImbalancedChen.Part3.NonzeroModeKLHilbertSum20261026a
