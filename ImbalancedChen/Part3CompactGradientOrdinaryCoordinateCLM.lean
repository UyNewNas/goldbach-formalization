import ImbalancedChen.Part3GammaGraphStrongLocalH1
import ImbalancedChen.Part3GammaCompletedGradientClassicalRepresentative
import ImbalancedChen.Part3CanonicalMaassTensorDensity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A native compact canonical vector L2 field has an ordinary coordinate
component by projection, zero extension and the ACTUAL planar unitary.
All three operations are complex linear; the resulting map is a
contraction, with its literal divide-by-height representative proved.
No operator output, Poisson equation or derivative premise occurs. -/

namespace ImbalancedChen.Part3.CompactGradientOrdinaryCoordinateCLM20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactCoreGradient20261025a
open Gamma0CompactQuotientPullbackLinear20261025a Gamma0EnergyGeometricWeakGradient20261025a
open CanonicalPlanarL2UnitarySourceOnly CanonicalMaassTensorDensity20261025a
open PlanarLocalWeakGradientExtraction20261026b

def zeroExtension {K : Set UpperHalfPlane} (hK : MeasurableSet K) (f : LocalScalarL2 K) : HyperbolicL2 :=
  ((memLp_indicator_iff_restrict hK).2 f.memLp).toLp (K.indicator f)

def zeroExtensionLinear {K : Set UpperHalfPlane} (hK : MeasurableSet K) :
    LocalScalarL2 K →ₗ[ℂ] HyperbolicL2 where
  toFun := zeroExtension hK
  map_add' f g := by
    have hsum := (ae_restrict_iff' hK).1 (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hK).2 (f+g).memLp).coeFn_toLp,
      ((memLp_indicator_iff_restrict hK).2 f.memLp).coeFn_toLp,
      ((memLp_indicator_iff_restrict hK).2 g.memLp).coeFn_toLp,
      Lp.coeFn_add (zeroExtension hK f) (zeroExtension hK g),hsum]
      with z hfg hf hg ho hs
    rw [hfg,ho,hf,hg]
    by_cases hz : z∈K <;> simp [hz,hs]
  map_smul' c f := by
    have hsmul := (ae_restrict_iff' hK).1 (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hK).2 (c • f).memLp).coeFn_toLp,
      ((memLp_indicator_iff_restrict hK).2 f.memLp).coeFn_toLp,
      Lp.coeFn_smul c (zeroExtension hK f),hsmul] with z hcf hf ho hs
    rw [hcf,ho,hf]
    by_cases hz : z∈K <;> simp [hz,hs]

theorem zeroExtension_norm (K : Set UpperHalfPlane) (hK : MeasurableSet K) (f : LocalScalarL2 K) :
    ‖zeroExtensionLinear hK f‖=‖f‖ := by
  change ‖((memLp_indicator_iff_restrict hK).2 f.memLp).toLp (K.indicator f)‖=‖f‖
  rw [Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hK,Lp.norm_def]

def zeroExtensionCLM {K : Set UpperHalfPlane} (hK : MeasurableSet K) : LocalScalarL2 K →L[ℂ] HyperbolicL2 :=
  (zeroExtensionLinear hK).mkContinuous 1 (fun f => by simpa only [one_mul,zeroExtension_norm] using (le_refl ‖f‖))

theorem zeroExtension_coe_ae {K : Set UpperHalfPlane} (hK : MeasurableSet K) (f : LocalScalarL2 K) :
    (zeroExtensionCLM hK f : UpperHalfPlane → ℂ)=ᵐ[volume] K.indicator f :=
  ((memLp_indicator_iff_restrict hK).2 f.memLp).coeFn_toLp

def componentCLM (K : Set UpperHalfPlane) (i : Fin 2) :
    CompactGradientL2 K →L[ℂ] LocalScalarL2 K :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 ((volume : Measure UpperHalfPlane).restrict K)

theorem componentCLM_norm_le (K : Set UpperHalfPlane) (i : Fin 2) (g : CompactGradientL2 K) :
    ‖componentCLM K i g‖≤‖g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL g] with z hz
  rw [hz]
  exact PiLp.norm_apply_le (g z) i

def compactGradientToPlane (K : Set UpperHalfPlane) (hK : MeasurableSet K) (vertical : Bool) :
    CompactGradientL2 K →L[ℂ] PlaneL2 :=
  canonicalToPlane.toContinuousLinearMap.comp ((zeroExtensionCLM hK).comp
    (componentCLM K (firstCoordinate vertical)))

theorem compactGradientToPlane_norm_le (K : Set UpperHalfPlane) (hK : MeasurableSet K)
    (vertical : Bool) (g : CompactGradientL2 K) :
    ‖compactGradientToPlane K hK vertical g‖≤‖g‖ := by
  change ‖canonicalToPlane (zeroExtensionCLM hK (componentCLM K (firstCoordinate vertical) g))‖≤‖g‖
  rw [canonicalToPlane.norm_map,zeroExtension_norm]
  exact componentCLM_norm_le K _ g

theorem compactGradientToPlane_coe_ae (K : Set UpperHalfPlane) (hK : MeasurableSet K)
    (vertical : Bool) (g : CompactGradientL2 K) :
    (compactGradientToPlane K hK vertical g : ℝ×ℝ → ℂ)=ᵐ[volume]
      forwardFunction (K.indicator (fun z => g z (firstCoordinate vertical))) := by
  let q := componentCLM K (firstCoordinate vertical) g
  have hq := (ae_restrict_iff' hK).1
    ((EuclideanSpace.proj (𝕜 := ℂ) (firstCoordinate vertical)).coeFn_compLpL g)
  have he : (zeroExtensionCLM hK q : UpperHalfPlane → ℂ)=ᵐ[volume]
      K.indicator (fun z => g z (firstCoordinate vertical)) := by
    filter_upwards [zeroExtension_coe_ae hK q,hq] with z hz hlocal
    rw [hz]
    by_cases hzin : z∈K
    · rw [Set.indicator_of_mem hzin,Set.indicator_of_mem hzin]
      exact hlocal hzin
    · rw [Set.indicator_of_notMem hzin,Set.indicator_of_notMem hzin]
  exact (forwardL2_coe_ae (zeroExtensionCLM hK q)).trans (forwardFunction_congr_ae he)

end
end ImbalancedChen.Part3.CompactGradientOrdinaryCoordinateCLM20261026b
