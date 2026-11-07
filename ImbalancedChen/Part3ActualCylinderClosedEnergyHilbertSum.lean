import ImbalancedChen.Part3ActualCylinderFiniteEnergyCore
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

True graph-norm closure of the actual finite Fourier / compact-height
gradient core. Each one-mode physical closed domain embeds isometrically
in the literal three-coordinate cylinder L2. Compact core density in
each mode is proved by a closed-preimage argument. Orthogonality and
the actual definition of the global closure then give a native onto
Hilbert-sum equivalence; no domain-identification premise is used.

The realization here is on the whole cylinder, with no truncation or
boundary condition. No Gamma quotient spectral assertion is made.
-/

namespace ImbalancedChen.Part3.ActualCylinderClosedEnergyHilbertSum20261026b
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open RadialSchrodingerL2Form20261025a
open ActualCylinderModeEmbeddings20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)
open ActualCylinderFiniteEnergyCore20261026b

def ambientModeEnergyLinear (n : NonzeroMode) :
    PhysicalEnergyHilbert →ₗ[ℂ] CylinderEnergyHilbert where
  toFun d := WithLp.toLp 2 ![modeEmbedding n (d 0),
    modeEmbedding n (d 1), modeEmbedding n (horizontalPhase n • d 2)]
  map_add' d e := by ext j; fin_cases j <;> simp [map_add, smul_add]
  map_smul' c d := by ext j; fin_cases j <;> simp [map_smul, smul_comm]

theorem ambientModeEnergyLinear_inner (n : NonzeroMode)
    (d e : PhysicalEnergyHilbert) :
    inner ℂ (ambientModeEnergyLinear n d) (ambientModeEnergyLinear n e) = inner ℂ d e := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [ambientModeEnergyLinear, Fin.sum_univ_three, modeEmbedding_inner,
    if_pos rfl, one_mul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, horizontalPhase_unit, one_mul]

def ambientModeEnergyEmbedding (n : NonzeroMode) :
    PhysicalEnergyHilbert →ₗᵢ[ℂ] CylinderEnergyHilbert :=
  (ambientModeEnergyLinear n).isometryOfInner (ambientModeEnergyLinear_inner n)

theorem ambientModeEnergyEmbedding_on_domain (n : NonzeroMode) (d : ModeEnergy n) :
    ambientModeEnergyEmbedding n (d : PhysicalEnergyHilbert) = modeEnergyVector n d := rfl

def cylinderEnergyCoreSpan : Submodule ℂ CylinderEnergyHilbert :=
  Submodule.span ℂ (range (fun p : Σ n : NonzeroMode, RadialTest =>
    modeEnergyVector p.1 (modeCorePoint p.1 p.2)))

/-- Literal closure of (F, y*partial_y F, y*partial_x F) for finite nonzero
Fourier polynomials with compact smooth height profiles. The derivative
interpretation is supplied by the preceding finite-core module. -/
def cylinderClosedEnergyDomain : Submodule ℂ CylinderEnergyHilbert :=
  cylinderEnergyCoreSpan.topologicalClosure

instance : CompleteSpace cylinderClosedEnergyDomain := inferInstance

theorem cylinderCoreVector_mem (n : NonzeroMode) (T : RadialTest) :
    modeEnergyVector n (modeCorePoint n T) ∈ cylinderClosedEnergyDomain :=
  cylinderEnergyCoreSpan.le_topologicalClosure (Submodule.subset_span ⟨⟨n, T⟩, rfl⟩)

theorem finiteEnergyVector_mem (s : Finset NonzeroMode)
    (T : NonzeroMode → RadialTest) : finiteEnergyVector s T ∈ cylinderClosedEnergyDomain := by
  apply Submodule.sum_mem
  intro n hn
  exact cylinderCoreVector_mem n (T n)

/-- Every vector of the actual one-mode closed physical domain belongs
to the global closure. This is proved from actual compact-core closure,
using the continuous ambient embedding, and is not assumed. -/
theorem modeEnergyVector_mem (n : NonzeroMode) (d : ModeEnergy n) :
    modeEnergyVector n d ∈ cylinderClosedEnergyDomain := by
  have hle : physicalClosedEnergyDomain (frequencyScale n)
      (frequencyScale_pos n.property) ≤
      cylinderClosedEnergyDomain.comap (ambientModeEnergyEmbedding n).toLinearMap := by
    apply (physicalEnergyCoreSpan (frequencyScale n)
      (frequencyScale_pos n.property)).topologicalClosure_minimal
    · apply Submodule.span_le.2
      rintro _ ⟨T, rfl⟩
      exact cylinderCoreVector_mem n T
    · exact cylinderEnergyCoreSpan.isClosed_topologicalClosure.preimage
        (ambientModeEnergyEmbedding n).continuous
  exact hle d.property

def cylinderModeEnergy (n : NonzeroMode) : ModeEnergy n →ₗᵢ[ℂ] cylinderClosedEnergyDomain where
  toFun d := ⟨modeEnergyVector n d, modeEnergyVector_mem n d⟩
  map_add' d e := by
    apply Subtype.ext
    exact (ambientModeEnergyEmbedding n).map_add (d : PhysicalEnergyHilbert) e
  map_smul' c d := by
    apply Subtype.ext
    exact (ambientModeEnergyEmbedding n).map_smul c (d : PhysicalEnergyHilbert)
  norm_map' d := (ambientModeEnergyEmbedding n).norm_map (d : PhysicalEnergyHilbert)

theorem cylinderModeEnergy_orthogonal :
    OrthogonalFamily ℂ ModeEnergy cylinderModeEnergy := by
  intro n m hnm d e
  change inner ℂ (modeEnergyVector n d) (modeEnergyVector m e) = 0
  rw [modeEnergyVector_inner, if_neg hnm, zero_mul]

def cylinderModeEnergySpan : Submodule ℂ cylinderClosedEnergyDomain :=
  ⨆ n : NonzeroMode, (cylinderModeEnergy n).toLinearMap.range

theorem cylinderModeEnergySpan_orthogonal_eq_bot : cylinderModeEnergySpanᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro F hF
  apply Submodule.mem_bot.mpr
  apply Subtype.ext
  have hcore : cylinderEnergyCoreSpan ≤ (innerSL ℂ (F : CylinderEnergyHilbert)).ker := by
    apply Submodule.span_le.2
    rintro _ ⟨⟨n, T⟩, rfl⟩
    have hin : cylinderModeEnergy n (modeCorePoint n T) ∈ cylinderModeEnergySpan :=
      (le_iSup (fun m : NonzeroMode => (cylinderModeEnergy m).toLinearMap.range) n)
        ⟨modeCorePoint n T, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal hin hF
    exact inner_eq_zero_symm.mp h
  have hclosed : cylinderClosedEnergyDomain ≤ (innerSL ℂ (F : CylinderEnergyHilbert)).ker :=
    cylinderEnergyCoreSpan.topologicalClosure_minimal hcore
      (innerSL ℂ (F : CylinderEnergyHilbert)).isClosed_ker
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hclosed F.property)

theorem cylinderModeEnergySpan_dense : cylinderModeEnergySpan.topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    cylinderModeEnergySpan_orthogonal_eq_bot, Submodule.bot_orthogonal_eq_top]

/-- The actual global gradient closure is an onto Hilbert sum of the
actual physical closed mode domains, with their native graph norms. -/
theorem actualCylinderEnergy_isHilbertSum :
    IsHilbertSum ℂ ModeEnergy cylinderModeEnergy :=
  IsHilbertSum.mk cylinderModeEnergy_orthogonal
    (by change ⊤ ≤ cylinderModeEnergySpan.topologicalClosure; rw [cylinderModeEnergySpan_dense])

abbrev PhysicalClosedModeSum := lp ModeEnergy 2

def actualCylinderEnergyFourier :
    cylinderClosedEnergyDomain ≃ₗᵢ[ℂ] PhysicalClosedModeSum :=
  actualCylinderEnergy_isHilbertSum.linearIsometryEquiv

theorem actualCylinderEnergyFourier_inverse_single (n : NonzeroMode) (d : ModeEnergy n) :
    actualCylinderEnergyFourier.symm (lp.single 2 n d) = cylinderModeEnergy n d :=
  actualCylinderEnergy_isHilbertSum.linearIsometryEquiv_symm_apply_single (i := n) d

theorem actualCylinderEnergyFourier_reconstruction (F : cylinderClosedEnergyDomain) :
    HasSum (fun n : NonzeroMode => cylinderModeEnergy n (actualCylinderEnergyFourier F n)) F := by
  simpa only [actualCylinderEnergyFourier.symm_apply_apply] using
    actualCylinderEnergy_isHilbertSum.hasSum_linearIsometryEquiv_symm
      (actualCylinderEnergyFourier F)

theorem actualCylinderEnergyFourier_reconstruction_ambient (F : cylinderClosedEnergyDomain) :
    HasSum (fun n : NonzeroMode => modeEnergyVector n (actualCylinderEnergyFourier F n))
      (F : CylinderEnergyHilbert) :=
  cylinderClosedEnergyDomain.subtypeL.hasSum (actualCylinderEnergyFourier_reconstruction F)

theorem actualCylinderEnergyFourier_hasSum_graph_pairing
    (F G : cylinderClosedEnergyDomain) :
    HasSum (fun n : NonzeroMode =>
      inner ℂ (actualCylinderEnergyFourier F n) (actualCylinderEnergyFourier G n))
      (inner ℂ F G) := by
  simpa only [actualCylinderEnergyFourier.inner_map_map] using
    lp.hasSum_inner (actualCylinderEnergyFourier F) (actualCylinderEnergyFourier G)

end
end ImbalancedChen.Part3.ActualCylinderClosedEnergyHilbertSum20261026b
