import ImbalancedChen.Part3ActualCylinderFourierCoefficients
import ImbalancedChen.Part3NonzeroCircleFourierUnitary

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The actual zero-horizontal-mean subspace of canonical cylinder L2 is the
Hilbert sum of the actual nonzero mode embeddings. Completeness follows
from the genuine slice-coefficient separation theorem, not from a target
Plancherel or onto hypothesis. The resulting native unitary has precisely
the literal slice Fourier integrals as its height-L2 coordinates.

This is the entire cylinder with dy/y^2 and unit Haar circle. No truncated
cusp boundary realization or Gamma quotient spectrum is identified.
-/

namespace ImbalancedChen.Part3.ActualZeroMeanCylinderFourierUnitary20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)

def zeroMeanCylinder : Submodule ℂ CylinderL2 := (cylinderCoefficient 0).ker

theorem zeroMeanCylinder_closed : IsClosed (zeroMeanCylinder : Set CylinderL2) :=
  (cylinderCoefficient 0).isClosed_ker

instance : CompleteSpace zeroMeanCylinder := zeroMeanCylinder_closed.completeSpace_coe

/-- This native closed subspace is exactly zero horizontal mean at
almost every height, with no pointwise representative assumption. -/
theorem mem_zeroMeanCylinder_iff (F : CylinderL2) :
    F ∈ zeroMeanCylinder ↔ ∀ᵐ y ∂heightMeasure,
      (∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) = 0 := by
  change cylinderCoefficient 0 F = 0 ↔ _
  have hmean : (cylinderCoefficient 0 F : PositiveHeight → ℂ) =ᵐ[heightMeasure]
      (fun y => ∫ x : UnitAddCircle, F (x, y) ∂AddCircle.haarAddCircle) := by
    simpa [sliceCoefficient, AddCircle.fourierCoeff] using cylinderCoefficient_ae 0 F
  constructor
  · intro h
    rw [h] at hmean
    exact hmean.symm.trans (Lp.coeFn_zero ℂ 2 heightMeasure)
  · intro h
    apply Lp.ext
    exact (hmean.trans h).trans (Lp.coeFn_zero ℂ 2 heightMeasure).symm

def nonzeroCylinderMode (n : NonzeroMode) : HeightL2 →ₗᵢ[ℂ] zeroMeanCylinder where
  toFun g := ⟨modeEmbedding n g, by
    change cylinderCoefficient 0 (modeEmbedding n g) = 0
    rw [cylinderCoefficient_mode]
    simp [Ne.symm n.property]⟩
  map_add' g h := by
    apply Subtype.ext
    exact (modeEmbedding n).map_add g h
  map_smul' c g := by
    apply Subtype.ext
    exact (modeEmbedding n).map_smul c g
  norm_map' g := (modeEmbedding n).norm_map g

theorem nonzeroCylinderMode_coe (n : NonzeroMode) (g : HeightL2) :
    (nonzeroCylinderMode n g : CylinderL2) = modeEmbedding n g := rfl

theorem nonzeroCylinderMode_orthogonal :
    OrthogonalFamily ℂ (fun _ : NonzeroMode => HeightL2) nonzeroCylinderMode := by
  intro n m hnm g h
  change inner ℂ (modeEmbedding n g) (modeEmbedding m h) = 0
  exact modeEmbedding_orthogonal (Subtype.val_injective.ne hnm) g h

def nonzeroModeSpan : Submodule ℂ zeroMeanCylinder :=
  ⨆ n : NonzeroMode, (nonzeroCylinderMode n).toLinearMap.range

theorem nonzeroModeSpan_orthogonal_eq_bot : nonzeroModeSpanᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro F hF
  apply Submodule.mem_bot.mpr
  apply Subtype.ext
  apply eq_zero_of_all_coefficients_zero
  intro n
  by_cases hn : n = 0
  · subst n
    exact F.property
  · apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [cylinderCoefficient_inner]
    have hin : nonzeroCylinderMode ⟨n, hn⟩ (cylinderCoefficient n (F : CylinderL2))
        ∈ nonzeroModeSpan :=
      (le_iSup (fun m : NonzeroMode => (nonzeroCylinderMode m).toLinearMap.range)
        ⟨n, hn⟩) ⟨cylinderCoefficient n (F : CylinderL2), rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hin hF

/-- The closure is the ACTUAL zero-mean cylinder subspace, established by
actual Fourier coefficient uniqueness on almost every height slice. -/
theorem nonzeroModeSpan_dense : nonzeroModeSpan.topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    nonzeroModeSpan_orthogonal_eq_bot, Submodule.bot_orthogonal_eq_top]

theorem actualCylinder_isHilbertSum :
    IsHilbertSum ℂ (fun _ : NonzeroMode => HeightL2) nonzeroCylinderMode :=
  IsHilbertSum.mk nonzeroCylinderMode_orthogonal
    (by change ⊤ ≤ nonzeroModeSpan.topologicalClosure; rw [nonzeroModeSpan_dense])

abbrev NonzeroHeightModes := lp (fun _ : NonzeroMode => HeightL2) 2

def actualCylinderFourier : zeroMeanCylinder ≃ₗᵢ[ℂ] NonzeroHeightModes :=
  actualCylinder_isHilbertSum.linearIsometryEquiv

theorem actualCylinderFourier_inverse_single (n : NonzeroMode) (g : HeightL2) :
    actualCylinderFourier.symm (lp.single 2 n g) = nonzeroCylinderMode n g :=
  actualCylinder_isHilbertSum.linearIsometryEquiv_symm_apply_single (i := n) g

/-- Exact native coordinate formula, proved by the unitary inner-product
identity and the already identified actual mode adjoint. -/
theorem actualCylinderFourier_apply (F : zeroMeanCylinder) (n : NonzeroMode) :
    actualCylinderFourier F n = cylinderCoefficient n (F : CylinderL2) := by
  apply ext_inner_left ℂ
  intro g
  calc
    inner ℂ g (actualCylinderFourier F n) =
        inner ℂ (lp.single 2 n g) (actualCylinderFourier F) :=
      (lp.inner_single_left n g (actualCylinderFourier F)).symm
    _ = inner ℂ (actualCylinderFourier.symm (lp.single 2 n g)) F := by
      rw [← actualCylinderFourier.symm.inner_map_map,
        actualCylinderFourier.symm_apply_apply]
    _ = inner ℂ (nonzeroCylinderMode n g) F := by
      rw [actualCylinderFourier_inverse_single]
    _ = inner ℂ g (cylinderCoefficient n (F : CylinderL2)) :=
      (cylinderCoefficient_inner n g (F : CylinderL2)).symm

theorem actualCylinderFourier_apply_ae (F : zeroMeanCylinder) (n : NonzeroMode) :
    (actualCylinderFourier F n : PositiveHeight → ℂ) =ᵐ[heightMeasure]
      fun y => AddCircle.fourierCoeff (fun x : UnitAddCircle => (F : CylinderL2) (x, y))
        (n : ℤ) := by
  rw [actualCylinderFourier_apply]
  exact cylinderCoefficient_ae n (F : CylinderL2)

theorem actualCylinderFourier_surjective : Function.Surjective actualCylinderFourier :=
  actualCylinderFourier.surjective

theorem actualCylinderFourier_inverse_hasSum (a : NonzeroHeightModes) :
    HasSum (fun n : NonzeroMode => nonzeroCylinderMode n (a n))
      (actualCylinderFourier.symm a) :=
  actualCylinder_isHilbertSum.hasSum_linearIsometryEquiv_symm a

theorem actualCylinderFourier_inverse_hasSum_ambient (a : NonzeroHeightModes) :
    HasSum (fun n : NonzeroMode => modeEmbedding n (a n))
      (actualCylinderFourier.symm a : CylinderL2) := by
  exact zeroMeanCylinder.subtypeL.hasSum (actualCylinderFourier_inverse_hasSum a)

theorem actualCylinderFourier_hasSum_reconstruction (F : zeroMeanCylinder) :
    HasSum (fun n : NonzeroMode => modeEmbedding n (cylinderCoefficient n (F : CylinderL2)))
      (F : CylinderL2) := by
  simpa only [actualCylinderFourier_apply, actualCylinderFourier.symm_apply_apply] using
    actualCylinderFourier_inverse_hasSum_ambient (actualCylinderFourier F)

def ambientNonzeroModeSpan : Submodule ℂ CylinderL2 :=
  ⨆ n : NonzeroMode, (modeEmbedding (n : ℤ)).toLinearMap.range

/-- Equality in the ambient canonical cylinder L2, not merely a naming
convention for the span. The reverse inclusion uses actual convergent
Fourier reconstruction. -/
theorem ambientNonzeroModeSpan_closure_eq :
    ambientNonzeroModeSpan.topologicalClosure = zeroMeanCylinder := by
  apply le_antisymm
  · apply ambientNonzeroModeSpan.topologicalClosure_minimal ?_ zeroMeanCylinder_closed
    apply iSup_le
    intro n F hF
    obtain ⟨g, rfl⟩ := hF
    exact (nonzeroCylinderMode n g).property
  · intro F hF
    have hsum := actualCylinderFourier_hasSum_reconstruction ⟨F, hF⟩
    apply ambientNonzeroModeSpan.isClosed_topologicalClosure.mem_of_tendsto hsum
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro n hn
    apply ambientNonzeroModeSpan.le_topologicalClosure
    exact (le_iSup (fun m : NonzeroMode =>
      (modeEmbedding (m : ℤ)).toLinearMap.range) n)
      ⟨cylinderCoefficient n F, rfl⟩

/-- Parseval in the quotient Hilbert spaces, now accompanying an actual
onto reconstruction theorem rather than merely a slice energy identity. -/
theorem actualCylinderFourier_hasSum_energy (F : zeroMeanCylinder) :
    HasSum (fun n : NonzeroMode => ‖cylinderCoefficient n (F : CylinderL2)‖ ^ 2)
      ‖(F : CylinderL2)‖ ^ 2 := by
  have h : HasSum (fun n : NonzeroMode => ‖actualCylinderFourier F n‖ ^ 2)
      ‖actualCylinderFourier F‖ ^ 2 := by
    apply_mod_cast lp.hasSum_norm (by norm_num) (actualCylinderFourier F)
  simpa only [actualCylinderFourier_apply, actualCylinderFourier.norm_map] using h

end
end ImbalancedChen.Part3.ActualZeroMeanCylinderFourierUnitary20261026a
