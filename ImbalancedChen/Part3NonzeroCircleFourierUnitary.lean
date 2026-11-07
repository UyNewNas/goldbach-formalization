import ImbalancedChen.Part3CuspZeroModeProjection

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The actual normalized-Haar circle Fourier basis, restricted to nonzero
integer modes, is a complete Hilbert basis of the existing zero-mean
subspace. This proves onto and reconstruction, not just Parseval for an
already-given function. No unknown basis or coefficient-surjectivity
premise is introduced. The circle has period one and Haar mass one.

This is the transverse Hilbert-space component of the whole-cylinder
construction. It does not identify the full cylinder with an iterated L2
space, impose a boundary condition on a truncated cusp, or provide a
Gamma-quotient spectral expansion.
-/

namespace ImbalancedChen.Part3.NonzeroCircleFourierUnitary20261026a

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
open P3CuspZeroModeProjectionSourceOnly

abbrev NonzeroMode := {n : ℤ // n ≠ 0}
abbrev ZeroMeanCircle := zeroModeSubspace

local instance : CompleteSpace ZeroMeanCircle :=
  zeroModeSubspace_closed.completeSpace_coe

def circleBasis : HilbertBasis ℤ ℂ CircleL2 :=
  AddCircle.fourierBasis (T := (1 : ℝ))

private theorem circleBasis_nonzero_mem (n : NonzeroMode) :
    circleBasis (n : ℤ) ∈ zeroModeSubspace := by
  rw [zeroModeSubspace_iff, ← AddCircle.fourierBasis_repr]
  change circleBasis.repr (circleBasis (n : ℤ)) 0 = 0
  rw [circleBasis.repr_self]
  simp [lp.single_apply, Pi.single_apply, n.property, Ne.symm n.property]

/-- The actual nonconstant Fourier monomials, inside the genuine
orthogonal complement of the constant mode. -/
def nonzeroFourierVector (n : NonzeroMode) : ZeroMeanCircle :=
  ⟨circleBasis n, circleBasis_nonzero_mem n⟩

theorem nonzeroFourierVector_orthonormal :
    Orthonormal ℂ nonzeroFourierVector := by
  apply (zeroModeSubspace.subtypeₗᵢ.orthonormal_comp_iff).mp
  exact circleBasis.orthonormal.comp Subtype.val Subtype.val_injective

/-- Completeness is proved using the actual all-integer Fourier unitary:
orthogonality kills every nonzero coordinate, and subspace membership
kills coordinate zero. -/
theorem nonzeroFourierVector_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range nonzeroFourierVector))ᗮ = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  apply Submodule.mem_bot.mpr
  apply Subtype.ext
  apply circleBasis.repr.injective
  ext n
  change circleBasis.repr (f : CircleL2) n = circleBasis.repr (0 : CircleL2) n
  rw [map_zero]
  change circleBasis.repr (f : CircleL2) n = 0
  by_cases hn : n = 0
  · subst n
    exact (AddCircle.fourierBasis_repr (f : CircleL2) 0).trans
      ((zeroModeSubspace_iff (f : CircleL2)).mp f.property)
  · have hinner : inner ℂ (nonzeroFourierVector ⟨n, hn⟩) f = 0 :=
      Submodule.inner_right_of_mem_orthogonal
        (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩) hf
    rw [circleBasis.repr_apply_apply]
    exact hinner

def nonzeroFourierBasis : HilbertBasis NonzeroMode ℂ ZeroMeanCircle :=
  HilbertBasis.mkOfOrthogonalEqBot nonzeroFourierVector_orthonormal
    nonzeroFourierVector_orthogonal_eq_bot

theorem nonzeroFourierBasis_apply (n : NonzeroMode) :
    nonzeroFourierBasis n = nonzeroFourierVector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    nonzeroFourierVector_orthonormal nonzeroFourierVector_orthogonal_eq_bot) n

/-- Onto nonzero-coordinate Fourier transform on the zero-mean circle. -/
def nonzeroCircleFourier : ZeroMeanCircle ≃ₗᵢ[ℂ] ℓ²(NonzeroMode, ℂ) :=
  nonzeroFourierBasis.repr

theorem nonzeroCircleFourier_apply (f : ZeroMeanCircle) (n : NonzeroMode) :
    nonzeroCircleFourier f n = AddCircle.fourierCoeff (f : CircleL2) (n : ℤ) := by
  change nonzeroFourierBasis.repr f n = _
  rw [nonzeroFourierBasis.repr_apply_apply, nonzeroFourierBasis_apply]
  change inner ℂ (circleBasis (n : ℤ)) (f : CircleL2) = _
  rw [← circleBasis.repr_apply_apply]
  exact AddCircle.fourierBasis_repr (f : CircleL2) (n : ℤ)

theorem nonzeroCircleFourier_surjective : Function.Surjective nonzeroCircleFourier :=
  nonzeroCircleFourier.surjective

/-- Every square-summable sequence of nonzero coefficients is realized,
and its inverse has zero constant coefficient by actual subspace membership. -/
theorem inverse_coefficients (a : ℓ²(NonzeroMode, ℂ)) (n : NonzeroMode) :
    AddCircle.fourierCoeff (nonzeroCircleFourier.symm a : CircleL2) (n : ℤ) = a n := by
  rw [← nonzeroCircleFourier_apply, nonzeroCircleFourier.apply_symm_apply]

theorem inverse_mean_zero (a : ℓ²(NonzeroMode, ℂ)) :
    (∫ x, (nonzeroCircleFourier.symm a : CircleL2) x
      ∂(AddCircle.haarAddCircle (T := (1 : ℝ)))) = 0 := by
  have hz := (zeroModeSubspace_iff
    (nonzeroCircleFourier.symm a : CircleL2)).mp (nonzeroCircleFourier.symm a).property
  simpa [AddCircle.fourierCoeff] using hz

/-- Native L2 reconstruction over precisely the nonzero integers. -/
theorem inverse_hasSum (a : ℓ²(NonzeroMode, ℂ)) :
    HasSum (fun n : NonzeroMode => a n • (circleBasis (n : ℤ)))
      (nonzeroCircleFourier.symm a : CircleL2) := by
  have h := zeroModeSubspace.subtypeL.hasSum (nonzeroFourierBasis.hasSum_repr_symm a)
  simpa only [nonzeroCircleFourier, nonzeroFourierBasis_apply,
    nonzeroFourierVector, Submodule.subtypeL_apply, Submodule.coe_smul] using h

/-- Energy is in the native Hilbert norm; no width or 2*pi factor occurs
because the existing period-one circle uses normalized Haar mass one. -/
theorem nonzeroCircleFourier_hasSum_energy (f : ZeroMeanCircle) :
    HasSum (fun n : NonzeroMode =>
      ‖AddCircle.fourierCoeff (f : CircleL2) (n : ℤ)‖ ^ 2) ‖f‖ ^ 2 := by
  have h : HasSum (fun n : NonzeroMode => ‖nonzeroCircleFourier f n‖ ^ 2)
      (‖nonzeroCircleFourier f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm (by norm_num) (nonzeroCircleFourier f)
  simpa only [nonzeroCircleFourier_apply, nonzeroCircleFourier.norm_map] using h

/-- The pre-existing orthogonal projector is exactly analyzed by this
unitary; it retains every original nonzero literal Fourier coefficient. -/
theorem projected_coefficient (f : CircleL2) (n : NonzeroMode) :
    nonzeroCircleFourier ⟨projectZero f, projectZero_mem f⟩ n =
      AddCircle.fourierCoeff f (n : ℤ) := by
  rw [nonzeroCircleFourier_apply]
  exact projectZero_coefficient_ne_zero f n n.property

end
end ImbalancedChen.Part3.NonzeroCircleFourierUnitary20261026a
