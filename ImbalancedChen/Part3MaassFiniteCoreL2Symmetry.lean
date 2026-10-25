import ImbalancedChen.Part3MaassFiniteCoreL2Graph

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual hyperbolic L² graph pairing agrees with the established compact
tensor Green form. Consequently the actual graph is symmetric and nonnegative.
The shifted graph has the Hilbert-space coercivity inequality. These are
properties of the actual finite test graph, without a density, closure or
self-adjointness premise. No spectral theorem is asserted.
-/

namespace ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a

/-- The actual Hilbert-space graph pairing is the canonical integral of
the actual finite function against the actual coordinate Laplacian. The
representatives in `Lp` are handled by their proved a.e. identities. -/
theorem finiteCoreL2_inner_Laplacian_eq_canonical_integral {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (finiteCoreL2 s T) (finiteCoreLaplacianL2 t U) =
      ∫ z : UpperHalfPlane,
        star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hf := (finiteCoreFunction_memLp s T).coeFn_toLp
  have hg := (finiteCoreLaplacian_memLp t U).coeFn_toLp
  change (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
    inner ℂ (((finiteCoreFunction_memLp s T).toLp (finiteCoreFunction s T)) z)
      (((finiteCoreLaplacian_memLp t U).toLp (finiteCoreLaplacian t U)) z) =
      star (finiteCoreFunction s T z) * finiteCoreLaplacian t U z)
  filter_upwards [hf, hg] with z hzF hzL
  rw [hzF, hzL]
  simp only [RCLike.inner_apply', Complex.star_def]

/-- True compact Green identity expressed in the actual canonical L²
inner product, retaining all finite tensor cross terms. -/
theorem finiteCoreL2_inner_Laplacian_eq_energy {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (finiteCoreL2 s T) (finiteCoreLaplacianL2 t U) =
      finiteCoreEnergy s T t U := by
  rw [finiteCoreL2_inner_Laplacian_eq_canonical_integral]
  exact canonical_weakMaass_on_finite_tensor_span s T t U

theorem finiteCoreL2_inner_Laplacian_hermitian {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (finiteCoreL2 s T) (finiteCoreLaplacianL2 t U) =
      star (inner ℂ (finiteCoreL2 t U) (finiteCoreLaplacianL2 s T)) := by
  rw [finiteCoreL2_inner_Laplacian_eq_energy,
    finiteCoreL2_inner_Laplacian_eq_energy]
  exact finiteCoreEnergy_hermitian s T t U

/-- Symmetry of the actual L² Maass graph on its finite tensor inputs. -/
theorem finiteCoreL2_Laplacian_symmetric {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor)
    (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (finiteCoreLaplacianL2 s T) (finiteCoreL2 t U) =
      inner ℂ (finiteCoreL2 s T) (finiteCoreLaplacianL2 t U) := by
  calc
    _ = star (inner ℂ (finiteCoreL2 t U) (finiteCoreLaplacianL2 s T)) := by
      simpa only [Complex.star_def] using
        (inner_conj_symm (𝕜 := ℂ) (finiteCoreLaplacianL2 s T) (finiteCoreL2 t U)).symm
    _ = _ := (finiteCoreL2_inner_Laplacian_hermitian s T t U).symm

theorem finiteCoreL2_Laplacian_nonneg {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    0 ≤ (inner ℂ (finiteCoreL2 s T) (finiteCoreLaplacianL2 s T)).re := by
  rw [finiteCoreL2_inner_Laplacian_eq_energy]
  exact finiteCoreEnergy_nonneg s T

/-- The shifted actual graph controls the squared canonical L² norm. -/
theorem finiteCoreL2_shifted_coercive {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ‖finiteCoreL2 s T‖ ^ 2 ≤
      (inner ℂ (finiteCoreL2 s T)
        (finiteCoreL2 s T + finiteCoreLaplacianL2 s T)).re := by
  have hself : (inner ℂ (finiteCoreL2 s T) (finiteCoreL2 s T)).re =
      ‖finiteCoreL2 s T‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [inner_add_right, Complex.add_re]
  rw [hself]
  exact le_add_of_nonneg_right (finiteCoreL2_Laplacian_nonneg s T)

/-- Symmetry as a statement about the actual graph relation, independent
of the choice of finite tensor presentation for either pair. -/
theorem finiteTensorL2Graph_symmetric {f g u v : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph)
    (huv : (u, v) ∈ finiteTensorL2Graph) :
    inner ℂ g u = inner ℂ f v := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rcases huv with ⟨m, U, hu, hv⟩
  rw [hf, hg, hu, hv]
  exact finiteCoreL2_Laplacian_symmetric Finset.univ T Finset.univ U

theorem finiteTensorL2Graph_nonneg {f g : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph) : 0 ≤ (inner ℂ f g).re := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rw [hf, hg]
  exact finiteCoreL2_Laplacian_nonneg Finset.univ T

theorem finiteTensorL2Graph_shifted_coercive {f g : HyperbolicL2}
    (hfg : (f, g) ∈ finiteTensorL2Graph) :
    ‖f‖ ^ 2 ≤ (inner ℂ f (f + g)).re := by
  rcases hfg with ⟨n, T, hf, hg⟩
  rw [hf, hg]
  exact finiteCoreL2_shifted_coercive Finset.univ T

end

end ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a
