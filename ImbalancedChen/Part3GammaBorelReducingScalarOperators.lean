import ImbalancedChen.Part3GammaPhysicalSpectralSectorReduction
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

For the actual Gamma0 scalar Laplace measure, a physically proved Borel
reducing subspace has exact scalar-measure splitting against its actual
orthogonal complement. Complex polarization then shows that any genuine
native operator represented by those diagonal scalar integrals preserves
the subspace and its orthogonal complement and commutes with its actual
orthogonal projection. The downstream native heat/resolvent identities
are already independent proved suppliers, not new spectral assumptions.
-/
namespace ImbalancedChen.Part3.GammaBorelReducingScalarOperators20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualConstantMode20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open GammaMeanCenteredScalarMeasure20261026b
open GammaPhysicalSpectralSectorReduction20261026b

/-- Exact scalar splitting for an actual Borel-invariant sector and its
orthogonal complement. Borel invariance is instantiated from the proved
physical generated sectors in the downstream module. -/
theorem actualLaplaceMeasure_reducing_linear_combination (N : ℕ) [NeZero N]
    (K : Submodule ℂ (QuotientL2 N))
    (hK : ∀ (B : Set ℝ) (hB : MeasurableSet B) (v : QuotientL2 N),
      v ∈ K → actualLaplaceBorelProjection N B hB v ∈ K)
    {f g : QuotientL2 N} (hf : f ∈ K) (hg : g ∈ Kᗮ) (a b : ℂ) :
    actualLaplaceMeasure N (a • f + b • g) =
      ENNReal.ofReal (‖a‖ ^ 2) • actualLaplaceMeasure N f +
        ENNReal.ofReal (‖b‖ ^ 2) • actualLaplaceMeasure N g := by
  apply Measure.ext
  intro B hB
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  rw [actualLaplaceMeasure_eq_borel_projection_norm_sq N _ B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N f B hB,
    actualLaplaceMeasure_eq_borel_projection_norm_sq N g B hB,
    map_add, map_smul, map_smul]
  have hfg : inner ℂ (actualLaplaceBorelProjection N B hB f)
      (actualLaplaceBorelProjection N B hB g) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (hK B hB f hf)
      (actual_borel_orthogonal_invariant N K B hB (fun v hv => hK B hB v hv) hg)
  have hc : inner ℂ (a • actualLaplaceBorelProjection N B hB f)
      (b • actualLaplaceBorelProjection N B hB g) = 0 := by
    rw [inner_smul_left, inner_smul_right, hfg, mul_zero, mul_zero]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hc,
    norm_smul, norm_smul, mul_pow, mul_pow,
    ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _)]

/-- Equal actual scalar measures give equal native diagonal coefficients
for an operator with an independently proved scalar integral formula. -/
theorem diagonal_eq_of_actualLaplaceMeasure_eq (N : ℕ) [NeZero N]
    (T : QuotientL2 N →L[ℂ] QuotientL2 N) (k : ℝ → ℂ)
    (hdiag : ∀ v : QuotientL2 N, (∫ λ, k λ ∂actualLaplaceMeasure N v) = inner ℂ v (T v))
    {u v : QuotientL2 N} (huv : actualLaplaceMeasure N u = actualLaplaceMeasure N v) :
    inner ℂ (T u) u = inner ℂ (T v) v := by
  have hi : inner ℂ u (T u) = inner ℂ v (T v) := by
    rw [← hdiag u, ← hdiag v, huv]
  simpa only [inner_conj_symm] using congrArg star hi

/-- The mixed native operator coefficient is zero because the four
polarization diagonals have exactly the same actual scalar measure. -/
theorem actual_scalar_integral_operator_cross_zero (N : ℕ) [NeZero N]
    (K : Submodule ℂ (QuotientL2 N))
    (hK : ∀ (B : Set ℝ) (hB : MeasurableSet B) (v : QuotientL2 N),
      v ∈ K → actualLaplaceBorelProjection N B hB v ∈ K)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N) (k : ℝ → ℂ)
    (hdiag : ∀ v : QuotientL2 N, (∫ λ, k λ ∂actualLaplaceMeasure N v) = inner ℂ v (T v))
    {f g : QuotientL2 N} (hf : f ∈ K) (hg : g ∈ Kᗮ) :
    inner ℂ (T f) g = 0 := by
  have hplus : actualLaplaceMeasure N (f + g) =
      actualLaplaceMeasure N f + actualLaplaceMeasure N g := by
    simpa using actualLaplaceMeasure_reducing_linear_combination N K hK hf hg (1 : ℂ) 1
  have hminus : actualLaplaceMeasure N (f - g) =
      actualLaplaceMeasure N f + actualLaplaceMeasure N g := by
    simpa [sub_eq_add_neg] using
      actualLaplaceMeasure_reducing_linear_combination N K hK hf hg (1 : ℂ) (-1)
  have hplusI : actualLaplaceMeasure N (f + Complex.I • g) =
      actualLaplaceMeasure N f + actualLaplaceMeasure N g := by
    simpa using actualLaplaceMeasure_reducing_linear_combination N K hK hf hg (1 : ℂ) Complex.I
  have hminusI : actualLaplaceMeasure N (f - Complex.I • g) =
      actualLaplaceMeasure N f + actualLaplaceMeasure N g := by
    simpa [sub_eq_add_neg] using
      actualLaplaceMeasure_reducing_linear_combination N K hK hf hg (1 : ℂ) (-Complex.I)
  have hm := diagonal_eq_of_actualLaplaceMeasure_eq N T k hdiag (hminus.trans hplus.symm)
  have hpI := diagonal_eq_of_actualLaplaceMeasure_eq N T k hdiag (hplusI.trans hplus.symm)
  have hmI := diagonal_eq_of_actualLaplaceMeasure_eq N T k hdiag (hminusI.trans hplus.symm)
  rw [inner_map_polarization' T.toLinearMap f g]
  change (inner ℂ (T (f + g)) (f + g) - inner ℂ (T (f - g)) (f - g) -
    Complex.I * inner ℂ (T (f + Complex.I • g)) (f + Complex.I • g) +
    Complex.I * inner ℂ (T (f - Complex.I • g)) (f - Complex.I • g)) / 4 = 0
  rw [hm, hpI, hmI]
  ring

/-- Actual native operator invariance follows from the proved Borel
invariance and genuine diagonal integral identity, without CFC approximation. -/
theorem actual_scalar_integral_operator_invariant (N : ℕ) [NeZero N]
    (K : Submodule ℂ (QuotientL2 N)) (hclosed : IsClosed (K : Set (QuotientL2 N)))
    (hK : ∀ (B : Set ℝ) (hB : MeasurableSet B) (v : QuotientL2 N),
      v ∈ K → actualLaplaceBorelProjection N B hB v ∈ K)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N) (k : ℝ → ℂ)
    (hdiag : ∀ v : QuotientL2 N, (∫ λ, k λ ∂actualLaplaceMeasure N v) = inner ℂ v (T v))
    {f : QuotientL2 N} (hf : f ∈ K) : T f ∈ K := by
  letI : CompleteSpace K := hclosed.completeSpace_coe
  have hmem : T f ∈ Kᗮᗮ := by
    intro g hg
    rw [inner_eq_zero_symm]
    exact actual_scalar_integral_operator_cross_zero N K hK T k hdiag hf hg
  simpa only [K.orthogonal_orthogonal] using hmem

/-- Both native operator blocks are invariant, so the actual orthogonal
projection commutes with the operator on every physical quotient vector. -/
theorem actual_scalar_integral_operator_projection_commute (N : ℕ) [NeZero N]
    (K : Submodule ℂ (QuotientL2 N)) [CompleteSpace K]
    (hclosed : IsClosed (K : Set (QuotientL2 N)))
    (hK : ∀ (B : Set ℝ) (hB : MeasurableSet B) (v : QuotientL2 N),
      v ∈ K → actualLaplaceBorelProjection N B hB v ∈ K)
    (T : QuotientL2 N →L[ℂ] QuotientL2 N) (k : ℝ → ℂ)
    (hdiag : ∀ v : QuotientL2 N, (∫ λ, k λ ∂actualLaplaceMeasure N v) = inner ℂ v (T v))
    (f : QuotientL2 N) : K.starProjection (T f) = T (K.starProjection f) := by
  apply K.eq_starProjection_of_mem_orthogonal
  · exact actual_scalar_integral_operator_invariant N K hclosed hK T k hdiag
      (K.starProjection_apply_mem f)
  · rw [← map_sub]
    exact actual_scalar_integral_operator_invariant N Kᗮ (Submodule.isClosed_orthogonal K)
      (fun B hB v hv => actual_borel_orthogonal_invariant N K B hB
        (fun w hw => hK B hB w hw) hv) T k hdiag (K.sub_starProjection_mem_orthogonal f)

end
end ImbalancedChen.Part3.GammaBorelReducingScalarOperators20261026b
