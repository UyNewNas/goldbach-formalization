import ImbalancedChen.Part3SmoothTensorLaplacianRender
import ImbalancedChen.Part3Gamma0ActualSmoothQuotientCore
import ImbalancedChen.Part3ActualUpperMaassLinearity

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL smooth finite-tensor Gamma0 quotient L2 core is preserved by
the actual coordinate Maass differential. Its output is constructed from
the two explicitly rendered smooth compact tensors on each generator,
then from genuine finite-span induction. Faithfulness of the existing
actual continuous quotient representatives gives uniqueness and linearity.

No output-core membership, rendering equality, representative agreement,
or L2 differential target is an assumed supplier. This is an algebraic
core endomorphism; graph closure, essential self-adjointness and the final
spectral theorem remain separate obligations.
-/

namespace ImbalancedChen.Part3.ActualSmoothCoreMaassEndomorphism20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.ActualUpperMaassLinearity20261025a
open ImbalancedChen.Part3.SmoothTensorLaplacianRender20261025a

def renderedSeed (s : SmoothSeed) : SmoothSeed :=
  ⟨s.1 * 2, ordinalRenderedFamily s.1 s.2⟩

theorem coreRepresentative_zero (N : ℕ) [NeZero N] :
    coreRepresentative N (0 : smoothCore N) = 0 :=
  (coreRepresentativeLinearMap N).map_zero

/-- The concrete generator output is another literal generating seed. -/
theorem generator_rendered_output (N : ℕ) [NeZero N] (s : SmoothSeed) :
    coreRepresentative N (seedCoreElement N (renderedSeed s)) =
      upperMaass (coreRepresentative N (seedCoreElement N s)) := by
  rw [coreRepresentative_seed, coreRepresentative_seed]
  exact (upperMaass_smoothFinitePoincare_eq_ordinal_render N s.1 s.2).symm

private theorem coreRepresentative_c2 (N : ℕ) [NeZero N] (u : smoothCore N) :
    ContDiffOn ℝ 2 (extendUpper (coreRepresentative N u)) positiveChart :=
  (coreRepresentative_cinfty N u).of_le (by simp)

/-- Genuine output-core membership for every element of the actual span,
derived from explicit generator rendering and differential linearity. -/
theorem smoothCoreMaass_hasCoreOutput (N : ℕ) [NeZero N] (u : smoothCore N) :
    ∃ v : smoothCore N,
      coreRepresentative N v = upperMaass (coreRepresentative N u) := by
  rcases u with ⟨u, hu⟩
  change u ∈ Submodule.span ℂ (range (seedVector N)) at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨s, rfl⟩ := hu
      exact ⟨seedCoreElement N (renderedSeed s), generator_rendered_output N s⟩
  | zero =>
      refine ⟨0, ?_⟩
      rw [coreRepresentative_zero, coreRepresentative_zero, upperMaass_zero]
  | add u w hu hw ihu ihw =>
      obtain ⟨v, hv⟩ := ihu
      obtain ⟨x, hx⟩ := ihw
      refine ⟨v + x, ?_⟩
      change coreRepresentative N (v + x) =
        upperMaass (coreRepresentative N
          ((⟨u, hu⟩ : smoothCore N) + (⟨w, hw⟩ : smoothCore N)))
      rw [coreRepresentative_add, coreRepresentative_add,
        upperMaass_add _ _ (coreRepresentative_c2 N ⟨u, hu⟩)
          (coreRepresentative_c2 N ⟨w, hw⟩), hv, hx]
  | smul c u hu ihu =>
      obtain ⟨v, hv⟩ := ihu
      refine ⟨c • v, ?_⟩
      change coreRepresentative N (c • v) =
        upperMaass (coreRepresentative N (c • (⟨u, hu⟩ : smoothCore N)))
      rw [coreRepresentative_smul, coreRepresentative_smul, upperMaass_smul, hv]

def coreMaassOutput (N : ℕ) [NeZero N] (u : smoothCore N) : smoothCore N :=
  Classical.choose (smoothCoreMaass_hasCoreOutput N u)

/-- Exact equality to the true geometric differential, everywhere on H. -/
theorem coreMaassOutput_spec (N : ℕ) [NeZero N] (u : smoothCore N) :
    coreRepresentative N (coreMaassOutput N u) =
      upperMaass (coreRepresentative N u) :=
  Classical.choose_spec (smoothCoreMaass_hasCoreOutput N u)

theorem coreMaassOutput_unique (N : ℕ) [NeZero N] (u v : smoothCore N)
    (hv : coreRepresentative N v = upperMaass (coreRepresentative N u)) :
    coreMaassOutput N u = v := by
  apply coreRepresentative_injective N
  exact (coreMaassOutput_spec N u).trans hv.symm

theorem coreMaassOutput_add (N : ℕ) [NeZero N] (u v : smoothCore N) :
    coreMaassOutput N (u + v) = coreMaassOutput N u + coreMaassOutput N v := by
  apply coreMaassOutput_unique N
  rw [coreRepresentative_add, coreMaassOutput_spec, coreMaassOutput_spec,
    coreRepresentative_add, upperMaass_add _ _ (coreRepresentative_c2 N u)
      (coreRepresentative_c2 N v)]

theorem coreMaassOutput_smul (N : ℕ) [NeZero N] (c : ℂ) (u : smoothCore N) :
    coreMaassOutput N (c • u) = c • coreMaassOutput N u := by
  apply coreMaassOutput_unique N
  rw [coreRepresentative_smul, coreMaassOutput_spec, coreRepresentative_smul,
    upperMaass_smul]

/-- The actual quotient smooth-core Laplacian is an endomorphism of that
same core; this is stronger than a merely H-valued differential expression. -/
def coreMaassEndomorphism (N : ℕ) [NeZero N] : smoothCore N →ₗ[ℂ] smoothCore N where
  toFun := coreMaassOutput N
  map_add' := coreMaassOutput_add N
  map_smul' := coreMaassOutput_smul N

theorem coreMaassEndomorphism_realizes_actualMaass (N : ℕ) [NeZero N]
    (u : smoothCore N) :
    coreRepresentative N (coreMaassEndomorphism N u) = smoothCoreMaass N u :=
  coreMaassOutput_spec N u

theorem coreMaassEndomorphism_generator (N : ℕ) [NeZero N] (s : SmoothSeed) :
    coreMaassEndomorphism N (seedCoreElement N s) =
      seedCoreElement N (renderedSeed s) :=
  coreMaassOutput_unique N _ _ (generator_rendered_output N s)

end
end ImbalancedChen.Part3.ActualSmoothCoreMaassEndomorphism20261025a
