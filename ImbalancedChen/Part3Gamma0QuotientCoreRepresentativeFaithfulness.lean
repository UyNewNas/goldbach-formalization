import ImbalancedChen.Part3Gamma0CompactTensorQuotientL2Core
import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding
import ImbalancedChen.Part3MaassFiniteCoreL2Graph

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Representative faithfulness for the actual Gamma0 quotient and canonical
hyperbolic volume. Each actual effective carrier translate has exactly the
same quotient pushforward measure. Therefore quotient a.e. equality pulls
back to a.e. equality on every actual cell; the proved conull tiling gives
a.e. equality on the full upper half-plane. Continuous representatives are
then equal everywhere because canonical hyperbolic volume has full support.

This is applied to the EXISTING quotientTensorPoincareL2 object. Equality
of its input vectors forces pointwise equality of the actual automorphic
Poincare functions and hence equality of their actual upperMaass outputs.
No hDomain, spectral normalization, operator equivariance, or hypothetical
quotient/reduced-carrier equivalence is used as an input.
-/

namespace ImbalancedChen.Part3.Gamma0QuotientCoreRepresentativeFaithfulness20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a

/-- This is the actual quotient pushforward on EACH proved effective
cell, with no multiplicity factor from the central action kernel. -/
theorem effectiveCell_pushforward_eq (N : ℕ) [NeZero N] (q : effectiveGamma0 N) :
    ((volume : Measure UpperHalfPlane).restrict (effectiveCell N q)).map
      (orbitProjection N) = carrierPushforward N := by
  change cellPushforward N ((effectiveRepresentative N q) • reducedCarrier N) = _
  rw [cellPushforward_gamma0_translate]
  exact reducedCarrier_pushforward_eq N

/-- Arbitrary quotient a.e. equality propagates through the ACTUAL conull
tiling. No regularity or invariance premise on the quotient functions is
needed, because orbit projection already carries genuine invariance. -/
theorem quotient_ae_pullback_full (N : ℕ) [NeZero N]
    {F G : Gamma0OrbitSpace N → ℂ} (h : F =ᵐ[carrierPushforward N] G) :
    (F ∘ orbitProjection N) =ᵐ[(volume : Measure UpperHalfPlane)]
      (G ∘ orbitProjection N) := by
  letI : Countable (effectiveGamma0 N) := inferInstance
  have hcell (q : effectiveGamma0 N) :
      (F ∘ orbitProjection N) =ᵐ[(volume : Measure UpperHalfPlane).restrict (effectiveCell N q)]
        (G ∘ orbitProjection N) := by
    have hmap : F =ᵐ[((volume : Measure UpperHalfPlane).restrict (effectiveCell N q)).map
        (orbitProjection N)] G := by rw [effectiveCell_pushforward_eq]; exact h
    exact ae_of_ae_map (orbitProjection_measurable N).aemeasurable hmap
  have hall := (ae_eq_restrict_iUnion_iff (effectiveCell N)
    (F ∘ orbitProjection N) (G ∘ orbitProjection N)).mpr hcell
  change (F ∘ orbitProjection N) =ᵐ[(volume : Measure UpperHalfPlane).restrict (allEffectiveCells N)]
    (G ∘ orbitProjection N) at hall
  rw [Measure.restrict_eq_self_of_ae_mem (allEffectiveCells_ae N)] at hall
  exact hall

/-- The real canonical hyperbolic measure detects equality of continuous
automorphic representatives after the preceding full-plane AE transfer. -/
theorem quotient_ae_continuous_pullback_eq (N : ℕ) [NeZero N]
    {F G : Gamma0OrbitSpace N → ℂ} (h : F =ᵐ[carrierPushforward N] G)
    (hF : Continuous (F ∘ orbitProjection N)) (hG : Continuous (G ∘ orbitProjection N)) :
    F ∘ orbitProjection N = G ∘ orbitProjection N := by
  letI := canonical_volume_isOpenPosMeasure
  exact Measure.eq_of_ae_eq (quotient_ae_pullback_full N h) hF hG

/-- In particular no two continuous automorphic representatives of one
actual quotient L2 vector can disagree on even an exceptional orbit. -/
theorem quotient_ae_eq_of_continuous_pullbacks (N : ℕ) [NeZero N]
    {F G : Gamma0OrbitSpace N → ℂ} (h : F =ᵐ[carrierPushforward N] G)
    (hF : Continuous (F ∘ orbitProjection N)) (hG : Continuous (G ∘ orbitProjection N)) :
    F = G := by
  have heq := quotient_ae_continuous_pullback_eq N h hF hG
  funext q
  exact Quotient.inductionOn q (fun z => congrFun heq z)

theorem poincare_eq_of_quotientL2_eq (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (h : quotientTensorPoincareL2 N s T = quotientTensorPoincareL2 N t U) :
    finiteCompactTensorPoincare N s T = finiteCompactTensorPoincare N t U := by
  have hF : (quotientTensorPoincareL2 N s T : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientTensorPoincare N s T := (quotientTensorPoincare_memLp_two N s T).coeFn_toLp
  have hG : (quotientTensorPoincareL2 N t U : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientTensorPoincare N t U := (quotientTensorPoincare_memLp_two N t U).coeFn_toLp
  rw [h] at hF
  have hQ := hF.symm.trans hG
  have hH := quotient_ae_pullback_full N hQ
  have hH' : finiteCompactTensorPoincare N s T =ᵐ[(volume : Measure UpperHalfPlane)]
      finiteCompactTensorPoincare N t U := by
    simpa only [Function.comp_def,quotientTensorPoincare_projection] using hH
  letI := canonical_volume_isOpenPosMeasure
  exact Measure.eq_of_ae_eq hH' (finiteCompactTensorPoincare_continuous N s T)
    (finiteCompactTensorPoincare_continuous N t U)

theorem quotientL2_eq_of_poincare_eq (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (h : finiteCompactTensorPoincare N s T = finiteCompactTensorPoincare N t U) :
    quotientTensorPoincareL2 N s T = quotientTensorPoincareL2 N t U := by
  have hQ : quotientTensorPoincare N s T = quotientTensorPoincare N t U := by
    funext q
    exact Quotient.inductionOn q (fun z => congrFun h z)
  apply Lp.ext
  exact (quotientTensorPoincare_memLp_two N s T).coeFn_toLp.trans
    ((Filter.Eventually.of_forall (fun q => congrFun hQ q)).trans
      (quotientTensorPoincare_memLp_two N t U).coeFn_toLp.symm)

/-- Exact equivalence on the EXISTING actual quotient core object. -/
theorem quotientL2_eq_iff_poincare_eq (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    quotientTensorPoincareL2 N s T = quotientTensorPoincareL2 N t U ↔
      finiteCompactTensorPoincare N s T = finiteCompactTensorPoincare N t U :=
  ⟨poincare_eq_of_quotientL2_eq N s T t U,quotientL2_eq_of_poincare_eq N s T t U⟩

/-- The actual coordinate differential expression is independent of a
seed presentation of the same quotient L2 input. This does not assert that
the output descends or is L2; those are separate genuine supplier goals. -/
theorem upperMaass_eq_of_quotientL2_eq (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor)
    (h : quotientTensorPoincareL2 N s T = quotientTensorPoincareL2 N t U) :
    upperMaass (finiteCompactTensorPoincare N s T) =
      upperMaass (finiteCompactTensorPoincare N t U) :=
  congrArg upperMaass (poincare_eq_of_quotientL2_eq N s T t U h)

end
end ImbalancedChen.Part3.Gamma0QuotientCoreRepresentativeFaithfulness20261025a
