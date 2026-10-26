import ImbalancedChen.Part3ActualHeckeSecondL2
import ImbalancedChen.Part3ZeroCuspOriginalTraceMinimalPair

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

DEDUP: the full canonical quotient measure theorem is the existing frozen
ActualFrickeQuotientMeasure00063d, and actual Fricke L2 isometry is the
existing ActualHeckeSecondL2. They are reused, not assumed or duplicated.
Here actual quotient involutivity and measure-preserving AE composition
prove Hilbert involutivity/surjectivity. The resulting genuine linear
isometry equivalence has the ORIGINAL compact trace's actual zero-chart
quotient representative. No hMeasure, presumed unitary, or domain premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b

open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.InfinityZeroActualFiniteGeometricAssembly20261026b
open ImbalancedChen.Part3.ZeroCuspOriginalTraceMinimalPair20261026b
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a

theorem frickeL2_involutive (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Involutive (frickeL2 N hN) := by
  intro F
  have hmp : MeasurePreserving (quotientFricke N hN) (carrierPushforward N) (carrierPushforward N) :=
    ⟨quotientFricke_measurable N hN, quotientFricke_map_measure N hN⟩
  have hout := frickeL2_coe N hN (frickeL2 N hN F)
  have hin := hmp.quasiMeasurePreserving.ae_eq_comp (frickeL2_coe N hN F)
  apply Lp.ext
  filter_upwards [hout, hin] with q hq hq'
  calc
    _ = frickeL2 N hN F (quotientFricke N hN q) := hq
    _ = F (quotientFricke N hN (quotientFricke N hN q)) := hq'
    _ = F q := congrArg F (quotientFricke_involutive N hN q)

/-- Genuine surjective canonical-quotient Fricke Hilbert isometry. -/
def globalFrickeL2Equiv (N : ℕ) [NeZero N] (hN : 0 < N) :
    Lp ℂ 2 (carrierPushforward N) ≃ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward N) :=
  LinearIsometryEquiv.ofSurjective (frickeL2 N hN) (frickeL2_involutive N hN).surjective

theorem globalFrickeL2Equiv_apply (N : ℕ) [NeZero N] (hN : 0 < N)
    (F : Lp ℂ 2 (carrierPushforward N)) : globalFrickeL2Equiv N hN F = frickeL2 N hN F := rfl

/-- The full original H trace descends by genuine Gamma0 invariance. -/
def originalTraceQuotient (N : ℕ) (f : UpperHalfPlane → ℂ) : Gamma0OrbitSpace N → ℂ :=
  quotientInvariantFunction N (complexSeedTrace N f) (compactSeedTrace_gamma0_invariant N f)

theorem complexPoincare_ae_originalTraceQuotient (N : ℕ) [NeZero N]
    (f : UpperHalfPlane → ℂ) :
    complexPoincare N f =ᵐ[carrierPushforward N] originalTraceQuotient N f := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [complexPoincare_projection]
  rfl

/-- Pointwise full-quotient dictionary, including noncanonical representatives. -/
theorem originalTraceQuotient_comp_Fricke (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (q : Gamma0OrbitSpace N) :
    originalTraceQuotient N f (quotientFricke N hN q) = originalZeroTraceQuotient N hN f q := by
  refine Quotient.inductionOn q ?_
  intro z
  rw [quotientFricke_projection]
  change complexSeedTrace N f (frickeSL N hN • z) = _
  rfl

/-- The existing actual Hilbert map is the ORIGINAL zero-chart trace
whenever the original quotient vector has its actual periodized-seed representative. -/
theorem frickeL2_original_trace_ae (N : ℕ) [NeZero N] (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (F : Lp ℂ 2 (carrierPushforward N))
    (hF : (F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f) :
    (frickeL2 N hN F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      originalZeroTraceQuotient N hN f := by
  have hmp : MeasurePreserving (quotientFricke N hN) (carrierPushforward N) (carrierPushforward N) :=
    ⟨quotientFricke_measurable N hN, quotientFricke_map_measure N hN⟩
  have hfull := hF.trans (complexPoincare_ae_originalTraceQuotient N f)
  have hcomp := hmp.quasiMeasurePreserving.ae_eq_comp hfull
  filter_upwards [frickeL2_coe N hN F, hcomp] with q hq hq'
  exact hq.trans (hq'.trans (originalTraceQuotient_comp_Fricke N hN f q))

end ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
