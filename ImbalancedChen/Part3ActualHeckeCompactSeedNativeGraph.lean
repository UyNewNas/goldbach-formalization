import ImbalancedChen.Part3ActualCompactSeedHeckeQuotient
import ImbalancedChen.Part3ActualDualHeckeSeedMaass
import ImbalancedChen.Part3GammaFiniteTensorGraphCore

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The ACTUAL bounded normalized physical Hecke operator maps a genuine
original compact smooth H-seed Poincare input/output pair into the ACTUAL
minimal closed Gamma0 Maass graph. The true right-transversal Poincare
identity, full +/-I descent, finite compact support, native smoothness,
actual upperMaass covariance and quotient AE/L2 dictionaries are all paid.
The clean constructive compact smooth seed graph theorem is reused.
No transformed seed/core identity, domain inclusion or commutation target
is supplied as an assumption. This is the compact-seed native graph bridge;
no global Friedrichs-domain commutation or essential SA is inferred.
-/

namespace ImbalancedChen.Part3.ActualHeckeCompactSeedNativeGraph20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ActualBoundedPhysicalHecke20261026b ActualCompactSeedHeckeQuotient20261026b
open ActualCompactSeedHeckeReindex20261026b ActualDualHeckeSeedCompactSmooth20261026b
open ActualDualHeckeSeedMaass20261026b ActualCompactSeedMaassJoin20261025a
open GammaFiniteTensorGraphCore20261026a GammaCompactSeedGraphTransport20261026a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

/-- Physical Hecke on BOTH ORIGINAL compact-seed graph coordinates lands
in the genuine native minimal graph. Only the original input/output
representatives are named in the hypotheses, not the Hecke result. -/
theorem physicalHecke_original_seed_pair_mem_minimalGraph
    (f : ℍ → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f)
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N (upperMaass f)) :
    (physicalHeckeOperator N p hN hp hpN u,physicalHeckeOperator N p hN hp hpN v) ∈
      (actualClosedGammaMaass N).graph := by
  have hf2 : ContDiffOn ℝ 2 (extendUpper f) positiveChart := hf.of_le (by simp)
  have hTu := physicalHecke_original_compact_seed N p hN hp hpN f
    (native_C2_continuous f hf2) hfc (subset_tsupport f) u hu
  have hsupport : Function.support (upperMaass f) ⊆ tsupport f :=
    upperMaass_support_subset_closed f hfc.isClosed (subset_tsupport f)
  have hTv := physicalHecke_original_compact_seed N p hN hp hpN (upperMaass f)
    (native_C2_upperMaass_continuous f hf2) hfc hsupport v hv
  have houtput : (physicalHeckeOperator N p hN hp hpN v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass (dualHeckeSeed p hp f)) := by
    rw [dualHeckeSeed_upperMaass p hp f hf]
    exact hTv
  exact compact_smooth_seed_ae_pair_mem_minimalGraph N (dualHeckeSeed p hp f)
    (dualHeckeSeed_hasCompactSupport p hp f hfc) (dualHeckeSeed_nativeCinfty p hp f hf)
    (physicalHeckeOperator N p hN hp hpN u) (physicalHeckeOperator N p hN hp hpN v) hTu houtput

/-- Fully concrete original compact input/output definitions. No AE or
native graph supplier is an input to this conclusion. -/
theorem physicalHecke_compactInput_graph (f : ℍ → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    (physicalHeckeOperator N p hN hp hpN
      (compactInput N f (hf.of_le (by simp)) (tsupport f) hfc (subset_tsupport f)),
    physicalHeckeOperator N p hN hp hpN
      (compactOutput N f (hf.of_le (by simp)) (tsupport f) hfc (subset_tsupport f))) ∈
        (actualClosedGammaMaass N).graph :=
  physicalHecke_original_seed_pair_mem_minimalGraph N p hN hp hpN f hfc hf _ _
    (compactInput_ae N f _ (tsupport f) hfc (subset_tsupport f))
    (compactOutput_ae N f _ (tsupport f) hfc (subset_tsupport f))

/-- Actual native-domain element and EXACT original physical Hecke
output, obtained from proved graph membership rather than postulated. -/
theorem physicalHecke_compactInput_native_domain_action (f : ℍ → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ w : (actualClosedGammaMaass N).domain,
      (w : QuotientL2 N) = physicalHeckeOperator N p hN hp hpN
        (compactInput N f (hf.of_le (by simp)) (tsupport f) hfc (subset_tsupport f)) ∧
      actualClosedGammaMaass N w = physicalHeckeOperator N p hN hp hpN
        (compactOutput N f (hf.of_le (by simp)) (tsupport f) hfc (subset_tsupport f)) :=
  LinearPMap.mem_graph_iff.mp (physicalHecke_compactInput_graph N p hN hp hpN f hfc hf)

end
end ImbalancedChen.Part3.ActualHeckeCompactSeedNativeGraph20261026b
