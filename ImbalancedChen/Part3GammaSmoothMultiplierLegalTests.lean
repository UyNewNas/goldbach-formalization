import ImbalancedChen.Part3GammaNativeMaassLeibniz
import ImbalancedChen.Part3GammaModularCutoffMinimalDomain

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Legal actual quotient tests obtained by multiplying original finite smooth
Poincare tests by a genuine Gamma0-invariant smooth multiplier. Compact
seed multiplication and the constructive finite tensor graph-core theorem
produce the minimal-domain pair. Its output is exactly the descended
native Maass Leibniz expression, including cross-gradient terms.

The final theorem applies to EVERY member of the ORIGINAL finite tensor
smoothCore, through its proved finite-family representation. It does not
assume that the multiplied function is in that algebraic tensor span.
-/

namespace ImbalancedChen.Part3.GammaSmoothMultiplierLegalTests20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0SmoothCompactTensorCore20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0CompactTensorQuotientL2Core20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open Gamma0ActualMaassClosedOperator20261025a
open GammaCompactSeedGraphTransport20261026a GammaFiniteTensorGraphCore20261026a
open GammaSmoothMultiplierPeriodization20261026a GammaNativeMaassLeibniz20261026a
open ActualCompactSeedMaassJoin20261025a ActualGamma0MaassDescent20261025a
open ActualModularCutoffMaassBudget20261025a ActualModularSmoothCuspCutoff20261025a

/-- The actual output, with every differential term explicitly retained. -/
def multiplierDifferential (chi F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  chi z * upperMaass F z + F z * upperMaass chi z + maassCross chi F z

theorem multiplierDifferential_eq (chi F : UpperHalfPlane → ℂ)
    (hcs : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    multiplierDifferential chi F = upperMaass (chi*F) := by
  funext z
  exact (upperMaass_mul chi F hcs hFs z).symm

/-- The CROSS TERM descends as part of the true invariant differential;
its invariance is derived, not supplied as another hypothesis. -/
theorem multiplierDifferential_invariant (N : ℕ) (chi F : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi) (hF : IsGammaInvariant N F)
    (hcs : ContDiffOn ℝ 2 (extendUpper chi) positiveChart)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart) :
    IsGammaInvariant N (multiplierDifferential chi F) := by
  rw [multiplierDifferential_eq chi F hcs hFs]
  have hs : ContDiffOn ℝ 2 (extendUpper (chi*F)) positiveChart := by
    rw [extendUpper_mul]
    exact hcs.mul hFs
  intro gamma z
  have hprod : IsGammaInvariant N (chi*F) := by
    intro g w
    simp only [Pi.mul_apply, hc g w, hF g w]
  exact upperMaass_gamma0_invariant N (chi*F) hs hprod gamma z

/-- Actual finite-family test interface. The output is the literal
Leibniz differential on the original Poincare function, and BOTH genuine
quotient L2 vectors are constructed from the compact multiplied seed. -/
theorem exists_legal_multiplied_poincare_pair
    (N : ℕ) [NeZero N] {ι : Type*} (s : Finset ι) (T : ι → SmoothCompactTensor)
    (chi : UpperHalfPlane → ℂ) (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ∃ U V : Lp ℂ 2 (carrierPushforward N),
      ((U : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N chi hc * quotientTensorPoincare N s
          (fun i => (T i).toCompactTensor)) ∧
      ((V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N (multiplierDifferential chi (smoothFinitePoincare N s T))
          (multiplierDifferential_invariant N chi (smoothFinitePoincare N s T) hc
            (smoothFinitePoincare_gamma0_invariant N s T) (hcs.of_le (by simp))
            ((smoothFinitePoincare_contDiffOn_chart N s T).of_le (by simp)))) ∧
      (U,V) ∈ (actualClosedGammaMaass N).graph := by
  let f := finiteCoreFunction s (fun i => (T i).toCompactTensor)
  let F := smoothFinitePoincare N s T
  obtain ⟨hfc, hfs⟩ := finiteSmoothSeed_compact_cinfty s T
  let G := chi*f
  have hGs : ContDiffOn ℝ ∞ (extendUpper G) positiveChart :=
    compact_multiplier_seed_smooth chi f hcs hfs
  have hGsupport : Function.support G ⊆ tsupport f := multiplier_seed_support_subset chi f
  let U := compactInput N G (hGs.of_le (by simp)) (tsupport f) hfc hGsupport
  let V := compactOutput N G (hGs.of_le (by simp)) (tsupport f) hfc hGsupport
  have hU := compactInput_ae N G (hGs.of_le (by simp)) (tsupport f) hfc hGsupport
  have hV := compactOutput_ae N G (hGs.of_le (by simp)) (tsupport f) hfc hGsupport
  have htrace : complexSeedTrace N G = chi*F := complexSeedTrace_mul_invariant N chi f hc
  refine ⟨U,V,?_,?_,?_⟩
  · filter_upwards [hU, reducedProjection_range_ae N] with q hUq hsection
    obtain ⟨z, rfl⟩ := hsection
    rw [hUq, complexPoincare_projection]
    exact congrFun htrace z
  · filter_upwards [hV, reducedProjection_range_ae N] with q hVq hsection
    obtain ⟨z, rfl⟩ := hsection
    rw [hVq, complexPoincare_projection]
    change complexSeedTrace N (upperMaass G) (z : UpperHalfPlane) =
      multiplierDifferential chi F z
    rw [← upperMaass_compactSeedTrace N G (hGs.of_le (by simp)) hfc hGsupport, htrace]
    exact upperMaass_mul chi F (hcs.of_le (by simp))
      ((smoothFinitePoincare_contDiffOn_chart N s T).of_le (by simp)) z
  · exact compact_smooth_seed_ae_pair_mem_minimalGraph N G
      (multiplier_seed_hasCompactSupport chi f hfc) hGs U V hU hV

/-- Every actual original core vector is first rendered as one genuine
finite SmoothSeed by the EXISTING representation theorem. The product is
then made a legal minimal-domain test, not falsely inserted in smoothCore. -/
theorem exists_legal_multiplied_core_test
    (N : ℕ) [NeZero N] (u : smoothCore N)
    (chi : UpperHalfPlane → ℂ) (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ∃ U V : Lp ℂ 2 (carrierPushforward N),
      ((U : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N chi hc * (u : Lp ℂ 2 (carrierPushforward N))) ∧
      ((V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N (multiplierDifferential chi (coreRepresentative N u))
          (multiplierDifferential_invariant N chi (coreRepresentative N u) hc
            (coreRepresentative_gamma0_invariant N u) (hcs.of_le (by simp))
            ((coreRepresentative_cinfty N u).of_le (by simp)))) ∧
      (U,V) ∈ (actualClosedGammaMaass N).graph := by
  obtain ⟨n,T,hT⟩ := exists_finite_poincare_representation N u
  have hu : u = seedCoreElement N ⟨n,T⟩ := Subtype.ext hT
  have hrep : coreRepresentative N u = smoothFinitePoincare N Finset.univ T := by
    rw [hu, coreRepresentative_seed]
  obtain ⟨U,V,hU,hV,hgraph⟩ := exists_legal_multiplied_poincare_pair N Finset.univ T chi hc hcs
  refine ⟨U,V,?_,?_,hgraph⟩
  · have hraw := (quotientTensorPoincare_memLp_two N Finset.univ
      (fun i => (T i).toCompactTensor)).coeFn_toLp
    have hua : ((u : Lp ℂ 2 (carrierPushforward N)) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) := by
      rw [hT]
      exact hraw
    filter_upwards [hU,hua] with q hUq huq
    simpa only [Pi.mul_apply,huq] using hUq
  · simpa only [hrep] using hV

/-- The actual modular cutoff used by the defect/IMS consumer satisfies
all multiplier hypotheses by its genuine global construction. -/
theorem actualCutoff_isGammaInvariant (N : ℕ) (Y : ℝ) :
    IsGammaInvariant N (complexGlobalH Y) := complexGlobalH_invariant N Y

theorem actualCutoff_cinfty (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ ∞ (extendUpper (complexGlobalH Y)) positiveChart := by
  have hs : ContDiffOn ℝ ∞
      (fun p => (globalCutoff Y (chartLift p) : ℂ)) positiveChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (globalCutoff_chart_cinfty Y hY)
  apply hs.congr
  intro p hp
  exact (extendUpper_chartLift (complexGlobalH Y) p hp).symm

/-- Genuine cutoff-squared multiplier, ready for original-core legal tests. -/
theorem actualCutoff_square_invariant (N : ℕ) (Y : ℝ) :
    IsGammaInvariant N (complexGlobalH Y * complexGlobalH Y) := by
  intro gamma z
  simp only [Pi.mul_apply, complexGlobalH_invariant N Y gamma z]

theorem actualCutoff_square_cinfty (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ ∞
      (extendUpper (complexGlobalH Y * complexGlobalH Y)) positiveChart :=
  compact_multiplier_seed_smooth _ _ (actualCutoff_cinfty Y hY) (actualCutoff_cinfty Y hY)

/-- The descended multiplier is the original physical quotient cutoff. -/
theorem actualCutoff_quotientMultiplier (N : ℕ) (Y : ℝ) :
    quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) =
      (fun q => (ActualModularSmoothCutoffL2Tail20261025a.quotientCutoff N Y q : ℂ)) := by
  funext q
  exact Quotient.inductionOn q (fun z => rfl)

theorem actualCutoff_square_quotientMultiplier (N : ℕ) (Y : ℝ) :
    quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
      (actualCutoff_square_invariant N Y) =
      (fun q => (ActualModularSmoothCutoffL2Tail20261025a.quotientCutoff N Y q : ℂ)^2) := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  change (globalCutoff Y z : ℂ) * (globalCutoff Y z : ℂ) = (globalCutoff Y z : ℂ)^2
  rw [pow_two]
/-- No domain premise remains: actual cutoff^2 times ANY original finite
smooth-core test has a legal actual minimal-domain input/output pair. -/
theorem exists_legal_actualCutoff_square_core_test
    (N : ℕ) [NeZero N] (u : smoothCore N) (Y : ℝ) (hY : 0 < Y) :
    ∃ U V : Lp ℂ 2 (carrierPushforward N),
      ((U : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N (complexGlobalH Y * complexGlobalH Y)
          (actualCutoff_square_invariant N Y) * (u : Lp ℂ 2 (carrierPushforward N))) ∧
      ((V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N
          (multiplierDifferential (complexGlobalH Y * complexGlobalH Y) (coreRepresentative N u))
          (multiplierDifferential_invariant N _ _ (actualCutoff_square_invariant N Y)
            (coreRepresentative_gamma0_invariant N u)
            ((actualCutoff_square_cinfty Y hY).of_le (by simp))
            ((coreRepresentative_cinfty N u).of_le (by simp)))) ∧
      (U,V) ∈ (actualClosedGammaMaass N).graph :=
  exists_legal_multiplied_core_test N u _ (actualCutoff_square_invariant N Y)
    (actualCutoff_square_cinfty Y hY)

end
end ImbalancedChen.Part3.GammaSmoothMultiplierLegalTests20261026a
