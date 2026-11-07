import ImbalancedChen.Part3GammaMinimalPairFormApproximation
import ImbalancedChen.Part3GammaOriginalCoreCutoffEventualExact
import ImbalancedChen.Part3Gamma0WeightedCutoffDefectLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual invariant smooth multiplication on the original quotient core now
has a canonical LINEAR energy-completion lift. Its physical vector is the
literal quotient product and its form output is the full native Leibniz
differential. Form membership and core/gradient approximation are proved
from the actual minimal graph, not supplied as multiplier hypotheses.

For the original actual cutoff square this lift is eventually EXACTLY
the original core embedding, hence converges in the genuine energy norm.
Extending this map to arbitrary completed-form inputs still requires a
uniform core energy bound; no such bound is assumed or claimed here.
-/

namespace ImbalancedChen.Part3.GammaSmoothCoreMultiplierEnergyLift20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CarrierGradientHilbertMap20261026b GammaMinimalPairFormApproximation20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaCompactSeedCutoffPlateau20261026a GammaOriginalCoreCutoffEventualExact20261026b
open ActualModularCutoffMaassBudget20261025a Gamma0WeightedCutoffDefectLimit20261026a

/-- All genuine form and approximation data for the original smooth-core
product. Neither a core-product membership nor a form-domain premise is
required, even for an invariant multiplier unbounded away from the seed. -/
theorem exists_smooth_core_multiplier_energy
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ∃ e : EnergyCompletion N,
      ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
        =ᵐ[carrierPushforward N] quotientMultiplier N chi hc * (u : QuotientL2 N) ∧
      (∃ V : QuotientL2 N,
        ((V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
          quotientMultiplier N (multiplierDifferential chi (coreRepresentative N u))
            (multiplierDifferential_invariant N _ _ hc (coreRepresentative_gamma0_invariant N u)
              (hcs.of_le (by simp)) ((coreRepresentative_cinfty N u).of_le (by simp)))) ∧
        ∀ d : EnergyCompletion N, actualDirichletPair N d e = inner ℂ (physicalProjection N d) V) ∧
      (∃ s : ℕ → EnergyCore N,
        Tendsto (fun n => coreEmbedding N (s n)) atTop (𝓝 e) ∧
        Tendsto (fun n => carrierCoreGradient N (s n)) atTop
          (𝓝 (completedCarrierGradient N e))) := by
  obtain ⟨U,V,hU,hV,hgraph⟩ := exists_legal_multiplied_core_test N u chi hc hcs
  obtain ⟨s,e,hp,hL,he,hproj,ht,hgradient,henergy⟩ :=
    exists_minimal_pair_form_approximation N U V hgraph
  exact ⟨e,by simpa only [hproj] using hU,⟨V,hV,ht⟩,⟨s,he,hgradient⟩⟩

/-- Canonical by actual physical-projection injectivity; the analytic
existence is supplied by the preceding constructed approximation. -/
def coreMultiplierEnergyLift
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) : EnergyCompletion N :=
  Classical.choose (exists_smooth_core_multiplier_energy N u chi hc hcs)

theorem coreMultiplierEnergyLift_physical_ae
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ((physicalProjection N (coreMultiplierEnergyLift N u chi hc hcs) : QuotientL2 N) :
      Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N chi hc * (u : QuotientL2 N) :=
  (Classical.choose_spec (exists_smooth_core_multiplier_energy N u chi hc hcs)).1

theorem smoothCoreProduct_invariant
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi) : IsGammaInvariant N (chi * coreRepresentative N u) := by
  intro gamma z
  simp only [Pi.mul_apply,hc gamma z,coreRepresentative_gamma0_invariant N u gamma z]

/-- The physical energy lift has the genuine globally smooth invariant
H representative chi*coreRepresentative. This is an equality on the
actual quotient measure; no carrier-restricted identity is globalized. -/
theorem coreMultiplierEnergyLift_smooth_representative_ae
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ((physicalProjection N (coreMultiplierEnergyLift N u chi hc hcs) : QuotientL2 N) :
      Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientMultiplier N (chi * coreRepresentative N u) (smoothCoreProduct_invariant N u chi hc) := by
  have hquot : quotientMultiplier N (chi * coreRepresentative N u)
      (smoothCoreProduct_invariant N u chi hc) =
      quotientMultiplier N chi hc * chosenQuotientRepresentative N u := by
    funext q
    exact Quotient.inductionOn q (fun z => rfl)
  rw [hquot]
  filter_upwards [coreMultiplierEnergyLift_physical_ae N u chi hc hcs,
    (chosenRepresentative_spec N u).1] with q hq huq
  simpa only [Pi.mul_apply,huq] using hq

theorem coreMultiplierEnergyLift_native_output
    (N : ℕ) [NeZero N] (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    ∃ V : QuotientL2 N,
      ((V : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        quotientMultiplier N (multiplierDifferential chi (coreRepresentative N u))
          (multiplierDifferential_invariant N _ _ hc (coreRepresentative_gamma0_invariant N u)
            (hcs.of_le (by simp)) ((coreRepresentative_cinfty N u).of_le (by simp)))) ∧
      ∀ d : EnergyCompletion N,
        actualDirichletPair N d (coreMultiplierEnergyLift N u chi hc hcs) =
          inner ℂ (physicalProjection N d) V :=
  (Classical.choose_spec (exists_smooth_core_multiplier_energy N u chi hc hcs)).2.1

theorem coreMultiplierEnergyLift_add
    (N : ℕ) [NeZero N] (u v : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    coreMultiplierEnergyLift N (u+v) chi hc hcs =
      coreMultiplierEnergyLift N u chi hc hcs + coreMultiplierEnergyLift N v chi hc hcs := by
  apply physicalProjection_injective N
  rw [map_add]
  apply Lp.ext
  filter_upwards [coreMultiplierEnergyLift_physical_ae N (u+v) chi hc hcs,
    coreMultiplierEnergyLift_physical_ae N u chi hc hcs,
    coreMultiplierEnergyLift_physical_ae N v chi hc hcs,
    Lp.coeFn_add (u : QuotientL2 N) (v : QuotientL2 N),
    Lp.coeFn_add (physicalProjection N (coreMultiplierEnergyLift N u chi hc hcs))
      (physicalProjection N (coreMultiplierEnergyLift N v chi hc hcs))]
    with q huv hu hv hadd hsum
  simp only [Pi.mul_apply] at huv hu hv
  rw [hsum,huv,hu,hv]
  change quotientMultiplier N chi hc q * ((u : QuotientL2 N)+(v : QuotientL2 N)) q = _
  rw [hadd]
  ring

theorem coreMultiplierEnergyLift_smul
    (N : ℕ) [NeZero N] (c : ℂ) (u : smoothCore N) (chi : UpperHalfPlane → ℂ)
    (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    coreMultiplierEnergyLift N (c • u) chi hc hcs = c • coreMultiplierEnergyLift N u chi hc hcs := by
  apply physicalProjection_injective N
  rw [map_smul]
  apply Lp.ext
  filter_upwards [coreMultiplierEnergyLift_physical_ae N (c • u) chi hc hcs,
    coreMultiplierEnergyLift_physical_ae N u chi hc hcs,
    Lp.coeFn_smul c (u : QuotientL2 N),
    Lp.coeFn_smul c (physicalProjection N (coreMultiplierEnergyLift N u chi hc hcs))]
    with q hcu hu hsmul hsum
  simp only [Pi.mul_apply] at hcu hu
  rw [hsum,hcu]
  change quotientMultiplier N chi hc q * (c • (u : QuotientL2 N)) q = _
  rw [hsmul]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hu]
  ring

/-- A genuine original-core multiplier into the ACTUAL energy completion.
Continuity in the energy norm is deliberately a separate analytic claim. -/
def coreMultiplierEnergyLinear
    (N : ℕ) [NeZero N] (chi : UpperHalfPlane → ℂ) (hc : IsGammaInvariant N chi)
    (hcs : ContDiffOn ℝ ∞ (extendUpper chi) positiveChart) :
    EnergyCore N →ₗ[ℂ] EnergyCompletion N where
  toFun u := coreMultiplierEnergyLift N u chi hc hcs
  map_add' u v := coreMultiplierEnergyLift_add N u v chi hc hcs
  map_smul' c u := coreMultiplierEnergyLift_smul N c u chi hc hcs

def actualCutoffCoreEnergy (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0 < Y) :
    EnergyCore N →ₗ[ℂ] EnergyCompletion N :=
  coreMultiplierEnergyLinear N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y)
    (actualCutoff_cinfty Y hY)

def actualCutoffSquareCoreEnergy (N : ℕ) [NeZero N] (Y : ℝ) (hY : 0 < Y) :
    EnergyCore N →ₗ[ℂ] EnergyCompletion N :=
  coreMultiplierEnergyLinear N (complexGlobalH Y * complexGlobalH Y)
    (actualCutoff_square_invariant N Y) (actualCutoff_square_cinfty Y hY)

/-- The original full-core cutoff-square exactness now holds in the
genuine energy completion itself, including the entire closed-form
energy and the global carrier gradient, rather than only physical L2. -/
theorem exists_actualCutoffSquareCoreEnergy_eventual_exact
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ Y : ℝ, ∀ hY : plateauThreshold a b ≤ Y,
        actualCutoffSquareCoreEnergy N Y ((plateauThreshold_pos a b).trans_le hY) u =
          coreEmbedding N u := by
  obtain ⟨a,b,ha,hab,hfixed⟩ := exists_original_core_eventual_fixed N u
  refine ⟨a,b,ha,hab,?_⟩
  intro Y hY
  apply physicalProjection_injective N
  rw [physicalProjection_core]
  apply Lp.ext
  exact (coreMultiplierEnergyLift_physical_ae N u _ (actualCutoff_square_invariant N Y)
    (actualCutoff_square_cinfty Y ((plateauThreshold_pos a b).trans_le hY))).trans
      (hfixed Y hY).2.2

/-- Actual original cutoff scales n+2 converge in the energy norm on
EVERY original core vector because they are eventually exactly equal. -/
theorem actualCutoffSquareCoreEnergy_tendsto
    (N : ℕ) [NeZero N] (u : EnergyCore N) :
    Tendsto (fun n => actualCutoffSquareCoreEnergy N (cutoffHeight n) (cutoffHeight_pos n) u)
      atTop (𝓝 (coreEmbedding N u)) := by
  obtain ⟨a,b,ha,hab,hexact⟩ := exists_actualCutoffSquareCoreEnergy_eventual_exact N u
  have heventual : ∀ᶠ n in atTop,
      actualCutoffSquareCoreEnergy N (cutoffHeight n) (cutoffHeight_pos n) u = coreEmbedding N u := by
    filter_upwards [cutoffHeight_tendsto.eventually (eventually_ge_atTop (plateauThreshold a b))]
      with n hn
    exact hexact (cutoffHeight n) hn
  exact tendsto_const_nhds.congr' heventual

end
end ImbalancedChen.Part3.GammaSmoothCoreMultiplierEnergyLift20261026b
