import ImbalancedChen.Part3CountableSigmaL2Equivalence
import ImbalancedChen.Part3Gamma0CountableCyclicSeeds
import ImbalancedChen.Part3Gamma0ActualGlobalLambdaDomain

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 quotient Hilbert space has a single-L2 Plancherel
model on the countable disjoint union of the genuine scalar spectra.
The measure is literally the sum of the pushforwards of the scalar
spectral measures of the existing Zorn cyclic seeds. Countability is
proved from the actual quotient Hilbert space, not assumed here.

The native physical Friedrichs graph is EXACTLY multiplication by
(1-r)/r in this one L2 space; its full domain is precisely the true
MemLp of that product. This transfers the existing actual global graph
in both directions through the constructed ONTO Sigma-L2 equivalence.

This is an abstract scalar spectral measure bundle. It makes no claim
to cusp/Eisenstein parameters, scattering matrices or 1/(4*pi) density.
-/

namespace ImbalancedChen.Part3.Gamma0ActualSigmaPlancherel20261025a

noncomputable section
open Set MeasureTheory Filter
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open Gamma0ActualGlobalLambdaDomain20261025a
open Gamma0CountableCyclicSeeds20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedMultiplication20261025a
open CountableSigmaMeasureBundle20261025a
open CountableSigmaL2Equivalence20261025a

abbrev ActualSigmaSpectrum (N : ℕ) [NeZero N] :=
  Σ i : ActualSpectralIndex N,ResolventSpectrum (actualGammaResolvent N)

def actualSigmaFiberMeasure (N : ℕ) [NeZero N] (i : ActualSpectralIndex N) :
    Measure (ResolventSpectrum (actualGammaResolvent N)) :=
  scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (i:QuotientL2 N)

instance actualSigmaFiberMeasure_finite (N : ℕ) [NeZero N] (i : ActualSpectralIndex N) :
    IsFiniteMeasure (actualSigmaFiberMeasure N i) := by
  unfold actualSigmaFiberMeasure
  infer_instance

def actualSigmaMeasure (N : ℕ) [NeZero N] : Measure (ActualSigmaSpectrum N) :=
  bundleMeasure (actualSigmaFiberMeasure N)

/-- The whole measure need not be finite. Its sigma-finiteness comes
from the actual countable family of finite scalar spectral fibers. -/
instance actualSigmaMeasure_sigmaFinite (N : ℕ) [NeZero N] :
    SigmaFinite (actualSigmaMeasure N) :=
  bundleMeasure_sigmaFinite (actualSigmaFiberMeasure N)

abbrev ActualSigmaL2 (N : ℕ) [NeZero N] := Lp ℂ 2 (actualSigmaMeasure N)

def actualSigmaAssembly (N : ℕ) [NeZero N] :
    ActualSpectralSum N≃ₗᵢ[ℂ]ActualSigmaL2 N :=
  sigmaL2Equivalence (actualSigmaFiberMeasure N)

/-- A genuine ONTO Plancherel map from the ACTUAL physical quotient
Hilbert space to one scalar L2 space, with no unitary premise. -/
def actualSigmaPlancherel (N : ℕ) [NeZero N] :
    QuotientL2 N≃ₗᵢ[ℂ]ActualSigmaL2 N :=
  (actualGlobalSpectralUnitary N).symm.trans (actualSigmaAssembly N)

theorem actualSigmaPlancherel_fiber (N : ℕ) [NeZero N] (u : QuotientL2 N)
    (i : ActualSpectralIndex N) :
    (fun t => actualSigmaPlancherel N u ⟨i,t⟩)=ᵐ[actualSigmaFiberMeasure N i]
      actualGlobalSpectralCoordinates N u i :=
  sigmaL2Equivalence_fiber (actualSigmaFiberMeasure N) _ i

theorem actualSigmaPlancherel_reconstruction (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    (actualSigmaPlancherel N).symm (actualSigmaPlancherel N u)=u :=
  (actualSigmaPlancherel N).symm_apply_apply u

theorem actualSigmaPlancherel_onto (N : ℕ) [NeZero N] :
    Function.Surjective (actualSigmaPlancherel N) := (actualSigmaPlancherel N).surjective

theorem actualSigmaPlancherel_norm (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    ‖actualSigmaPlancherel N u‖=‖u‖ := (actualSigmaPlancherel N).norm_map u

/-- The exact single-measure Plancherel integral, not a supplied
measure-normalization identity. -/
theorem actualSigmaPlancherel_integral (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    (∫ s,‖actualSigmaPlancherel N u s‖^2∂actualSigmaMeasure N)=‖u‖^2 := by
  rw [← l2_norm_sq_integral,actualSigmaPlancherel_norm]

def actualSigmaLambda (N : ℕ) [NeZero N] (s : ActualSigmaSpectrum N) : ℝ :=
  lambdaCoordinate (actualGammaResolvent N) s.2

def actualSigmaLambdaProduct (N : ℕ) [NeZero N] (g : ActualSigmaL2 N) :
    ActualSigmaSpectrum N→ℂ := fun s => (actualSigmaLambda N s:ℂ)*g s

/-- The fiberwise TRUE graph is exactly the single Sigma-measure AE
graph. Both implications use the proved countable AE decomposition. -/
theorem actualFamilyLambdaGraph_iff_sigma (N : ℕ) [NeZero N]
    (a b : ActualSpectralSum N) :
    actualGlobalFamilyLambdaGraph N a b ↔
      actualSigmaAssembly N b=ᵐ[actualSigmaMeasure N]
        actualSigmaLambdaProduct N (actualSigmaAssembly N a) := by
  constructor
  · intro hab
    apply (bundle_ae_iff (actualSigmaFiberMeasure N) _).mpr
    intro i
    have ha := sigmaL2Equivalence_fiber (actualSigmaFiberMeasure N) a i
    have hb := sigmaL2Equivalence_fiber (actualSigmaFiberMeasure N) b i
    have hi := hab i
    filter_upwards [ha,hb,hi] with t hat hbt hit
    change actualSigmaAssembly N b ⟨i,t⟩ =
      (lambdaCoordinate (actualGammaResolvent N) t:ℂ)*actualSigmaAssembly N a ⟨i,t⟩
    rw [hbt,hat]
    exact hit
  · intro hab
    intro i
    have ha := sigmaL2Equivalence_fiber (actualSigmaFiberMeasure N) a i
    have hb := sigmaL2Equivalence_fiber (actualSigmaFiberMeasure N) b i
    have hi := (bundle_ae_iff (actualSigmaFiberMeasure N) _).mp hab i
    filter_upwards [ha,hb,hi] with t hat hbt hit
    change b i t=(lambdaCoordinate (actualGammaResolvent N) t:ℂ)*a i t
    change actualSigmaAssembly N b ⟨i,t⟩ =
      (lambdaCoordinate (actualGammaResolvent N) t:ℂ)*actualSigmaAssembly N a ⟨i,t⟩ at hit
    rw [hat,hbt] at hit
    exact hit

/-- EXACT native unbounded physical graph in the one-measure model.
There is no lambda-domain, zero-atom or graph-association input. -/
theorem actualGammaFriedrichs_sigma_graph_iff_lambda (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) :
    (u,v)∈(actualGammaFriedrichs N).graph ↔
      actualSigmaPlancherel N v=ᵐ[actualSigmaMeasure N]
        actualSigmaLambdaProduct N (actualSigmaPlancherel N u) :=
  (actualGammaFriedrichs_global_graph_iff_lambda N u v).trans
    (actualFamilyLambdaGraph_iff_sigma N _ _)

/-- The maximal multiplication domain is a CONCLUSION, not a premise.
The reverse direction constructs an actual physical output from the L2
lambda product using the proved onto Plancherel map. -/
theorem actualGammaFriedrichs_sigma_domain_iff_lambda (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    u∈(actualGammaFriedrichs N).domain ↔
      MemLp (actualSigmaLambdaProduct N (actualSigmaPlancherel N u)) 2
        (actualSigmaMeasure N) := by
  constructor
  · intro hu
    have hg := (actualGammaFriedrichs_sigma_graph_iff_lambda N u
      (actualGammaFriedrichs N ⟨u,hu⟩)).mp (LinearPMap.mem_graph _ ⟨u,hu⟩)
    exact (memLp_congr_ae hg).mp (Lp.memLp _)
  · intro hprod
    let k : ActualSigmaL2 N := hprod.toLp
      (actualSigmaLambdaProduct N (actualSigmaPlancherel N u))
    let v : QuotientL2 N := (actualSigmaPlancherel N).symm k
    apply LinearPMap.mem_domain_of_mem_graph (y:=v)
    apply (actualGammaFriedrichs_sigma_graph_iff_lambda N u v).mpr
    change actualSigmaPlancherel N ((actualSigmaPlancherel N).symm k)=ᵐ[_] _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hprod.coeFn_toLp

/-- Equivalent maximal-domain statement starting at an ARBITRARY
single-measure L2 vector rather than a preselected physical domain. -/
theorem actualSigma_model_domain_iff (N : ℕ) [NeZero N] (g : ActualSigmaL2 N) :
    (actualSigmaPlancherel N).symm g∈(actualGammaFriedrichs N).domain ↔
      MemLp (actualSigmaLambdaProduct N g) 2 (actualSigmaMeasure N) := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    actualGammaFriedrichs_sigma_domain_iff_lambda N ((actualSigmaPlancherel N).symm g)

theorem actualSigma_model_graph_iff (N : ℕ) [NeZero N] (g k : ActualSigmaL2 N) :
    ((actualSigmaPlancherel N).symm g,(actualSigmaPlancherel N).symm k)∈
      (actualGammaFriedrichs N).graph ↔
      k=ᵐ[actualSigmaMeasure N] actualSigmaLambdaProduct N g := by
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    actualGammaFriedrichs_sigma_graph_iff_lambda N
      ((actualSigmaPlancherel N).symm g) ((actualSigmaPlancherel N).symm k)

def actualSigmaDomainMemLp (N : ℕ) [NeZero N] (u : (actualGammaFriedrichs N).domain) :
    MemLp (actualSigmaLambdaProduct N (actualSigmaPlancherel N u)) 2
      (actualSigmaMeasure N) :=
  (actualGammaFriedrichs_sigma_domain_iff_lambda N u).mp u.property

def actualSigmaLambdaOutput (N : ℕ) [NeZero N] (u : (actualGammaFriedrichs N).domain) :
    ActualSigmaL2 N :=
  (actualSigmaDomainMemLp N u).toLp
    (actualSigmaLambdaProduct N (actualSigmaPlancherel N u))

theorem actualGammaFriedrichs_sigma_action_ae (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualSigmaPlancherel N (actualGammaFriedrichs N u)=ᵐ[actualSigmaMeasure N]
      actualSigmaLambdaProduct N (actualSigmaPlancherel N u) :=
  (actualGammaFriedrichs_sigma_graph_iff_lambda N u _).mp (LinearPMap.mem_graph _ u)

theorem actualGammaFriedrichs_sigma_action (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualSigmaPlancherel N (actualGammaFriedrichs N u)=actualSigmaLambdaOutput N u := by
  apply Lp.ext
  exact (actualGammaFriedrichs_sigma_action_ae N u).trans
    (actualSigmaDomainMemLp N u).coeFn_toLp.symm

theorem actualGammaFriedrichs_sigma_reconstruction (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N u=(actualSigmaPlancherel N).symm (actualSigmaLambdaOutput N u) := by
  apply (actualSigmaPlancherel N).injective
  rw [LinearIsometryEquiv.apply_symm_apply,actualGammaFriedrichs_sigma_action]

end
end ImbalancedChen.Part3.Gamma0ActualSigmaPlancherel20261025a
