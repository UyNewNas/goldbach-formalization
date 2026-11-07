import ImbalancedChen.Part3Gamma0CanonicalWeightedNormJoin
import ImbalancedChen.Part3Gamma0ReducedContinuousApproximation

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

DENSITY of the actual smooth effective-Gamma0 Poincare family in the
ACTUAL quotient Hilbert space for its canonical carrier-pushforward measure.

The proof goes through the actual reduced representative carrier: genuine
compact-continuous Lp approximation, actual open-carrier finite localization,
support-preserving y^-1 weighted tensor approximation, literal finite smooth
tensor rendering, exact effective Poincare reconstruction and the actual
quotient/carrier isometry. No whole-plane density is relabeled quotient
density; no compact-interior approximation, norm or dense-range conclusion
is supplied as a premise. Only the actual level N and the target vector
and tolerance are inputs. No spectral decomposition is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0SmoothQuotientCoreDensity20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreResolventCoercivity20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.Gamma0QuotientL2Equivalence20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a
open ImbalancedChen.Part3.Gamma0CompactWeightedTensorApproximation20261025a
open ImbalancedChen.Part3.Gamma0SmoothTensorSpanRendering20261025a
open ImbalancedChen.Part3.Gamma0CompactUpperChartExtension20261025a
open ImbalancedChen.Part3.Gamma0CanonicalWeightedNormJoin20261025a
open ImbalancedChen.Part3.Gamma0ReducedContinuousApproximation20261025a

/-- The actual finite smooth Poincare family, not a whole-plane tensor
domain or an arbitrary supplied dense subset of a quotient. -/
def smoothQuotientCore (N : ℕ) [NeZero N] :
    Set (Lp ℂ 2 (carrierPushforward N)) :=
  {v | ∃ (n : ℕ) (T : Fin n→SmoothCompactTensor),
    v=smoothQuotientPoincareL2 N Finset.univ T}

/-- Quantitative actual quotient-core approximation. Every approximating
finite smooth seed and every carrier/norm identification is constructed. -/
theorem exists_smoothQuotientCore_near (N : ℕ) [NeZero N]
    (F : Lp ℂ 2 (carrierPushforward N)) (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ v∈smoothQuotientCore N,dist v F<epsilon := by
  let g := quotientL2ReducedCarrierEquiv N F
  obtain ⟨f,hfcont,hfcompact,hfsupp,hfr,hfnear⟩ :=
    exists_continuous_compact_inside_reduced_approx N g (epsilon/2) (half_pos hepsilon)
  have hfc : Continuous (extendUpper f) := extendUpper_continuous f hfcont hfcompact
  have hfcc : HasCompactSupport (extendUpper f) := extendUpper_hasCompactSupport f hfcompact
  have hfinside := extendUpper_support_inside_actual_chart N f hfcompact hfsupp
  obtain ⟨H,hHspan,_hHcompact,hHinside,herror⟩ :=
    exists_compact_interior_weighted_tensor_approx N (extendUpper f) hfc hfcc hfinside
      (epsilon/2) (half_pos hepsilon)
  obtain ⟨n,T,hHT⟩ := exists_finite_smooth_tensor_representation hHspan
  have hTinside : ∀ p∈tsupport (smoothChartFinite T),
      0<p.2 ∧ Gamma0CompactTensorPoincareC2Core20261025a.chartLift p∈
        Gamma0CarrierAESection20261025a.reducedCarrier N := by
    rw [← hHT]
    exact hHinside
  have hseedSupp := finite_seed_support_inside_of_chart_support N T hTinside
  let seed := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hfH : MemLp f 2 (volume : Measure UpperHalfPlane) :=
    hfcont.memLp_of_hasCompactSupport hfcompact
  have hseedH : MemLp seed 2 (volume : Measure UpperHalfPlane) :=
    finiteCoreFunction_memLp Finset.univ (fun i => (T i).toCompactTensor)
  have hseedR := reducedSeed_memLp_two N Finset.univ
    (fun i => (T i).toCompactTensor) hseedSupp
  have hext : extendUpper seed=smoothChartFinite T :=
    extendUpper_finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hnearSeed : dist (reducedFunctionL2 N f hfr)
      (reducedSeedL2 N Finset.univ (fun i => (T i).toCompactTensor) hseedSupp)<epsilon/2 := by
    calc
      _ ≤ dist (hfH.toLp f) (hseedH.toLp seed) :=
        reduced_toLp_dist_le_canonical N f seed hfH hseedH hfr hseedR
      _ = (eLpNorm (Gamma0LocalWeightedTensorApproximation20261025a.divideByHeight
          (extendUpper f-H)) 2 (volume : Measure (ℝ×ℝ))).toReal := by
        rw [canonical_toLp_dist_eq_weighted f seed hfH hseedH,hext,← hHT]
      _ < epsilon/2 := ENNReal.toReal_lt_of_lt_ofReal herror
  have htotal : dist g
      (reducedSeedL2 N Finset.univ (fun i => (T i).toCompactTensor) hseedSupp)<epsilon := by
    have hh := dist_triangle g (reducedFunctionL2 N f hfr)
      (reducedSeedL2 N Finset.univ (fun i => (T i).toCompactTensor) hseedSupp)
    linarith
  refine ⟨smoothQuotientPoincareL2 N Finset.univ T,⟨n,T,rfl⟩,?_⟩
  change dist (quotientTensorPoincareL2 N Finset.univ (fun i => (T i).toCompactTensor)) F<epsilon
  rw [quotient_distance_eq_reduced_seed_distance N Finset.univ
    (fun i => (T i).toCompactTensor) hseedSupp F,dist_comm]
  exact htotal

/-- The actual quotient smooth Poincare core is dense, with no density
or approximation supplier among the theorem's hypotheses. -/
theorem smoothQuotientCore_dense (N : ℕ) [NeZero N] : Dense (smoothQuotientCore N) := by
  apply Metric.dense_iff.mpr
  intro F epsilon hepsilon
  obtain ⟨v,hv,hdist⟩ := exists_smoothQuotientCore_near N F epsilon hepsilon
  exact ⟨v,Metric.mem_ball.mpr hdist,hv⟩

end
end ImbalancedChen.Part3.Gamma0SmoothQuotientCoreDensity20261025a
