import ImbalancedChen.Part3ActualResolventGlobalDiagonalization
import ImbalancedChen.Part3ActualResolventZeroAtomPushforward
import ImbalancedChen.Part3ActualFriedrichsSelfAdjointOperator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Exact unbounded multiplication graph and domain of the ACTUAL whole-space
Friedrichs operator, in the actual global scalar spectral coordinates.
The proved actual no-zero-atom theorem permits division by t almost
everywhere. The domain requires each lambda-times-coordinate to be L2
and their family to have finite lp norm. Both implications are proved.
Neither a domain characterization nor no-atom assertion is a premise.
This is a whole-space result, with no Gamma0 identification asserted.
-/

namespace ImbalancedChen.Part3.ActualFriedrichsGlobalMultiplicationGraph20261025a

noncomputable section

open Set MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
open ImbalancedChen.Part3.ActualResolventCyclicIntertwining20261025a
open ImbalancedChen.Part3.ActualResolventGlobalHilbertSum20261025a
open ImbalancedChen.Part3.ActualResolventGlobalDiagonalization20261025a
open ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a
open ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a

def lambdaProduct (ξ : ActualSpectralSum) (i : ActualSpectralIndex) :
    ResolventSpectrum → ℂ :=
  fun t => (spectralLambda t : ℂ) * (ξ i) t

/-- The true unbounded scalar multiplication relation, fiber by fiber. -/
def LambdaGraph (ξ η : ActualSpectralSum) : Prop :=
  ∀ i : ActualSpectralIndex,
    η i =ᵐ[scalarMeasure (i : HyperbolicL2)] lambdaProduct ξ i

private theorem scalar_resolvent_equation_iff (t : ResolventSpectrum)
    (ht : 0 < (t : ℝ)) (x y : ℂ) :
    (t : ℂ) * (x + y) = x ↔ y = (spectralLambda t : ℂ) * x := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hcast : (spectralLambda t : ℂ) = (t : ℂ)⁻¹ - 1 := by
    simp only [spectralLambda, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_one]
  rw [hcast]
  constructor
  · intro h
    have he := congrArg (fun z : ℂ => (t : ℂ)⁻¹ * z) h
    rw [← mul_assoc, inv_mul_cancel₀ htC, one_mul] at he
    calc
      y = (t : ℂ)⁻¹ * x - x := by linear_combination he
      _ = ((t : ℂ)⁻¹ - 1) * x := by ring
  · intro h
    rw [h]
    calc
      (t : ℂ) * (x + ((t : ℂ)⁻¹ - 1) * x) = (t : ℂ) * ((t : ℂ)⁻¹ * x) := by ring
      _ = x := by rw [← mul_assoc, mul_inv_cancel₀ htC, one_mul]

/-- The actual bounded resolvent equation is equivalent to the actual
unbounded coordinate equation. Actual scalar no-atom supplies ht internally. -/
theorem diagonal_resolvent_equation_iff (ξ η : ActualSpectralSum) :
    actualDiagonalResolvent (ξ + η) = ξ ↔ LambdaGraph ξ η := by
  constructor
  · intro h i
    have hi : coordinateMultiplier (i : HyperbolicL2) (ξ i + η i) = ξ i := by
      have he := congrArg (fun z : ActualSpectralSum => z i) h
      simpa only [actualDiagonalResolvent_apply, lp.coeFn_add, Pi.add_apply] using he
    have hm := coordinateMultiplier_coe_ae (i : HyperbolicL2) (ξ i + η i)
    rw [hi] at hm
    filter_upwards [hm, Lp.coeFn_add (ξ i) (η i),
      scalarMeasure_coordinate_pos_ae (i : HyperbolicL2)] with t hmt hadd ht
    have he : (t : ℂ) * ((ξ i) t + (η i) t) = (ξ i) t := by
      simpa only [hadd] using hmt.symm
    exact (scalar_resolvent_equation_iff t ht _ _).mp he
  · intro h
    apply lp.ext
    funext i
    change coordinateMultiplier (i : HyperbolicL2) (ξ i + η i) = ξ i
    apply Lp.ext
    filter_upwards [coordinateMultiplier_coe_ae (i : HyperbolicL2) (ξ i + η i),
      Lp.coeFn_add (ξ i) (η i), h i,
      scalarMeasure_coordinate_pos_ae (i : HyperbolicL2)] with t hm hadd hλ ht
    rw [hm, hadd]
    exact (scalar_resolvent_equation_iff t ht _ _).mpr hλ

/-- Exact graph transport in BOTH directions by the actual whole-H unitary. -/
theorem friedrichsGraph_unitary_iff (ξ η : ActualSpectralSum) :
    (actualSpectralUnitary ξ, actualSpectralUnitary η) ∈ friedrichsGraph ↔
      LambdaGraph ξ η := by
  rw [mem_friedrichsGraph_iff]
  change actualWeakResolvent (actualSpectralUnitary ξ + actualSpectralUnitary η) =
    actualSpectralUnitary ξ ↔ _
  rw [← map_add actualSpectralUnitary, ← actualSpectralUnitary_intertwine]
  exact actualSpectralUnitary.injective.eq_iff.trans (diagonal_resolvent_equation_iff ξ η)

theorem friedrichsGraph_spectral_iff (u v : HyperbolicL2) :
    (u, v) ∈ friedrichsGraph ↔
      LambdaGraph (actualSpectralUnitary.symm u) (actualSpectralUnitary.symm v) := by
  simpa only [actualSpectralUnitary.apply_symm_apply] using
    friedrichsGraph_unitary_iff (actualSpectralUnitary.symm u) (actualSpectralUnitary.symm v)

/-- An explicit domain, not an existence-of-operator-output condition:
each lambda product is L2 and the resulting L2 family has finite lp norm. -/
def LambdaDomain (ξ : ActualSpectralSum) : Prop :=
  ∃ h : ∀ i : ActualSpectralIndex,
      MemLp (lambdaProduct ξ i) 2 (scalarMeasure (i : HyperbolicL2)),
    Memℓp (fun i : ActualSpectralIndex => (h i).toLp (lambdaProduct ξ i)) 2

/-- Finite lp norm is equivalently summability of the squared fiber norms. -/
theorem lambdaDomain_iff_sum_norm_sq (ξ : ActualSpectralSum) :
    LambdaDomain ξ ↔
      ∃ h : ∀ i : ActualSpectralIndex,
          MemLp (lambdaProduct ξ i) 2 (scalarMeasure (i : HyperbolicL2)),
        Summable (fun i : ActualSpectralIndex => ‖(h i).toLp (lambdaProduct ξ i)‖ ^ 2) := by
  unfold LambdaDomain
  apply exists_congr
  intro h
  simpa using (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (f := fun i : ActualSpectralIndex => (h i).toLp (lambdaProduct ξ i)))

/-- The explicit norm domain gives an actual global output vector and,
conversely, every multiplication-graph output certifies exactly that domain. -/
theorem lambdaDomain_iff_exists_graph (ξ : ActualSpectralSum) :
    LambdaDomain ξ ↔ ∃ η : ActualSpectralSum, LambdaGraph ξ η := by
  constructor
  · rintro ⟨h, hsum⟩
    refine ⟨⟨fun i => (h i).toLp (lambdaProduct ξ i), hsum⟩, ?_⟩
    intro i
    exact (h i).coeFn_toLp
  · rintro ⟨η, hη⟩
    have h : ∀ i : ActualSpectralIndex,
        MemLp (lambdaProduct ξ i) 2 (scalarMeasure (i : HyperbolicL2)) := by
      intro i
      exact (memLp_congr_ae (hη i)).mp (η i).memLp
    refine ⟨h, ?_⟩
    have heq : (fun i : ActualSpectralIndex => (h i).toLp (lambdaProduct ξ i)) =
        (fun i : ActualSpectralIndex => η i) := by
      funext i
      apply Lp.ext
      exact (h i).coeFn_toLp.trans (hη i).symm
    rw [heq]
    exact lp.memℓp η

/-- Exact actual Friedrichs domain: no hDomain, hNoAtom or output-supplier
premise. The original native LinearPMap domain is used unchanged. -/
theorem actualFriedrichs_domain_spectral_iff (u : HyperbolicL2) :
    u ∈ actualFriedrichs.domain ↔ LambdaDomain (actualSpectralUnitary.symm u) := by
  rw [LinearPMap.mem_domain_iff, lambdaDomain_iff_exists_graph]
  constructor
  · rintro ⟨v, hv⟩
    rw [actualFriedrichs_graph_eq] at hv
    exact ⟨actualSpectralUnitary.symm v, (friedrichsGraph_spectral_iff u v).mp hv⟩
  · rintro ⟨η, hη⟩
    refine ⟨actualSpectralUnitary η, ?_⟩
    rw [actualFriedrichs_graph_eq]
    apply (friedrichsGraph_spectral_iff u (actualSpectralUnitary η)).mpr
    simpa only [actualSpectralUnitary.symm_apply_apply] using hη

/-- Native graph membership is exactly fiberwise multiplication by 1/t-1. -/
theorem actualFriedrichs_graph_spectral_iff (u v : HyperbolicL2) :
    (u, v) ∈ actualFriedrichs.graph ↔
      ∀ i : ActualSpectralIndex,
        (actualSpectralUnitary.symm v) i =ᵐ[scalarMeasure (i : HyperbolicL2)]
          (fun t : ResolventSpectrum =>
            (spectralLambda t : ℂ) * ((actualSpectralUnitary.symm u) i) t) := by
  rw [actualFriedrichs_graph_eq]
  exact friedrichsGraph_spectral_iff u v

end
end ImbalancedChen.Part3.ActualFriedrichsGlobalMultiplicationGraph20261025a
