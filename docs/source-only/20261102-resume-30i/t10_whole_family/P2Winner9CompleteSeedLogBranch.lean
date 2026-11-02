import ImbalancedChen.P2Winner9CompleteSeedT10Q6
import ImbalancedChen.P2DegreeSixLogGapSoundness
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL factorwise log6/exp3 branch on every physical source row.
This is necessary because the selected source max cannot be replaced by
Q6 raw alone. The independent polynomial pullback proves its real moments.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedLogBranch
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9SelectedAllMixedMoments
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9CompleteSeedMomentDecoder
open ImbalancedChen.P2Winner9CompleteSeedT10Q6
open ImbalancedChen.P2DegreeSixLogGapSoundnessSourceOnly
open ImbalancedChen.P2PositiveAffineSimplexLogJensenSourceOnly

local notation "muQ" => P2Winner9CompleteSeedMomentDecoder.means

def top (i : RowIndex) (j : Fin 10) : ℚ :=
  (List.ofFn (fun k : Fin 9 => rawFactor (physicalVertices i) k j)).foldl max 0

def logY (i : RowIndex) (j : Fin 10) : Ambient → ℝ :=
  scaledDeviation (top i j : ℝ) (physicalFactor j)

def logYPoly (i : RowIndex) (j : Fin 10) : Poly :=
  affinePoly (fun k => 1 - rawFactor (physicalVertices i) k j / top i j)

def logPower (i : RowIndex) (j : Fin 10) (k : ℕ) : ℚ :=
  polynomialMoment (gapPoly i * (logYPoly i j)^k) / polynomialMoment (gapPoly i)

def logGap (i : RowIndex) (j : Fin 10) : ℚ :=
  ∑ k ∈ Finset.range 5, (logPower i j (k + 2) - (logPower i j 1)^(k + 2)) / (k + 2)

def savedGap (i : RowIndex) (j : Fin 10) : ℚ :=
  ((entry i).logGapFloors[j.val]! : ℚ) / q80

def cubicQ (x : ℚ) : ℚ := 1 + x * (1 + x * (1 / 2 + x / 6))

/-- Exact original source field protocol, checked against independent sparse
polynomial moments. The former logSelected maximum with parent Jensen is
already included in this floor (the cubic is >=1). No integral appears. -/
structure LogFacts (i : RowIndex) : Prop where
  top_pos : ∀ j : Fin 10, 0 < top i j
  top_bound : ∀ j : Fin 10, ∀ k : Fin 9, rawFactor (physicalVertices i) k j ≤ top i j
  gaps : ∀ j : Fin 10, FloorAt q80 (logGap i j) ((entry i).logGapFloors[j.val]!)
  parent : FloorAt q96 (entry i).jensen (entry i).parentJensenFloor
  selected : FloorAt q96 ((entry i).jensen * cubicQ (∑ j : Fin 10, savedGap i j))
    (entry i).logSelected

/-- Closed full-family source proof bodies, not executed in this task. -/
theorem all_log_facts : ∀ i : RowIndex, LogFacts i := by
  intro i
  constructor <;> revert i <;> simp only [FloorAt] <;> decide +kernel

theorem factor_le_top (i : RowIndex) (j : Fin 10) {z : Ambient}
    (hz : z ∈ actualSupport i) : physicalFactor j z ≤ (top i j : ℝ) := by
  rcases hz with ⟨x, hx, rfl⟩
  rw [physicalFactor_vertexMap]
  apply affine_upper hx
  intro k
  rw [← rawFactor_cast]
  exact_mod_cast (all_log_facts i).top_bound j k

theorem logY_continuous (i : RowIndex) (j : Fin 10) : Continuous (logY i j) :=
  continuous_const.sub ((continuous_physicalFactor j).div_const _)

theorem factor_log_continuousOn (i : RowIndex) (j : Fin 10) :
    ContinuousOn (fun z => Real.log (physicalFactor j z)) (actualSupport i) :=
  (continuous_physicalFactor j).continuousOn.log
    (fun z hz => ((all_actual_support_positive i hz).2 j).2.ne')

theorem logY_range (i : RowIndex) (j : Fin 10) {z : Ambient}
    (hz : z ∈ actualSupport i) :
    logY i j z ∈ Icc (0 : ℝ) (1 - (minimumFactor j : ℝ) / (top i j : ℝ)) ∧
      1 - (minimumFactor j : ℝ) / (top i j : ℝ) < 1 := by
  apply scaledDeviation_range
    (by exact_mod_cast (all_log_facts i).top_pos j)
    (by exact_mod_cast (original_vertex_analytic_guards.1 j).1)
  exact ⟨((all_actual_support_positive i hz).2 j).1, factor_le_top i j hz⟩

theorem log_q_lt_one (i : RowIndex) (j : Fin 10) :
    1 - (minimumFactor j : ℝ) / (top i j : ℝ) < 1 := by
  have ht : (0 : ℝ) < (top i j : ℝ) := by exact_mod_cast (all_log_facts i).top_pos j
  have hl : (0 : ℝ) < (minimumFactor j : ℝ) :=
    by exact_mod_cast (original_vertex_analytic_guards.1 j).1
  linarith [div_pos hl ht]

theorem logYPoly_eval (i : RowIndex) (j : Fin 10) (x : Ambient) :
    (logYPoly i j).eval₂ (Rat.castHom ℝ) x =
      logY i j (vertexMap (realVertices (physicalVertices i)) x) := by
  rw [logYPoly, affinePoly_eval]
  simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, rawFactor_cast]
  rw [logY, scaledDeviation, physicalFactor_vertexMap]
  rw [affine_sub, affine_constant, affine_div]

/-- All actual degree-six moments on the same physical gap probability. -/
theorem integral_logY_pow (i : RowIndex) (j : Fin 10) (k : ℕ) :
    (∫ z, (logY i j z)^k ∂ν i) = (logPower i j k : ℝ) := by
  rw [weighted_integral]
  apply measured_polynomial i ((logYPoly i j)^k)
  intro x
  rw [MvPolynomial.eval₂_pow, logYPoly_eval]

theorem gapSix_identity (i : RowIndex) (j : Fin 10) :
    gapSix (ν i) (logY i j) = (logGap i j : ℝ) := by
  have h1 : (∫ z, logY i j z ∂ν i) = (logPower i j 1 : ℝ) :=
    by simpa only [pow_one] using integral_logY_pow i j 1
  simp only [gapSix, integral_logY_pow, h1]
  simp [logGap]

theorem factor_probability_mean (i : RowIndex) (j : Fin 10) :
    (∫ z, physicalFactor j z ∂ν i) = (muQ i j : ℝ) := by
  rw [weighted_integral]
  exact actual_factor_mean i j

theorem savedGap_nonneg (i : RowIndex) (j : Fin 10) : (0 : ℝ) ≤ (savedGap i j : ℝ) := by
  unfold savedGap q80
  positivity

/-- Exact source log-gap floors are transported to real measured log bounds;
this is not a source-row enclosure input. -/
theorem actual_log_bound (i : RowIndex) (j : Fin 10) :
    (∫ z in actualSupport i, physicalGap z * Real.log (physicalFactor j z)) / gapMass i ≤
      Real.log (muQ i j : ℝ) - (savedGap i j : ℝ) := by
  have h := probability_factor_log_bound (ν i) (top i j : ℝ)
    (by exact_mod_cast (all_log_facts i).top_pos j) (physicalFactor j)
    (log_q_lt_one i j)
    ((ν_support i).mono (fun z hz => (logY_range i j hz).1))
    ((ν_support i).mono (fun z hz => ((all_actual_support_positive i hz).2 j).2))
    (weighted_integrable i (continuous_physicalFactor j).continuousOn)
    (weighted_integrable i (factor_log_continuousOn i j))
    (fun k _ _ => weighted_integrable i ((logY_continuous i j).pow k).continuousOn)
  change (∫ z, Real.log (physicalFactor j z) ∂ν i) ≤
    Real.log (∫ z, physicalFactor j z ∂ν i) - gapSix (ν i) (logY i j) at h
  rw [factor_probability_mean, gapSix_identity, weighted_integral] at h
  have hf : (savedGap i j : ℝ) ≤ (logGap i j : ℝ) := by
    exact_mod_cast ((all_log_facts i).gaps j).1
  linarith

/-- The original factorwise log6/exp3 physical bound on every actual row. -/
theorem actual_log_cubic_enclosure (i : RowIndex) :
    ((entry i).jensen : ℝ) * cubicCorrection (∑ j : Fin 10, (savedGap i j : ℝ)) ≤
      ∫ z in actualSupport i, physicalUpperIntegrand z := by
  have hLog (j : Fin 10) : Integrable
      (fun z => physicalGap z * Real.log (physicalFactor j z)) (μ i) :=
    (continuous_physicalGap.continuousOn.mul (factor_log_continuousOn i j)).integrableOn_compact
      (all_actual_support_compact i)
  have hRecip : Integrable (fun z => physicalGap z / ∏ j : Fin 10, physicalFactor j z) (μ i) := by
    have hprod : Continuous (fun z => ∏ j : Fin 10, physicalFactor j z) := by
      have hc := continuous_physicalFactor
      fun_prop
    apply ContinuousOn.integrableOn_compact _ (all_actual_support_compact i)
    exact continuous_physicalGap.continuousOn.div hprod.continuousOn (fun z hz =>
      (Finset.prod_pos (fun j _ => ((all_actual_support_positive i hz).2 j).2)).ne')
  have h := weighted_log_gap_cubic_lower_four (μ i) physicalGap physicalFactor
    (fun j => (muQ i j : ℝ)) (fun j => (savedGap i j : ℝ))
    continuous_physicalGap.measurable (gap_integrable i) (gap_nonneg_ae i) (gapMass_pos i)
    ((μ_support i).mono (fun z hz j => ((all_actual_support_positive i hz).2 j).2))
    hLog hRecip (fun j => by exact_mod_cast all_original_means_positive i j)
    (savedGap_nonneg i) (actual_log_bound i)
  rw [actual_Jensen_factor]
  exact h

theorem all_original_log_floors (i : RowIndex) :
    ((entry i).logSelected : ℝ) / (q96 : ℝ) ≤
      ∫ z in actualSupport i, physicalUpperIntegrand z := by
  have hf : ((entry i).logSelected : ℝ) / (q96 : ℝ) ≤
      ((entry i).jensen : ℝ) * cubicCorrection (∑ j : Fin 10, (savedGap i j : ℝ)) := by
    have h := (all_log_facts i).selected.1
    have hc := (show (((entry i).logSelected : ℚ) / q96 : ℝ) ≤
      (((entry i).jensen * cubicQ (∑ j : Fin 10, savedGap i j) : ℚ) : ℝ) from
      by exact_mod_cast h)
    simpa [cubicQ, cubicCorrection] using hc
  exact hf.trans (actual_log_cubic_enclosure i)

end
end ImbalancedChen.P2Winner9CompleteSeedLogBranch

