import ImbalancedChen.P2U8QuadratureTendsto

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A rational inner certificate for the literal original U8 harmonic integral.
The first-prime cutoff is 417/5000, the inclusive second-prime wall is 1/3,
and the strict moving wall is x+2y<1. A cell is included only when its
UPPER corner passes that wall; no boundary-crossing cell is a lower cell.
Closed coordinate walls are aggregated using the already proved product
measure null-wall and half-open disjointness results.

The final rational enclosure combines the independent inner sum with the
proved upper quadrature error. No numerical endpoint is evaluated or
asserted. In particular the original lowerU8AtK0/K0 comparison remains a
separate finite rational certificate, not a premise of the geometric proof.
-/
namespace ImbalancedChen.P5U8OriginalInnerCertificateSourceOnly

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators
open Classical
open P2NegativeDomainCover P2U8DirectedBoxEnclosure P2U8UniformRationalCover
open P2U8UniformCoverConvergence P2U8QuadratureTendsto

/-- A strict rational gate for whole closed cells in the actual domain. -/
def innerCells (M : ℕ) : Finset (Fin M × Fin M) :=
  Finset.univ.filter fun ij => (meshBox M ij).xu + 2 * (meshBox M ij).yu < 1

def innerUnion (M : ℕ) : Set Point := closedUnion M (innerCells M)

theorem innerCells_subset_selected {M : ℕ} (hM : 0 < M) :
    innerCells M ⊆ selected M := by
  intro ij hij
  have hg := (Finset.mem_filter.mp hij).2
  have hv := meshBox_valid hM ij
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by linarith only [hg, hv.2.1, hv.2.2.2.1]⟩

/-- Whole-cell inclusion uses the actual strict upper argument wall. -/
theorem innerCell_subset_eighthDomain {M : ℕ} (hM : 0 < M)
    {ij : Fin M × Fin M} (hij : ij ∈ innerCells M) :
    (meshBox M ij).region ⊆ eighthDomain := by
  intro x hx
  obtain ⟨hxl, hxu, hyl, hyu⟩ := Box.mem_region.mp hx
  have hrect := Box.mem_region.mp (mesh_subset_rectangle hM ij hx)
  have ha : (417 / 5000 : ℝ) ≤ x 0 := by
    simpa only [rectangleBox, alpha] using hrect.1
  have hc : (1 / 3 : ℝ) ≤ x 1 := by
    simpa only [rectangleBox, cubeWall] using hrect.2.2.1
  have hgQ := (Finset.mem_filter.mp hij).2
  have hgR : ((meshBox M ij).xu : ℝ) + 2 * (meshBox M ij).yu < 1 := by
    exact_mod_cast hgQ
  have hgate : x 0 + 2 * x 1 < 1 := by linarith only [hxu, hyu, hgR]
  have hxthird : x 0 < (1 / 3 : ℝ) := by linarith only [hc, hgate]
  have hyhalf : x 1 < (1 / 2 : ℝ) := by linarith only [ha, hgate]
  refine ⟨mem_logPrimeBox.mpr ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨ha, by linarith only [hxthird]⟩
    · exact ⟨by linarith only [hc], hyhalf⟩
  · change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1
    exact ⟨hxthird, hc, hgate⟩

theorem innerUnion_subset_eighthDomain {M : ℕ} (hM : 0 < M) :
    innerUnion M ⊆ eighthDomain := by
  intro x hx
  obtain ⟨ij, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hij, hx⟩ := mem_iUnion.mp hx
  exact innerCell_subset_eighthDomain hM hij hx

theorem measurableSet_innerUnion (M : ℕ) : MeasurableSet (innerUnion M) := by
  exact Finset.measurableSet_biUnion (innerCells M) (fun _ _ => measurableSet_Icc)

theorem eighthDensity_nonneg {x : Point} (hx : x ∈ eighthDomain) :
    0 ≤ eighthDensity x := by
  have hx0 := mem_logPrimeBox.mp hx.1 (0 : Fin 2)
  have hr := hx.2
  change x 0 < 1 / 3 ∧ 1 / 3 ≤ x 1 ∧ x 0 + 2 * x 1 < 1 at hr
  have hp : 0 ≤ x 0 := (by norm_num : (0 : ℝ) ≤ 417 / 5000).trans hx0.1
  have hq : 0 ≤ x 1 := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans hr.2.1
  have hgap : 0 ≤ 1 - x 0 - x 1 := by linarith only [hr.2.2, hq]
  rw [density_eq_reciprocal]
  exact div_nonneg (by norm_num) (mul_nonneg (mul_nonneg hp hq) hgap)

theorem innerUnion_integral_le_original {M : ℕ} (hM : 0 < M) :
    (∫ x in innerUnion M, eighthDensity x) ≤ currentChenUpsilon8HarmonicIntegral := by
  have hsub := innerUnion_subset_eighthDomain hM
  have hleft : Integrable ((innerUnion M).indicator eighthDensity) :=
    (integrableOn_eighthDensity.mono_set hsub).integrable_indicator
      (measurableSet_innerUnion M)
  have hright : Integrable (eighthDomain.indicator eighthDensity) :=
    integrableOn_eighthDensity.integrable_indicator measurableSet_eighthDomain
  have hpoint (x : Point) :
      (innerUnion M).indicator eighthDensity x ≤ eighthDomain.indicator eighthDensity x := by
    by_cases hx : x ∈ innerUnion M
    · rw [indicator_of_mem hx, indicator_of_mem (hsub hx)]
    · rw [indicator_of_notMem hx]
      by_cases hD : x ∈ eighthDomain
      · rw [indicator_of_mem hD]
        exact eighthDensity_nonneg hD
      · rw [indicator_of_notMem hD]
  have hmono := integral_mono hleft hright hpoint
  rw [integral_indicator (measurableSet_innerUnion M),
    integral_indicator measurableSet_eighthDomain] at hmono
  exact hmono

/-- Pure rational data: lower corner enclosure times exact whole-cell area. -/
def innerLower (M : ℕ) : ℚ :=
  ∑ ij ∈ innerCells M, (meshBox M ij).lower * (meshBox M ij).area

/-- Genuine lower certificate for the literal J8, with no integral premise. -/
theorem innerLower_le_original (M : ℕ) (hM : 0 < M) :
    (innerLower M : ℝ) ≤ currentChenUpsilon8HarmonicIntegral := by
  calc
    (innerLower M : ℝ) =
        ∑ ij ∈ innerCells M, (((meshBox M ij).lower * (meshBox M ij).area : ℚ) : ℝ) := by
      unfold innerLower
      push_cast
    _ ≤ ∑ ij ∈ innerCells M, ∫ x in (meshBox M ij).region, eighthDensity x := by
      exact Finset.sum_le_sum (fun ij _ => (Box.integral_density_enclosure (meshBox_valid hM ij)).1)
    _ = ∫ x in innerUnion M, eighthDensity x := by
      exact (closed_mesh_integral_aggregation hM (innerCells M) eighthDensity
        (fun ij _ => Box.integrable_density (meshBox_valid hM ij))).symm
    _ ≤ currentChenUpsilon8HarmonicIntegral := innerUnion_integral_le_original hM

/-- The rational lower endpoint obtained from the proved quadrature error. -/
def errorLower (M : ℕ) : ℚ := uniformUpper M - errorNumerator / (M : ℚ)

theorem errorLower_le_original (M : ℕ) (hM : 0 < M) :
    (errorLower M : ℝ) ≤ currentChenUpsilon8HarmonicIntegral := by
  have herror := (uniformUpper_error M hM).2
  simp only [errorLower, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast]
  linarith only [herror]

/-- Independent inner data may improve the rigorous upper-minus-error floor. -/
def certifiedLower (M : ℕ) : ℚ := max (innerLower M) (errorLower M)

theorem certifiedLower_le_original (M : ℕ) (hM : 0 < M) :
    (certifiedLower M : ℝ) ≤ currentChenUpsilon8HarmonicIntegral := by
  rw [certifiedLower, Rat.cast_max]
  exact max_le (innerLower_le_original M hM) (errorLower_le_original M hM)

theorem original_rational_enclosure (M : ℕ) (hM : 0 < M) :
    (certifiedLower M : ℝ) ≤ currentChenUpsilon8HarmonicIntegral ∧
      currentChenUpsilon8HarmonicIntegral ≤ (uniformUpper M : ℝ) :=
  ⟨certifiedLower_le_original M hM, eighthIntegral_le_uniformUpper M hM⟩

/-- The lower certificate is also complete under refinement, with the same
explicit O(1/M) reserve; no special selected endpoint is presumed. -/
theorem certifiedLower_error (M : ℕ) (hM : 0 < M) :
    0 ≤ currentChenUpsilon8HarmonicIntegral - (certifiedLower M : ℝ) ∧
      currentChenUpsilon8HarmonicIntegral - (certifiedLower M : ℝ) ≤
        (errorNumerator : ℝ) / (M : ℝ) := by
  have hup := eighthIntegral_le_uniformUpper M hM
  have hfloorQ : errorLower M ≤ certifiedLower M := le_max_right _ _
  have hfloorR : (uniformUpper M : ℝ) - (errorNumerator : ℝ) / (M : ℝ) ≤
      (certifiedLower M : ℝ) := by
    have hcast : (errorLower M : ℝ) ≤ (certifiedLower M : ℝ) := by exact_mod_cast hfloorQ
    simpa only [errorLower, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast] using hcast
  exact ⟨sub_nonneg.mpr (certifiedLower_le_original M hM), by linarith only [hup, hfloorR]⟩

theorem tendsto_certifiedLower :
    Tendsto (fun M : ℕ => (certifiedLower M : ℝ)) atTop
      (𝓝 currentChenUpsilon8HarmonicIntegral) := by
  have herror : Tendsto (fun M : ℕ => (errorNumerator : ℝ) / (M : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [herror.eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℕ)] with M hsmall hM
  have hb := certifiedLower_error M (by omega)
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hb.1]
  exact hb.2.trans_lt hsmall

def lowerEndpointCheck (M : ℕ) (q : ℚ) : Bool := decide (q ≤ certifiedLower M)

theorem lowerEndpointCheck_sound (M : ℕ) (hM : 0 < M) (q : ℚ)
    (hcheck : lowerEndpointCheck M q = true) :
    (q : ℝ) ≤ currentChenUpsilon8HarmonicIntegral := by
  have hq : q ≤ certifiedLower M := of_decide_eq_true hcheck
  have hqR : (q : ℝ) ≤ (certifiedLower M : ℝ) := by exact_mod_cast hq
  exact hqR.trans (certifiedLower_le_original M hM)

/-- Existence for every strictly separated lower endpoint. The original
Simpson endpoint's separation is intentionally not asserted. -/
theorem exists_finite_lowerEndpointCheck (q : ℚ)
    (hq : (q : ℝ) < currentChenUpsilon8HarmonicIntegral) :
    ∃ M : ℕ, 0 < M ∧ lowerEndpointCheck M q = true := by
  have hevent : ∀ᶠ M : ℕ in atTop, (q : ℝ) < (certifiedLower M : ℝ) :=
    tendsto_certifiedLower.eventually (lt_mem_nhds hq)
  obtain ⟨M, hM, hlt⟩ := ((eventually_ge_atTop (1 : ℕ)).and hevent).exists
  refine ⟨M, by omega, ?_⟩
  change decide (q ≤ certifiedLower M) = true
  apply decide_eq_true_iff.mpr
  exact_mod_cast hlt.le

end
end ImbalancedChen.P5U8OriginalInnerCertificateSourceOnly
