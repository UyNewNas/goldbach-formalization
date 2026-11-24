import ImbalancedChen.P2Winner9RawFirstMomentDecoder
import ImbalancedChen.P2Winner9RationalSimplexCaps
import ImbalancedChen.P2Winner9PhysicalQ6Probability

/-! The exact T10 and Q6 enclosure for an arbitrary rational physical row. -/

namespace ImbalancedChen.P2Winner9GenericRowIntegral

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SelectedRowRealJacobian (RationalVertices realVertices sourceSupport
  sourceSupport_compact sourceSupport_measurable source_integral)
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix)
open P2Winner9SelectedRowIntegerScales (rawGap rawFactor rawP rawGap_cast rawFactor_cast
  rawP_cast real_vertex_arrays VertexNormalization)
open P2Winner9SelectedRowAnalyticCaps (affine_lower affine_upper continuous_physicalGap
  continuous_physicalFactor)
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation
open P2Winner9BarycentricMixedDegreeOne
open P2Winner9PowerMoment
open P2Winner9MixedPowerSource
open P2Winner9MixedPowerMoment
open P2Winner9CurvatureFullExactAssembly (SimplexData value t10)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9MixedDegreeSixExactAssembly (q6 total)
open P2Winner9RationalSimplexData (Input toSimplexData)
open P2Winner9RationalSimplexCaps (upper lower transverseUpper)
open P2Winner9RawFirstMomentDecoder
open P2Winner9CanonicalPolynomialMoment
open P2Winner9FastMomentDecoder (weighted_polynomial_cast)
open P2Winner9ReciprocalProduct (reciprocal_product_quadratic)
open P2Winner9PhysicalQ6Probability (binomial6 binomial6_minorant)
open P2Winner9TaylorCorrection (actual_T10_identity_range)
open P2Winner9T10TailJensen (probability_T10_gap)
open P2PositiveAffineSimplexLogJensenSourceOnly

/-- The rational hypotheses needed for the enclosure on the original
ordered vertex array. The last two fields are exact first-moment and
normalization checks. -/
structure Row where
  vertices : RationalVertices
  means : Fin 10 → ℚ
  jensen : ℚ
  det_ne : (edgeMatrix vertices).det ≠ 0
  gap_nonneg : ∀ i, 0 ≤ rawGap vertices i
  gap_sum_pos : 0 < ∑ i, rawGap vertices i
  factor_pos : ∀ i j, 0 < rawFactor vertices i j
  means_pos : ∀ j, 0 < means j
  p_mean : affineMeanQ (rawGap vertices) (rawP vertices means) = 1
  jensen_eq : jensen =
    4 * |(edgeMatrix vertices).det| * gapMomentQ (rawGap vertices) /
      ∏ j : Fin 10, means j

/-- The ten exact factor means imply the exact mean-one identity for P. -/
theorem p_mean_of_factor_means (v : RationalVertices) (means : Fin 10 → ℚ)
    (hgap : 0 < ∑ i, rawGap v i) (hm : ∀ j, 0 < means j)
    (h : ∀ j, affineMeanQ (rawGap v) (fun i => rawFactor v i j) = means j) :
    affineMeanQ (rawGap v) (rawP v means) = 1 := by
  let G := ∑ i, rawGap v i
  let a (i : Fin 9) (j : Fin 10) := rawFactor v i j / means j
  have hG : 0 < 10 * G := mul_pos (by norm_num) hgap
  have hnormalized (j : Fin 10) :
      G * (∑ i, a i j) + ∑ i, rawGap v i * a i j = 10 * G := by
    have hj := (div_eq_iff hG.ne').mp (h j)
    change G * (∑ i, rawFactor v i j) + ∑ i, rawGap v i * rawFactor v i j =
      means j * (10 * G) at hj
    simp only [a]
    simp_rw [← Finset.sum_div, ← mul_div_assoc, ← Finset.sum_div, ← add_div]
    rw [hj, mul_comm (means j), mul_div_cancel_right₀ _ (hm j).ne']
  have hs₁ : (∑ i, ∑ j, a i j) = ∑ j, ∑ i, a i j := Finset.sum_comm
  have hs₂ : (∑ i, rawGap v i * ∑ j, a i j) = ∑ j, ∑ i, rawGap v i * a i j := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  change ((G * (∑ i, (∑ j, a i j) / 10) +
    ∑ i, rawGap v i * ((∑ j, a i j) / 10)) / (10 * G)) = 1
  apply (div_eq_iff hG.ne').2
  calc
    _ = (∑ j, (G * (∑ i, a i j) + ∑ i, rawGap v i * a i j)) / 10 := by
      simp_rw [← Finset.sum_div, ← mul_div_assoc, ← Finset.sum_div, ← add_div]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs₁, hs₂]
    _ = 1 * (10 * G) := by simp [hnormalized]

theorem rawP_pos (r : Row) (i : Fin 9) : 0 < rawP r.vertices r.means i := by
  unfold rawP
  exact div_pos (Finset.sum_pos (fun j _ => div_pos (r.factor_pos i j) (r.means_pos j))
    Finset.univ_nonempty) (by norm_num)

theorem jensen_nonneg (r : Row) : 0 ≤ r.jensen := by
  rw [r.jensen_eq]
  have hg := gapMomentQ_pos _ r.gap_sum_pos
  have hp : 0 < ∏ j : Fin 10, r.means j := Finset.prod_pos (fun j _ => r.means_pos j)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hg.le) hp.le

/-- Executable denominator and cap construction for a certified row. -/
def input (r : Row) : Input :=
  P2Winner9RationalSimplexCaps.ofPhysicalVertices r.vertices r.means r.jensen
    r.gap_nonneg r.gap_sum_pos (rawP_pos r 0) (jensen_nonneg r)

def data (r : Row) : SimplexData := toSimplexData (input r)

def gapScale (r : Row) : ℕ := P2Winner9RationalSimplexData.gapDen (input r)

theorem row_vertex_normalization (r : Row) :
    VertexNormalization r.vertices r.means (upper r.vertices r.means) (data r) (gapScale r) :=
  P2Winner9RationalSimplexCaps.ofPhysicalVertices_normalization ..

noncomputable section

def jacobian (r : Row) : ℝ := |((edgeMatrix r.vertices).det : ℝ)|

def gapMass (r : Row) : ℝ := ∫ z in sourceSupport r.vertices, physicalGap z

theorem jacobian_pos (r : Row) : 0 < jacobian r := by
  apply abs_pos.mpr
  exact_mod_cast r.det_ne

private theorem gapMass_typed (r : Row) :
    gapMass r = (jacobian r / (gapScale r : ℝ)) * actualGapMass (data r) := by
  have hg := (real_vertex_arrays r.vertices r.means (upper r.vertices r.means)
    (data r) (gapScale r) (row_vertex_normalization r)).1
  rw [gapMass, source_integral r.vertices r.det_ne]
  simp only [physicalGap_vertexMap, hg, affine_div]
  have he (x : Ambient) : affine (gapVertices (data r)) x / (gapScale r : ℝ) =
      (1 / (gapScale r : ℝ)) * affine (gapVertices (data r)) x := by ring
  simp_rw [he]
  rw [integral_const_mul]
  change jacobian r * ((1 / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  ring

theorem gapMass_eq (r : Row) :
    gapMass r = jacobian r * (gapMomentQ (rawGap r.vertices) : ℝ) := by
  rw [gapMass, source_integral r.vertices r.det_ne]
  have he (x : Ambient) :
      physicalGap (vertexMap (realVertices r.vertices) x) =
      (affinePoly (rawGap r.vertices)).eval₂ (Rat.castHom ℝ) x := by
    simp only [physicalGap_vertexMap, affinePoly_eval, rawGap_cast]
  simp_rw [he]
  rw [canonical_polynomial_integral, gapMomentQ_eq_polynomialMoment _ (data r) (gapScale r)
    (row_vertex_normalization r).1 (fun i => ((row_vertex_normalization r).2 i).1)]
  rfl

theorem gapMass_pos (r : Row) : 0 < gapMass r := by
  rw [gapMass_eq]
  exact mul_pos (jacobian_pos r) (by exact_mod_cast gapMomentQ_pos _ r.gap_sum_pos)

/-- Both the gap scale and the Jacobian cancel under the normalized weight. -/
theorem normalized_weighted_transport (r : Row) (f : Ambient → ℝ) :
    (∫ z in sourceSupport r.vertices, physicalGap z * f z) / gapMass r =
      (∫ x in canonicalSupport, affine (gapVertices (data r)) x *
        f (vertexMap (realVertices r.vertices) x)) / actualGapMass (data r) := by
  have hgap := (real_vertex_arrays r.vertices r.means (upper r.vertices r.means)
    (data r) (gapScale r) (row_vertex_normalization r)).1
  rw [source_integral r.vertices r.det_ne, gapMass_typed]
  have he (x : Ambient) :
      (affine (gapVertices (data r)) x / (gapScale r : ℝ)) *
          f (vertexMap (realVertices r.vertices) x) =
        (gapScale r : ℝ)⁻¹ * (affine (gapVertices (data r)) x *
          f (vertexMap (realVertices r.vertices) x)) := by ring
  simp_rw [physicalGap_vertexMap, hgap, affine_div, he]
  rw [integral_const_mul]
  have hscale : (gapScale r : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast (row_vertex_normalization r).1)
  change jacobian r * ((gapScale r : ℝ)⁻¹ * _) /
    ((jacobian r / (gapScale r : ℝ)) * actualGapMass (data r)) = _
  rw [← mul_assoc, ← div_eq_mul_inv]
  exact mul_div_mul_left _ _ (div_ne_zero (jacobian_pos r).ne' hscale)

def μ (r : Row) : Measure Ambient := volume.restrict (sourceSupport r.vertices)

def ν (r : Row) : Measure Ambient := weightedProbability (μ r) physicalGap

def U (r : Row) : ℝ := (upper r.vertices r.means : ℝ)

def P (r : Row) (z : Ambient) : ℝ := physicalP (fun j => (r.means j : ℝ)) z

def Y (r : Row) (z : Ambient) : ℝ := physicalY (fun j => (r.means j : ℝ)) (U r) z

def A (r : Row) (j : Fin 10) (z : Ambient) : ℝ :=
  normalizedFactor (fun k => (r.means k : ℝ)) j z

def V (r : Row) (j : Fin 10) : ℝ := (transverseUpper r.vertices r.means j : ℝ)

def B (r : Row) (j : Fin 10) (z : Ambient) : ℝ :=
  physicalDeviation (fun k => (r.means k : ℝ)) j z

def invP10 (r : Row) (z : Ambient) : ℝ := 1 / (P r z)^10

def prodInv (r : Row) (z : Ambient) : ℝ := 1 / ∏ j : Fin 10, A r j z

theorem U_pos (r : Row) : 0 < U r := by
  unfold U
  exact_mod_cast P2Winner9RationalSimplexCaps.upper_pos r.vertices r.means (rawP_pos r 0)

theorem U_typed (r : Row) : U r = ((data r).U : ℝ) / (data r).L := by
  have h := P2Winner9RationalSimplexData.upper_eq (input r)
  change upper r.vertices r.means = ((data r).U : ℚ) / (data r).L at h
  simpa only [U, Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) h

theorem V_typed (r : Row) (j : Fin 10) : V r j = ((data r).maxima j : ℝ) / (data r).L := by
  have h := P2Winner9RationalSimplexData.maxima_eq (input r) j
  change transverseUpper r.vertices r.means j = ((data r).maxima j : ℚ) / (data r).L at h
  simpa only [V, Rat.cast_div, Rat.cast_natCast] using congrArg (fun q : ℚ => (q : ℝ)) h

theorem support_caps (r : Row) {z : Ambient} (hz : z ∈ sourceSupport r.vertices) :
    0 ≤ physicalGap z ∧
      (∀ j : Fin 10, 0 < physicalFactor j z) ∧
      (lower r.vertices r.means : ℝ) ≤ P r z ∧ P r z ≤ U r ∧
      ∀ j : Fin 10, 0 < A r j z ∧ A r j z ≤ V r j ∧ P r z ≤ V r j := by
  rcases hz with ⟨x, hx, rfl⟩
  have hf (j : Fin 10) : 0 < physicalFactor j (vertexMap (realVertices r.vertices) x) := by
    rw [physicalFactor_vertexMap]
    let a : Fin 9 → ℝ := fun i => (rawFactor r.vertices i j : ℝ)
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
    have hmin : 0 < a i := by
      dsimp [a]
      exact_mod_cast r.factor_pos i j
    exact hmin.trans_le (affine_lower hx _ (a i) (fun k => by
      rw [← rawFactor_cast]
      exact hi k (Finset.mem_univ k)))
  refine ⟨?_, hf, ?_, ?_, ?_⟩
  · rw [physicalGap_vertexMap]
    apply affine_lower hx
    intro i
    rw [← rawGap_cast]
    exact_mod_cast r.gap_nonneg i
  · unfold P
    rw [physicalP_vertexMap]
    apply affine_lower hx
    intro i
    rw [← rawP_cast]
    exact_mod_cast P2Winner9RationalSimplexCaps.lower_le_rawP r.vertices r.means i
  · unfold P U
    rw [physicalP_vertexMap]
    apply affine_upper hx
    intro i
    rw [← rawP_cast]
    exact_mod_cast P2Winner9RationalSimplexCaps.rawP_le_upper r.vertices r.means i
  · intro j
    have hj : (0 : ℝ) < (r.means j : ℝ) := by exact_mod_cast r.means_pos j
    refine ⟨div_pos (hf j) hj, ?_, ?_⟩
    · unfold A V
      rw [normalizedFactor_vertexMap]
      apply affine_upper hx
      intro i
      change physicalFactor j (realVertices r.vertices i) / (r.means j : ℝ) ≤ _
      rw [← rawFactor_cast]
      exact_mod_cast P2Winner9RationalSimplexCaps.normalizedFactor_le_transverseUpper
        r.vertices r.means i j
    · unfold P V
      rw [physicalP_vertexMap]
      apply affine_upper hx
      intro i
      rw [← rawP_cast]
      exact_mod_cast P2Winner9RationalSimplexCaps.rawP_le_transverseUpper r.vertices r.means i j

theorem μ_support (r : Row) : ∀ᵐ z ∂μ r, z ∈ sourceSupport r.vertices :=
  ae_restrict_mem (sourceSupport_measurable r.vertices r.det_ne)

theorem gap_nonneg_ae (r : Row) : ∀ᵐ z ∂μ r, 0 ≤ physicalGap z :=
  (μ_support r).mono (fun _ hz => (support_caps r hz).1)

theorem gap_integrable (r : Row) : Integrable physicalGap (μ r) :=
  continuous_physicalGap.continuousOn.integrableOn_compact
    (sourceSupport_compact r.vertices r.det_ne)

instance row_probability (r : Row) : IsProbabilityMeasure (ν r) :=
  weightedProbability_isProbability (μ r) physicalGap (gap_integrable r)
    (gap_nonneg_ae r) (gapMass_pos r)

theorem ν_support (r : Row) : ∀ᵐ z ∂ν r, z ∈ sourceSupport r.vertices := by
  unfold ν weightedProbability
  exact (withDensity_absolutelyContinuous (μ r) _).ae_le (μ_support r)

theorem weighted_integral (r : Row) (f : Ambient → ℝ) :
    (∫ z, f z ∂ν r) = (∫ z in sourceSupport r.vertices, physicalGap z * f z) / gapMass r :=
  integral_weightedProbability (μ r) physicalGap continuous_physicalGap.measurable
    (gap_nonneg_ae r) (gapMass_pos r) f

theorem weighted_integrable (r : Row) {f : Ambient → ℝ}
    (hf : ContinuousOn f (sourceSupport r.vertices)) : Integrable f (ν r) := by
  apply integrable_weightedProbability (μ r) physicalGap
    continuous_physicalGap.measurable (gap_nonneg_ae r) (gapMass_pos r)
  exact (continuous_physicalGap.continuousOn.mul hf).integrableOn_compact
    (sourceSupport_compact r.vertices r.det_ne)

/-- Every affine rational vertex function carries its exact weighted
mean into the physical probability measure. -/
theorem weighted_affine_mean (r : Row) (f : Ambient → ℝ) (fq : Fin 9 → ℚ)
    (hf : ∀ x, f (vertexMap (realVertices r.vertices) x) = affine (fun i => (fq i : ℝ)) x) :
    (∫ z, f z ∂ν r) = (affineMeanQ (rawGap r.vertices) fq : ℝ) := by
  rw [weighted_integral, normalized_weighted_transport,
    ← affineMeanQ_eq_polynomialMoment _ _ (data r) (gapScale r)
      (row_vertex_normalization r).1 (fun i => ((row_vertex_normalization r).2 i).1)]
  exact (weighted_polynomial_cast _ (data r) (gapScale r)
    (row_vertex_normalization r).1 (fun i => ((row_vertex_normalization r).2 i).1)
    (affinePoly fq) _ (fun x => by rw [affinePoly_eval, hf])).symm

theorem probability_P_mean (r : Row) : (∫ z, P r z ∂ν r) = 1 := by
  rw [weighted_affine_mean r (P r) (rawP r.vertices r.means), r.p_mean, Rat.cast_one]
  intro x
  simp only [P, physicalP_vertexMap, rawP_cast]

theorem probability_factor_mean (r : Row) (j : Fin 10) :
    (∫ z, physicalFactor j z ∂ν r) =
      (affineMeanQ (rawGap r.vertices) (fun i => rawFactor r.vertices i j) : ℝ) := by
  apply weighted_affine_mean
  intro x
  simp only [physicalFactor_vertexMap, rawFactor_cast]

theorem A_continuous (r : Row) (j : Fin 10) : Continuous (A r j) :=
  (continuous_physicalFactor j).div_const _

theorem P_continuous (r : Row) : Continuous (P r) := by
  unfold P physicalP
  exact (continuous_finsetSum Finset.univ (fun j _ => A_continuous r j)).div_const _

theorem Y_continuous (r : Row) : Continuous (Y r) := by
  unfold Y physicalY
  exact continuous_const.sub ((P_continuous r).div_const _)

theorem B_continuous (r : Row) (j : Fin 10) : Continuous (B r j) :=
  (A_continuous r j).sub (P_continuous r)

theorem lower_pos (r : Row) : (0 : ℝ) < (lower r.vertices r.means : ℝ) := by
  exact_mod_cast P2Winner9RationalSimplexCaps.lower_pos r.vertices r.means (rawP_pos r)

theorem P_pos (r : Row) {z : Ambient} (hz : z ∈ sourceSupport r.vertices) :
    0 < P r z :=
  (lower_pos r).trans_le (support_caps r hz).2.2.1

private def yUpper (r : Row) : ℝ := 1 - (lower r.vertices r.means : ℝ) / U r

private theorem q_lt_one (r : Row) : yUpper r < 1 :=
  sub_lt_self _ (div_pos (lower_pos r) (U_pos r))

private theorem Y_mem (r : Row) {z : Ambient} (hz : z ∈ sourceSupport r.vertices) :
    Y r z ∈ Icc (0 : ℝ) (yUpper r) := by
  have hc := support_caps r hz
  change 0 ≤ 1 - P r z / U r ∧ 1 - P r z / U r ≤ yUpper r
  exact ⟨sub_nonneg.mpr ((div_le_one (U_pos r)).2 hc.2.2.2.1),
    sub_le_sub_left (div_le_div_of_nonneg_right hc.2.2.1 (U_pos r).le) 1⟩

private theorem Y_lt_one (r : Row) {z : Ambient} (hz : z ∈ sourceSupport r.vertices) :
    Y r z < 1 := (Y_mem r hz).2.trans_lt (q_lt_one r)

private theorem fY_continuousOn (r : Row) :
    ContinuousOn (fun z => 1 / (1 - Y r z)^10) (sourceSupport r.vertices) := by
  apply continuous_const.continuousOn.div
    ((continuous_const.sub (Y_continuous r)).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (ne_of_gt (sub_pos.mpr (Y_lt_one r hz)))

private theorem invP10_continuousOn (r : Row) :
    ContinuousOn (invP10 r) (sourceSupport r.vertices) := by
  apply continuous_const.continuousOn.div ((P_continuous r).pow 10).continuousOn
  intro z hz
  exact pow_ne_zero _ (P_pos r hz).ne'

private theorem invP10_scaled (r : Row) (z : Ambient) :
    invP10 r z = (1 / (U r)^10) * (1 / (1 - Y r z)^10) := by
  have hy : 1 - Y r z = P r z / U r := by
    unfold Y physicalY P
    ring
  rw [invP10, hy, div_pow]
  simp only [one_div, inv_div]
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (U_pos r).ne'), one_mul]

theorem prodInv_continuousOn (r : Row) :
    ContinuousOn (prodInv r) (sourceSupport r.vertices) := by
  have hA := A_continuous r
  have hp : Continuous (fun z => ∏ j : Fin 10, A r j z) := by fun_prop
  apply continuous_const.continuousOn.div hp.continuousOn
  intro z hz
  exact ne_of_gt (Finset.prod_pos (fun j _ => ((support_caps r hz).2.2.2.2 j).1))

theorem density_integrable (r : Row) :
    IntegrableOn physicalUpperIntegrand (sourceSupport r.vertices) := by
  have hfac : ∀ j : Fin 10, Continuous (physicalFactor j) := continuous_physicalFactor
  have hprod : Continuous (fun z : Ambient => ∏ j : Fin 10, physicalFactor j z) := by
    fun_prop
  have hnum : Continuous (fun z : Ambient => 4 * physicalGap z) :=
    continuous_const.mul continuous_physicalGap
  have hcont : ContinuousOn physicalUpperIntegrand (sourceSupport r.vertices) := by
    apply hnum.continuousOn.div hprod.continuousOn
    intro z hz
    exact ne_of_gt (Finset.prod_pos (fun j _ => (support_caps r hz).2.1 j))
  exact hcont.integrableOn_compact (sourceSupport_compact r.vertices r.det_ne)

theorem density_nonneg (r : Row) {z : Ambient} (hz : z ∈ sourceSupport r.vertices) :
    0 ≤ physicalUpperIntegrand z := by
  have hc := support_caps r hz
  exact div_nonneg (mul_nonneg (by norm_num) hc.1)
    (Finset.prod_nonneg (fun j _ => (hc.2.1 j).le))

theorem density_probability_normalization (r : Row) :
    (∫ z in sourceSupport r.vertices, physicalUpperIntegrand z) =
      (r.jensen : ℝ) * (∫ z, prodInv r z ∂ν r) := by
  let m : ℝ := ∏ j : Fin 10, (r.means j : ℝ)
  have hm : 0 < m := Finset.prod_pos (fun j _ => by exact_mod_cast r.means_pos j)
  have hj : (r.jensen : ℝ) = 4 * gapMass r / m := by
    rw [gapMass_eq]
    have h := congrArg (fun q : ℚ => (q : ℝ)) r.jensen_eq
    simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_abs, Rat.cast_prod, Rat.cast_ofNat] at h
    change (r.jensen : ℝ) = 4 * jacobian r * (gapMomentQ (rawGap r.vertices) : ℝ) / m at h
    rw [← mul_assoc]
    exact h
  have hfun (z : Ambient) (hz : z ∈ sourceSupport r.vertices) :
      physicalGap z * prodInv r z = (m / 4) * physicalUpperIntegrand z := by
    have hF : (∏ j : Fin 10, physicalFactor j z) ≠ 0 :=
      (Finset.prod_pos (fun j _ => (support_caps r hz).2.1 j)).ne'
    unfold prodInv A normalizedFactor physicalUpperIntegrand
    rw [Finset.prod_div_distrib]
    change physicalGap z * (1 / ((∏ j : Fin 10, physicalFactor j z) / m)) =
      (m / 4) * (4 * physicalGap z / ∏ j : Fin 10, physicalFactor j z)
    field_simp [hF, hm.ne']
  rw [weighted_integral, hj]
  have h : (∫ z in sourceSupport r.vertices, physicalGap z * prodInv r z) =
      (m / 4) * ∫ z in sourceSupport r.vertices, physicalUpperIntegrand z := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (sourceSupport_measurable r.vertices r.det_ne) hfun
  rw [h]
  field_simp [hm.ne', (gapMass_pos r).ne']

theorem integral_Y_pow (r : Row) (k : ℕ) :
    (∫ z, (Y r z)^k ∂ν r) = actualPowerExpectation (data r) k := by
  have hY := (real_vertex_arrays r.vertices r.means (upper r.vertices r.means)
    (data r) (gapScale r) (row_vertex_normalization r)).2.1
  rw [weighted_integral, normalized_weighted_transport]
  simp only [Y, U, physicalY_vertexMap, hY]
  rfl

theorem integral_Y (r : Row) : (∫ z, Y r z ∂ν r) = 1 - 1 / U r := by
  change (∫ z, 1 - P r z / U r ∂ν r) = _
  rw [integral_sub (integrable_const _) ((weighted_integrable r
    (P_continuous r).continuousOn).div_const _), integral_div, probability_P_mean]
  simp

theorem actual_T10_lower (r : Row) :
    1 + (value (t10 (data r)) : ℝ) ≤ ∫ z, invP10 r z ∂ν r := by
  have hY := weighted_integrable r (Y_continuous r).continuousOn
  have hf := weighted_integrable r (fY_continuousOn r)
  have hp (k : ℕ) (_hk : k ∈ Finset.range 11) : Integrable (fun z => (Y r z)^k) (ν r) :=
    weighted_integrable r ((Y_continuous r).pow k).continuousOn
  have hgap := probability_T10_gap (ν r) (Y r) (q_lt_one r)
    ((ν_support r).mono (fun z hz => Y_mem r hz)) hY hf hp
  have hU := U_pos r
  have hscale : 0 ≤ 1 / (U r)^10 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgap hscale
  have hI : (∫ z, invP10 r z ∂ν r) =
      (1 / (U r)^10) * ∫ z, 1 / (1 - Y r z)^10 ∂ν r := by
    rw [← integral_const_mul]
    exact integral_congr_ae ((ν_support r).mono (fun z _ => invP10_scaled r z))
  have hunit : (1 / (U r)^10) * (1 / (1 - ∫ z, Y r z ∂ν r)^10) = 1 := by
    rw [integral_Y]
    field_simp [hU.ne']
    ring
  rw [← hI, mul_add, hunit] at hscaled
  simp_rw [integral_Y_pow] at hscaled
  have hmean := integral_Y_pow r 1
  simp only [pow_one] at hmean
  rw [hmean, U_typed] at hscaled
  rwa [actual_T10_identity_range]


private def transverseSum (r : Row) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, (B r j z)^2 / (2 * (V r j)^2)

private def cTerm (r : Row) (j : Fin 10) (k : Fin 7) (z : Ambient) : ℝ :=
  (((9 + k.val).choose k.val : ℝ) * (Y r z)^k.val * (B r j z)^2) /
    (2 * (V r j)^2 * (U r)^10)

def C6 (r : Row) (z : Ambient) : ℝ :=
  ∑ j : Fin 10, ∑ k : Fin 7, cTerm r j k z

private theorem C6_factorization (r : Row) (z : Ambient) :
    C6 r z = (1 / (U r)^10) * binomial6 (Y r z) * transverseSum r z := by
  unfold C6 transverseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [binomial6, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  unfold cTerm
  rw [← div_div]
  ring

private theorem transverseSum_nonneg (r : Row) (z : Ambient) : 0 ≤ transverseSum r z :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (by positivity))

private theorem pointwise_Q6 (r : Row) {z : Ambient}
    (hz : z ∈ sourceSupport r.vertices) :
    invP10 r z + C6 r z ≤ prodInv r z := by
  have caps := support_caps r hz
  have hsum : ∑ j : Fin 10, A r j z = 10 * P r z := by
    unfold A P physicalP
    ring
  have hquadratic : (1 + transverseSum r z) / (P r z)^10 ≤ prodInv r z :=
    reciprocal_product_quadratic (fun j => A r j z) (V r) (P r z)
      (fun j => (caps.2.2.2.2 j).1) (P_pos r hz)
      (fun j => (caps.2.2.2.2 j).2.1) (fun j => (caps.2.2.2.2 j).2.2) hsum
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (binomial6_minorant (Y_mem r hz).1 (Y_lt_one r hz))
      (by positivity : 0 ≤ 1 / (U r)^10)
  rw [← invP10_scaled r z] at hscaled
  have hC : C6 r z ≤ invP10 r z * transverseSum r z := by
    rw [C6_factorization]
    exact mul_le_mul_of_nonneg_right hscaled (transverseSum_nonneg r z)
  calc
    invP10 r z + C6 r z ≤ invP10 r z + invP10 r z * transverseSum r z :=
      add_le_add le_rfl hC
    _ = (1 + transverseSum r z) / (P r z)^10 := by
      unfold invP10
      ring
    _ ≤ prodInv r z := hquadratic

private theorem cTerm_continuous (r : Row) (j : Fin 10) (k : Fin 7) :
    Continuous (cTerm r j k) := by
  have hY := Y_continuous r
  have hB := B_continuous r j
  unfold cTerm
  fun_prop

private theorem C6_integrable (r : Row) : Integrable (C6 r) (ν r) := by
  apply weighted_integrable r
  have hc := cTerm_continuous r
  unfold C6
  fun_prop

/-- The actual probability moment, with the same physical gap weighting
and the same normalized factor deviations as the pointwise estimate. -/
private def mixedMoment (r : Row) (j : Fin 10) (k : Fin 7) : ℝ :=
  ∫ z, (Y r z)^k.val * (B r j z)^2 ∂ν r

private theorem integral_cTerm (r : Row) (j : Fin 10) (k : Fin 7) :
    (∫ z, cTerm r j k z ∂ν r) =
      ((9 + k.val).choose k.val : ℝ) * mixedMoment r j k /
        (2 * (V r j)^2 * (U r)^10) := by
  simp only [cTerm, mixedMoment, mul_assoc, integral_div, integral_const_mul]

/-- The expectation contains all ten factors at all seven degrees. -/
private theorem C6_expectation (r : Row) :
    (∫ z, C6 r z ∂ν r) =
      ∑ j : Fin 10, ∑ k : Fin 7,
        ((9 + k.val).choose k.val : ℝ) * mixedMoment r j k /
          (2 * (V r j)^2 * (U r)^10) := by
  have hk (j : Fin 10) (k : Fin 7) : Integrable (cTerm r j k) (ν r) :=
    weighted_integrable r (cTerm_continuous r j k).continuousOn
  have hj (j : Fin 10) :
      Integrable (fun z => ∑ k : Fin 7, cTerm r j k z) (ν r) :=
    integrable_finsetSum Finset.univ (fun k _ => hk j k)
  unfold C6
  rw [integral_finsetSum Finset.univ (fun j _ => hj j)]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => hk _ k), integral_cTerm]

private theorem Q6_expectation_lower (r : Row) :
    (∫ z, invP10 r z ∂ν r) + (∫ z, C6 r z ∂ν r) ≤
      ∫ z, prodInv r z ∂ν r := by
  have hi := weighted_integrable r (invP10_continuousOn r)
  have hc := C6_integrable r
  have hp := weighted_integrable r (prodInv_continuousOn r)
  have hrow : ∀ᵐ z ∂ν r, invP10 r z + C6 r z ≤ prodInv r z :=
    (ν_support r).mono (fun _ hz => pointwise_Q6 r hz)
  have h := integral_mono_ae (hi.add hc) hp hrow
  simpa only [Pi.add_apply, integral_add hi hc] using h

/-- The physical probability mixed moment is the exact canonical
moment with its typed gap and deviation scales. -/
theorem moment_probability (r : Row) (j : Fin 10) (k : ℕ) :
    (∫ z, (Y r z)^k * (B r j z)^2 ∂ν r) = actualMixedPowerExpectation (data r) j k := by
  have h := real_vertex_arrays r.vertices r.means (upper r.vertices r.means)
    (data r) (gapScale r) (row_vertex_normalization r)
  rw [weighted_integral, normalized_weighted_transport]
  simp only [Y, U, B, physicalY_vertexMap, h.2.1, physicalDeviation_vertexMap, h.2.2 j,
    actualMixedPowerExpectation, actualMixedPowerNumerator, canonicalSupport, mul_assoc]

theorem C6_expectation_eq_source (r : Row) :
    (∫ z, C6 r z ∂ν r) = (value (q6 (data r)) : ℝ) := by
  rw [C6_expectation, actual_q6_eq]
  simp only [mixedMoment, moment_probability, V_typed, U_typed]

/-- The rational T10 plus Q6 value bounds the original physical integral. -/
theorem physical_Q6_enclosure (r : Row) :
    ((r.jensen * (1 + value (total (data r))) : ℚ) : ℝ) ≤
      ∫ z in sourceSupport r.vertices, physicalUpperIntegrand z := by
  push_cast
  rw [density_probability_normalization]
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast jensen_nonneg r)
  refine le_trans ?_ (Q6_expectation_lower r)
  rw [total, P2Winner9CurvatureFullExactAssembly.add_value, Rat.cast_add,
    ← C6_expectation_eq_source, ← add_assoc]
  exact add_le_add (actual_T10_lower r) le_rfl

/-- A rational directed floor transfers to the Lebesgue integral. -/
theorem Q6_floor_actual_integral (r : Row) (n : ℕ)
    (h : (n : ℚ) / q96 ≤ r.jensen * (1 + value (total (data r)))) :
    (n : ℝ) / (q96 : ℝ) ≤ ∫ z in sourceSupport r.vertices, physicalUpperIntegrand z := by
  have hh : (((n : ℚ) / q96 : ℚ) : ℝ) ≤
      ((r.jensen * (1 + value (total (data r))) : ℚ) : ℝ) := Rat.cast_le.mpr h
  have hi := hh.trans (physical_Q6_enclosure r)
  simpa only [Rat.cast_div, Rat.cast_natCast] using hi

end

end ImbalancedChen.P2Winner9GenericRowIntegral
