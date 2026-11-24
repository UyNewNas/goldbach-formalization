import ImbalancedChen.P2DegreeSixLogGapSoundness
import ImbalancedChen.P2Winner9RawFirstMomentDecoder
import ImbalancedChen.P2Winner9RationalSimplexData
import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

/-! The original factorwise log6/exp3 bound for an arbitrary physical Winner9 simplex. -/

namespace ImbalancedChen.P2Winner9GenericLogBranch

open Set MeasureTheory
open P2DegreeSixLogGapSoundnessSourceOnly
open P2PositiveAffineSimplexLogJensenSourceOnly
open P2Winner9BarycentricMixedDegreeOne (affine yVertices)
open P2Winner9CanonicalPolynomialMoment
open P2Winner9CurvatureExactMomentFloor (q80 q96)
open P2Winner9FastMomentDecoder (powerMomentQ actualPowerExpectation_eq_cast weighted_polynomial_cast)
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation
open P2Winner9RationalSimplexData
open P2Winner9RawFirstMomentDecoder
open P2Winner9SelectedRowAnalyticCaps
  (affine_lower affine_upper continuous_physicalFactor continuous_physicalGap)
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix)
open P2Winner9SelectedRowIntegerScales (rawFactor rawGap rawFactor_cast rawGap_cast)
open P2Winner9SelectedRowRealJacobian
open P2Winner9PowerMoment (actualPowerExpectation)

/-- Rational vertex conditions needed by the physical logarithmic estimate. -/
structure Geometry where
  vertices : RationalVertices
  det_ne : (edgeMatrix vertices).det ≠ 0
  gap_nonneg : ∀ i, 0 ≤ rawGap vertices i
  gap_sum_pos : 0 < ∑ i, rawGap vertices i
  factor_pos : ∀ i j, 0 < rawFactor vertices i j

/-- The original factorwise maximum used to scale logarithmic deviations. -/
def factorTop (r : Geometry) (j : Fin 10) : ℚ :=
  (List.ofFn fun i : Fin 9 => rawFactor r.vertices i j).foldl max 0

private theorem foldl_max_initial {α : Type*} [LinearOrder α] (l : List α) (x : α) :
    x ≤ l.foldl max x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih => exact le_trans (le_max_left x a) (ih (max x a))

private theorem foldl_bound {α : Type*} [LinearOrder α] (l : List α) (x : α) {a : α}
    (ha : a ∈ l) : a ≤ l.foldl max x := by
  induction l generalizing x with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · exact le_trans (le_max_right x a) (foldl_max_initial l (max x a))
    · exact ih (max x b) h

theorem rawFactor_le_top (r : Geometry) (i : Fin 9) (j : Fin 10) :
    rawFactor r.vertices i j ≤ factorTop r j :=
  foldl_bound _ 0 (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem factorTop_pos (r : Geometry) (j : Fin 10) : 0 < factorTop r j :=
  (r.factor_pos 0 j).trans_le (rawFactor_le_top r 0 j)

private def factorLower (r : Geometry) (j : Fin 10) : ℚ :=
  (List.ofFn fun i : Fin 9 => rawFactor r.vertices i j).foldl min 1

private theorem factorLower_pos (r : Geometry) (j : Fin 10) : 0 < factorLower r j := by
  have aux (l : List ℚ) (a : ℚ) (ha : 0 < a) (hh : ∀ b ∈ l, 0 < b) :
      0 < l.foldl min a := by
    induction l generalizing a with
    | nil => exact ha
    | cons b l ih =>
      exact ih (min a b) (lt_min ha (hh _ (List.mem_cons_self ..)))
        (fun c hc => hh c (List.mem_cons_of_mem b hc))
  apply aux _ 1 (by norm_num)
  intro b hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
  exact r.factor_pos i j

private theorem factorLower_le_rawFactor (r : Geometry) (i : Fin 9) (j : Fin 10) :
    factorLower r j ≤ rawFactor r.vertices i j :=
  foldl_bound (α := ℚᵒᵈ) _ 1 (List.mem_ofFn.mpr ⟨i, rfl⟩)

private def factorInput (r : Geometry) (j : Fin 10) : Input where
  gaps := rawGap r.vertices
  p i := rawFactor r.vertices i j
  deviations _ _ := 0
  upper := factorTop r j
  maxima _ := 1
  jensen := 0
  gaps_nonneg := r.gap_nonneg
  gaps_pos := r.gap_sum_pos
  upper_pos := factorTop_pos r j
  p_le_upper i := rawFactor_le_top r i j
  maxima_pos _ := by norm_num
  jensen_nonneg := by norm_num

/-- Exact rational moments of the top-scaled affine factor deviation. -/
def logPowerQ (r : Geometry) (j : Fin 10) (k : ℕ) : ℚ :=
  powerMomentQ (toSimplexData (factorInput r j)) k

/-- The original sum of five logarithmic Jensen gaps at powers 2 through 6. -/
def logGapQ (r : Geometry) (j : Fin 10) : ℚ :=
  ∑ k ∈ Finset.range 5, (logPowerQ r j (k + 2) - (logPowerQ r j 1)^(k + 2)) / ((k : ℚ) + 2)

/-- Weighted first moments of all ten original affine factors. -/
def meansQ (r : Geometry) (j : Fin 10) : ℚ :=
  affineMeanQ (rawGap r.vertices) (fun i => rawFactor r.vertices i j)

theorem meansQ_pos (r : Geometry) (j : Fin 10) : 0 < meansQ r j := by
  unfold meansQ affineMeanQ
  have hsum : 0 < ∑ i : Fin 9, rawFactor r.vertices i j := by
    exact Finset.sum_pos (fun i _ => r.factor_pos i j) Finset.univ_nonempty
  have hweighted : 0 ≤ ∑ i : Fin 9, rawGap r.vertices i * rawFactor r.vertices i j := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (r.gap_nonneg i) (r.factor_pos i j).le)
  exact div_pos (add_pos_of_pos_of_nonneg (mul_pos r.gap_sum_pos hsum) hweighted)
    (mul_pos (by norm_num) r.gap_sum_pos)

/-- The original normalization includes the factor of four in the physical density. -/
def jensenQ (r : Geometry) : ℚ :=
  4 * |(edgeMatrix r.vertices).det| * gapMomentQ (rawGap r.vertices) / ∏ j, meansQ r j

def savedGapQ (floors : Fin 10 → ℕ) (j : Fin 10) : ℚ := (floors j : ℚ) / q80

def logPriceQ (jensen : ℚ) (floors : Fin 10 → ℕ) : ℚ :=
  let s := ∑ j, savedGapQ floors j
  jensen * (1 + s * (1 + s * (1 / 2 + s / 6)))

noncomputable section

def μ (r : Geometry) : Measure Ambient := volume.restrict (sourceSupport r.vertices)

def ν (r : Geometry) : Measure Ambient := weightedProbability (μ r) physicalGap

private def gapMass (r : Geometry) : ℝ := mass (μ r) physicalGap

private theorem jacobian_pos (r : Geometry) : 0 < |((edgeMatrix r.vertices).det : ℝ)| := by
  apply abs_pos.mpr
  exact_mod_cast r.det_ne

private theorem gap_pullback (r : Geometry) (x : Ambient) :
    physicalGap (vertexMap (realVertices r.vertices) x) =
      (affinePoly (rawGap r.vertices)).eval₂ (Rat.castHom ℝ) x := by
  simp only [physicalGap_vertexMap, affinePoly_eval, rawGap_cast]

private theorem gap_polynomial (r : Geometry) :
    polynomialMoment (affinePoly (rawGap r.vertices)) = gapMomentQ (rawGap r.vertices) :=
  gapMomentQ_eq_polynomialMoment _ (toSimplexData (factorInput r 0)) _
    (gapDen_pos (factorInput r 0)) (gaps_eq (factorInput r 0))

private theorem gapMass_eq (r : Geometry) :
    gapMass r = |((edgeMatrix r.vertices).det : ℝ)| *
      (gapMomentQ (rawGap r.vertices) : ℝ) := by
  change (∫ x in sourceSupport r.vertices, physicalGap x) = _
  rw [source_integral r.vertices r.det_ne]
  simp_rw [gap_pullback, canonical_polynomial_integral, gap_polynomial]

private theorem gapMass_pos (r : Geometry) : 0 < gapMass r := by
  rw [gapMass_eq]
  exact mul_pos (jacobian_pos r) (by exact_mod_cast gapMomentQ_pos _ r.gap_sum_pos)

private theorem factor_bounds (r : Geometry) (j : Fin 10) {z : Ambient}
    (hz : z ∈ sourceSupport r.vertices) :
    (factorLower r j : ℝ) ≤ physicalFactor j z ∧ physicalFactor j z ≤ (factorTop r j : ℝ) := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [physicalFactor_vertexMap]
  constructor
  · apply affine_lower hx
    intro i
    rw [← rawFactor_cast]
    exact_mod_cast factorLower_le_rawFactor r i j
  · apply affine_upper hx
    intro i
    rw [← rawFactor_cast]
    exact_mod_cast rawFactor_le_top r i j

private theorem factor_pos_on (r : Geometry) {z : Ambient} (hz : z ∈ sourceSupport r.vertices)
    (j : Fin 10) : 0 < physicalFactor j z :=
  lt_of_lt_of_le (by exact_mod_cast factorLower_pos r j) (factor_bounds r j hz).1

private theorem μ_support (r : Geometry) : ∀ᵐ z ∂μ r, z ∈ sourceSupport r.vertices :=
  ae_restrict_mem (sourceSupport_measurable _ r.det_ne)

private theorem gap_ae (r : Geometry) : ∀ᵐ z ∂μ r, 0 ≤ physicalGap z := by
  filter_upwards [μ_support r] with z hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [physicalGap_vertexMap]
  apply affine_lower hx
  intro i
  rw [← rawGap_cast]
  exact_mod_cast r.gap_nonneg i

private theorem gap_integrable (r : Geometry) : Integrable physicalGap (μ r) :=
  continuous_physicalGap.continuousOn.integrableOn_compact
    (sourceSupport_compact _ r.det_ne)

private theorem weighted_integrable (r : Geometry) {f : Ambient → ℝ}
    (hf : ContinuousOn f (sourceSupport r.vertices)) : Integrable f (ν r) :=
  integrable_weightedProbability _ _ continuous_physicalGap.measurable (gap_ae r) (gapMass_pos r)
    ((continuous_physicalGap.continuousOn.mul hf).integrableOn_compact
      (sourceSupport_compact _ r.det_ne))

private theorem weighted_polynomial (r : Geometry) (f : Ambient → ℝ) (p : Poly)
    (hf : ∀ x, p.eval₂ (Rat.castHom ℝ) x = f (vertexMap (realVertices r.vertices) x)) :
    (∫ z, f z ∂ν r) =
      ((polynomialMoment (affinePoly (rawGap r.vertices) * p) /
        polynomialMoment (affinePoly (rawGap r.vertices)) : ℚ) : ℝ) := by
  rw [ν, integral_weightedProbability _ _ continuous_physicalGap.measurable (gap_ae r) (gapMass_pos r)]
  change (∫ z in sourceSupport r.vertices, physicalGap z * f z) / gapMass r = _
  rw [source_integral r.vertices r.det_ne, gapMass_eq, ← gap_polynomial]
  simp_rw [gap_pullback, ← hf, ← MvPolynomial.eval₂_mul, canonical_polynomial_integral]
  rw [mul_div_mul_left _ _ (jacobian_pos r).ne', Rat.cast_div]

private def logY (r : Geometry) (j : Fin 10) : Ambient → ℝ :=
  scaledDeviation (factorTop r j : ℝ) (physicalFactor j)

private def logYPoly (r : Geometry) (j : Fin 10) : Poly :=
  affinePoly (fun i => 1 - rawFactor r.vertices i j / factorTop r j)

private theorem logYPoly_eval (r : Geometry) (j : Fin 10) (x : Ambient) :
    (logYPoly r j).eval₂ (Rat.castHom ℝ) x = logY r j (vertexMap (realVertices r.vertices) x) := by
  rw [logYPoly, affinePoly_eval]
  simp only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, rawFactor_cast]
  rw [logY, scaledDeviation, physicalFactor_vertexMap]
  rw [affine_sub, affine_constant, affine_div]

private theorem logYPoly_scaled (r : Geometry) (j : Fin 10) (x : Ambient) :
    (logYPoly r j).eval₂ (Rat.castHom ℝ) x = affine (yVertices (toSimplexData (factorInput r j))) x := by
  rw [logYPoly, affinePoly_eval]
  congr 1
  funext i
  have h := congrArg (fun q : ℚ => (q : ℝ)) (y_eq (factorInput r j) i)
  simpa only [factorInput, yVertices, Rat.cast_div, Rat.cast_natCast] using h

/-- The fast polynomial moment is the integral under the physical gap probability. -/
theorem integral_logPowerQ (r : Geometry) (j : Fin 10) (k : ℕ) :
    (∫ z, (logY r j z)^k ∂ν r) = (logPowerQ r j k : ℝ) := by
  rw [weighted_polynomial r _ ((logYPoly r j)^k) (fun x => by rw [MvPolynomial.eval₂_pow, logYPoly_eval])]
  rw [weighted_polynomial_cast (rawGap r.vertices) (toSimplexData (factorInput r j)) _
    (gapDen_pos (factorInput r j)) (gaps_eq (factorInput r j)) _ _
    (fun x => by rw [MvPolynomial.eval₂_pow, logYPoly_scaled])]
  exact actualPowerExpectation_eq_cast _ k

theorem probability_factor_mean (r : Geometry) (j : Fin 10) :
    (∫ z, physicalFactor j z ∂ν r) = (meansQ r j : ℝ) := by
  rw [weighted_polynomial r _ (affinePoly (fun i => rawFactor r.vertices i j))
    (fun x => by rw [affinePoly_eval, physicalFactor_vertexMap]; simp only [rawFactor_cast])]
  rw [affineMeanQ_eq_polynomialMoment (rawGap r.vertices) _ (toSimplexData (factorInput r j)) _
    (gapDen_pos (factorInput r j)) (gaps_eq (factorInput r j))]
  rfl

private theorem gapSix_eq (r : Geometry) (j : Fin 10) :
    gapSix (ν r) (logY r j) = (logGapQ r j : ℝ) := by
  have h := integral_logPowerQ r j 1
  simp only [pow_one] at h
  simp only [gapSix, logGapQ, integral_logPowerQ, h, Rat.cast_sum, Rat.cast_div, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat]

private theorem measured_log_bound (r : Geometry) (j : Fin 10) :
    (∫ z, physicalGap z * Real.log (physicalFactor j z) ∂μ r) / gapMass r ≤
      Real.log (meansQ r j : ℝ) - (logGapQ r j : ℝ) := by
  have hTop : (0 : ℝ) < (factorTop r j : ℝ) := by exact_mod_cast factorTop_pos r j
  have hLo : (0 : ℝ) < (factorLower r j : ℝ) := by exact_mod_cast factorLower_pos r j
  have hq : 1 - (factorLower r j : ℝ) / (factorTop r j : ℝ) < 1 := by
    linarith [div_pos hLo hTop]
  have hν : ∀ᵐ z ∂ν r, z ∈ sourceSupport r.vertices :=
    (withDensity_absolutelyContinuous (μ r) _).ae_le (μ_support r)
  let : IsProbabilityMeasure (ν r) :=
    weightedProbability_isProbability _ _ (gap_integrable r) (gap_ae r) (gapMass_pos r)
  have h := probability_factor_log_bound (ν r) (factorTop r j : ℝ) hTop (physicalFactor j) hq
    (hν.mono fun _ hz => (scaledDeviation_range hTop hLo (factor_bounds r j hz)).1)
    (hν.mono fun _ hz => factor_pos_on r hz j)
    (weighted_integrable r (continuous_physicalFactor j).continuousOn)
    (weighted_integrable r ((continuous_physicalFactor j).continuousOn.log
      (fun _ hz => (factor_pos_on r hz j).ne')))
    (fun k _ _ => weighted_integrable r
      ((continuous_const.sub ((continuous_physicalFactor j).div_const _)).pow k).continuousOn)
  change (∫ z, Real.log (physicalFactor j z) ∂ν r) ≤
    Real.log (∫ z, physicalFactor j z ∂ν r) - gapSix (ν r) (logY r j) at h
  rw [probability_factor_mean, gapSix_eq] at h
  exact (integral_weightedProbability _ _ continuous_physicalGap.measurable (gap_ae r)
    (gapMass_pos r) (fun z => Real.log (physicalFactor j z))) ▸ h

/-- The stored degree-six log-gap floors give the original cubic physical bound. -/
theorem log_price_le_integral (r : Geometry) (floors : Fin 10 → ℕ)
    (hgap : ∀ j, savedGapQ floors j ≤ logGapQ r j) :
    (logPriceQ (jensenQ r) floors : ℝ) ≤ ∫ z in sourceSupport r.vertices, physicalUpperIntegrand z := by
  have hc := sourceSupport_compact r.vertices r.det_ne
  have hlog (j : Fin 10) : Integrable (fun z => physicalGap z * Real.log (physicalFactor j z)) (μ r) :=
    (continuous_physicalGap.continuousOn.mul ((continuous_physicalFactor j).continuousOn.log
      (fun _ hz => (factor_pos_on r hz j).ne'))).integrableOn_compact hc
  have hprod : Continuous (fun z => ∏ j, physicalFactor j z) :=
    continuous_finsetProd _ (fun j _ => continuous_physicalFactor j)
  have hrecip : Integrable (fun z => physicalGap z / ∏ j, physicalFactor j z) (μ r) :=
    (continuous_physicalGap.continuousOn.div hprod.continuousOn (fun z hz =>
      (Finset.prod_pos (fun j _ => factor_pos_on r hz j)).ne')).integrableOn_compact hc
  have hbound (j : Fin 10) : (∫ z, physicalGap z * Real.log (physicalFactor j z) ∂μ r) / gapMass r ≤
      Real.log (meansQ r j : ℝ) - (savedGapQ floors j : ℝ) := by
    exact (measured_log_bound r j).trans (sub_le_sub_left (by exact_mod_cast hgap j) _)
  have h := weighted_log_gap_cubic_lower_four (μ r) physicalGap physicalFactor
    (fun j => (meansQ r j : ℝ)) (fun j => (savedGapQ floors j : ℝ))
    continuous_physicalGap.measurable (gap_integrable r) (gap_ae r) (gapMass_pos r)
    ((μ_support r).mono fun _ hz => factor_pos_on r hz) hlog hrecip
    (fun j => by exact_mod_cast meansQ_pos r j)
    (fun j => by unfold savedGapQ q80; positivity) hbound
  change (4 * gapMass r / ∏ j, (meansQ r j : ℝ)) * _ ≤ _ at h
  rw [gapMass_eq] at h
  simpa [logPriceQ, jensenQ, Rat.cast_sum, Rat.cast_prod, cubicCorrection,
    physicalUpperIntegrand, μ, mul_assoc] using h

/-- The directed Q96 log-selected floor for the actual physical simplex. -/
theorem directed_log_floor (r : Geometry) (jensen : ℚ) (floors : Fin 10 → ℕ) (selected : ℕ)
    (hjensen : jensen = jensenQ r) (hgap : ∀ j, savedGapQ floors j ≤ logGapQ r j)
    (hfloor : (selected : ℚ) / q96 ≤ logPriceQ jensen floors) :
    (selected : ℝ) / (q96 : ℝ) ≤ ∫ z in sourceSupport r.vertices, physicalUpperIntegrand z := by
  rw [hjensen] at hfloor
  have hcast : (((selected : ℚ) / q96 : ℚ) : ℝ) ≤ (logPriceQ (jensenQ r) floors : ℝ) :=
    Rat.cast_le.mpr hfloor
  exact (by simpa only [Rat.cast_div, Rat.cast_natCast] using hcast :
    (selected : ℝ) / (q96 : ℝ) ≤ (logPriceQ (jensenQ r) floors : ℝ)).trans
      (log_price_le_integral r floors hgap)

end

end ImbalancedChen.P2Winner9GenericLogBranch
