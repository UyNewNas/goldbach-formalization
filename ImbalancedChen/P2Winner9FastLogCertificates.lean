import ImbalancedChen.P2Winner9GenericLogBranch

/-! Integer comparisons for the original degree-six logarithmic floors. -/

namespace ImbalancedChen.P2Winner9FastLogCertificates

open P2Winner9CurvatureExactMomentFloor (gapTotal q80)
open P2Winner9BarycentricMixedDegreeOne (affine yVertices)
open P2Winner9CanonicalPolynomialMoment (affinePoly affinePoly_eval polynomialMoment)
open P2Winner9CurvatureFullExactAssembly
  (SimplexData ExactFraction D H powerMoment weightedMoment homogeneous z value)
open P2Winner9FastExactAssembly (weightedMomentFast zFast)
open P2Winner9FastMomentDecoder (powerMomentQ actualPowerExpectation_eq_cast weighted_polynomial_cast)
open P2Winner9GenericLogBranch
  (Geometry factorTop factorTop_pos rawFactor_le_top logPowerQ logGapQ savedGapQ)
open P2Winner9HomogeneousRecurrence
  (boundedHomogeneous homogeneousFast_eq_source prefixCoefficients prefixCoefficients_correct
    split_coefficient)
open P2Winner9PowerMoment (actualPowerExpectation)
open P2Winner9RationalSimplexData (Input toSimplexData gapDen gapDen_pos gaps_eq y_eq)
open P2Winner9SelectedRowIntegerScales (rawGap rawFactor)
open P2Winner9TaylorCorrection (actualPowerGap_eq_z)

/-- The least common multiple of `k * choose (9 + k) k` for degrees 2–6. -/
private def commonMultiplier : ℕ := 60060

private def degreeMultiplier (k : ℕ) : ℕ := commonMultiplier / (((9 + k).choose k) * k)

private theorem degreeMultiplier_spec (k : ℕ) (hlo : 2 ≤ k) (hhi : k ≤ 6) :
    degreeMultiplier k * (9 + k).choose k * k = commonMultiplier ∧ 0 < degreeMultiplier k := by
  interval_cases k <;> decide

private theorem zFast_eq_source (d : SimplexData) (k : ℕ) : zFast d k = z d k := by
  have h (n : ℕ) : P2Winner9HomogeneousRecurrence.homogeneousFast d.y n =
      homogeneous d.y n := homogeneousFast_eq_source d.y n
  simp only [zFast, z, weightedMomentFast, weightedMoment, h]

private def scaledTerm (d : SimplexData) (k : ℕ) : ℤ :=
  zFast d k * (degreeMultiplier k : ℤ) * (D d : ℤ)^(6 - k)

private theorem boundedCoefficient_irrel {n b₁ b₂ k : ℕ} (y : Fin n → ℕ)
    (h₁ : k ≤ b₁) (h₂ : k ≤ b₂) :
    boundedHomogeneous y b₁ k = boundedHomogeneous y b₂ k := by
  induction n generalizing k with
  | zero =>
    have h (b : ℕ) : boundedHomogeneous y b k = if k = 0 then 1 else 0 := by
      classical
      unfold boundedHomogeneous
      rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Fin (b + 1))]
      · simp [eq_comm]
      · intro e _ he
        exact (he (funext fun i => i.elim0)).elim
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [h, h]
  | succ n ih =>
    rw [split_coefficient y h₁, split_coefficient y h₂]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ih _ ((Nat.sub_le k j).trans h₁) ((Nat.sub_le k j).trans h₂)]

private def momentFromTable (d : SimplexData) (table : List ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), table[k - j]?.getD 0 * powerMoment d j

private theorem momentFromTable_eq (d : SimplexData) (k : ℕ) (hk : k ≤ 6) :
    momentFromTable d (prefixCoefficients 6 9 d.y) k = weightedMomentFast d k := by
  rw [momentFromTable, weightedMomentFast]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [prefixCoefficients_correct _ _ _ _ ((Nat.sub_le k i).trans hk),
    homogeneousFast_eq_source]
  rw [boundedCoefficient_irrel d.y ((Nat.sub_le k i).trans hk) (le_refl (k - i))]
  rfl

private def logNumerator (d : SimplexData) : ℤ :=
  let table := prefixCoefficients 6 9 d.y
  let g := gapTotal d.gaps
  let h := H d
  let meanNum := P2Winner9CurvatureFullExactAssembly.meanNumerator d
  let base := D d
  ∑ i ∈ Finset.range 5,
    let k := i + 2
    ((momentFromTable d table k : ℤ) * (h : ℤ)^k -
      (g : ℤ) * ((9 + k).choose k : ℤ) * (meanNum : ℤ)^k) *
        (degreeMultiplier k : ℤ) * (base : ℤ)^(6 - k)

private theorem logNumerator_eq (d : SimplexData) :
    logNumerator d = ∑ i ∈ Finset.range 5, scaledTerm d (i + 2) := by
  unfold logNumerator
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have h := Finset.mem_range.mp hi
  dsimp only
  rw [momentFromTable_eq d (i + 2) (by omega)]
  rfl

private def logDenominator (d : SimplexData) : ℕ := commonMultiplier * gapTotal d.gaps * (D d)^6

private theorem logDenominator_pos (d : SimplexData) : 0 < logDenominator d := by
  have hG := d.gapsPos
  have hU := d.UPos
  unfold logDenominator commonMultiplier D P2Winner9CurvatureFullExactAssembly.H
  positivity

/-- The original degree-six log gap with a single exact denominator. -/
def logGapFraction (d : SimplexData) : ExactFraction :=
  ⟨logNumerator d, logDenominator d, logDenominator_pos d⟩

private theorem scaledTerm_cast (d : SimplexData) (k : ℕ) (hlo : 2 ≤ k) (hhi : k ≤ 6) :
    (scaledTerm d k : ℝ) / (logDenominator d : ℝ) =
      (actualPowerExpectation d k - (actualPowerExpectation d 1)^k) / (k : ℝ) := by
  have hC : (((9 + k).choose k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k ≤ 9 + k)).ne'
  have hD : (D d : ℝ) ≠ 0 := by
    have hG := d.gapsPos
    have hU := d.UPos
    exact_mod_cast (show D d ≠ 0 by unfold D P2Winner9CurvatureFullExactAssembly.H; positivity)
  have hm : (degreeMultiplier k : ℝ) ≠ 0 := by
    exact_mod_cast (degreeMultiplier_spec k hlo hhi).2.ne'
  have hmult : (degreeMultiplier k : ℝ) * ((9 + k).choose k : ℝ) * (k : ℝ) =
      (commonMultiplier : ℝ) := by
    exact_mod_cast (degreeMultiplier_spec k hlo hhi).1
  have hpow : (D d : ℝ)^k * (D d : ℝ)^(6 - k) = (D d : ℝ)^6 := by
    rw [← pow_add, Nat.add_sub_of_le hhi]
  have hgap : actualPowerExpectation d k - (actualPowerExpectation d 1)^k =
      ((zFast d k : ℝ) / ((gapTotal d.gaps : ℝ) * (D d : ℝ)^k)) /
        ((9 + k).choose k : ℝ) := by
    apply (eq_div_iff hC).2
    rw [mul_comm, zFast_eq_source]
    exact actualPowerGap_eq_z d k
  rw [hgap, div_div, div_div]
  simp only [scaledTerm, logDenominator, Int.cast_mul, Int.cast_natCast, Int.cast_pow,
    Nat.cast_mul, Nat.cast_pow]
  calc
    _ = (zFast d k : ℝ) * ((degreeMultiplier k : ℝ) * (D d : ℝ)^(6 - k)) /
        ((((gapTotal d.gaps : ℝ) * (D d : ℝ)^k) * ((9 + k).choose k : ℝ) * (k : ℝ)) *
          ((degreeMultiplier k : ℝ) * (D d : ℝ)^(6 - k))) := by
      have hden : (commonMultiplier : ℝ) * (gapTotal d.gaps : ℝ) * (D d : ℝ)^6 =
          ((((gapTotal d.gaps : ℝ) * (D d : ℝ)^k) * ((9 + k).choose k : ℝ) * (k : ℝ)) *
            ((degreeMultiplier k : ℝ) * (D d : ℝ)^(6 - k))) := by
        rw [← hmult, ← hpow]
        ring
      rw [hden, mul_assoc]
    _ = (zFast d k : ℝ) /
        (((gapTotal d.gaps : ℝ) * (D d : ℝ)^k) * ((9 + k).choose k : ℝ) * (k : ℝ)) :=
      mul_div_mul_right _ _ (mul_ne_zero hm (pow_ne_zero _ hD))
    _ = _ := by rw [mul_assoc]

theorem logGapFraction_value (d : SimplexData) :
    value (logGapFraction d) =
      ∑ i ∈ Finset.range 5, (powerMomentQ d (i + 2) - (powerMomentQ d 1)^(i + 2)) /
        ((i : ℚ) + 2) := by
  apply Rat.cast_injective (α := ℝ)
  simp only [value, logGapFraction, logNumerator_eq, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast, Rat.cast_sum, Int.cast_sum, Rat.cast_sub, Rat.cast_pow, Rat.cast_add,
    Rat.cast_ofNat, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [← actualPowerExpectation_eq_cast, ← actualPowerExpectation_eq_cast]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    scaledTerm_cast d (i + 2) (by omega) (by omega)

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

private def factorData (r : Geometry) (j : Fin 10) : SimplexData :=
  toSimplexData (factorInput r j)

theorem logGapFraction_eq_original (r : Geometry) (j : Fin 10) :
    value (logGapFraction (factorData r j)) = logGapQ r j :=
  logGapFraction_value (factorData r j)

/-- A signed integer cross-product checks the supplied normalized factor data. -/
def logFloorCheckData (d : SimplexData) (floor : ℕ) : Prop :=
  let f := logGapFraction d
  (floor : ℤ) * (f.den : ℤ) ≤ (q80 : ℤ) * f.num

instance (d : SimplexData) (floor : ℕ) : Decidable (logFloorCheckData d floor) := by
  unfold logFloorCheckData
  infer_instance

theorem logFloorCheckData_iff (d : SimplexData) (floor : ℕ) :
    logFloorCheckData d floor ↔ (floor : ℚ) / q80 ≤ value (logGapFraction d) := by
  rw [value]
  have hq80 : (0 : ℚ) < (q80 : ℚ) := by norm_num [q80]
  have hden : (0 : ℚ) < ((logGapFraction d).den : ℚ) := by
    exact_mod_cast (logGapFraction d).denPos
  rw [div_le_div_iff₀ hq80 hden]
  unfold logFloorCheckData
  rw [mul_comm ((logGapFraction d).num : ℚ)]
  exact_mod_cast (Iff.rfl :
    (floor : ℤ) * ((logGapFraction d).den : ℤ) ≤ (q80 : ℤ) * (logGapFraction d).num ↔ _)

/-- Exact directed log-gap check for the source factor with automatic normalization. -/
def logFloorCheck (r : Geometry) (j : Fin 10) (floor : ℕ) : Prop :=
  logFloorCheckData (factorData r j) floor

instance (r : Geometry) (j : Fin 10) (floor : ℕ) : Decidable (logFloorCheck r j floor) := by
  unfold logFloorCheck
  infer_instance

theorem logFloorCheck_iff (r : Geometry) (j : Fin 10) (floor : ℕ) :
    logFloorCheck r j floor ↔ (floor : ℚ) / q80 ≤ logGapQ r j := by
  rw [← logGapFraction_eq_original]
  exact logFloorCheckData_iff _ _

private theorem normalized_factor_power (r : Geometry) (j : Fin 10) (d : SimplexData)
    (s : ℕ) (hs : 0 < s) (hg : ∀ i, rawGap r.vertices i = (d.gaps i : ℚ) / s)
    (hy : ∀ i, 1 - rawFactor r.vertices i j / factorTop r j = (d.y i : ℚ) / d.U)
    (k : ℕ) :
    ((polynomialMoment (affinePoly (rawGap r.vertices) *
        (affinePoly (fun i => 1 - rawFactor r.vertices i j / factorTop r j))^k) /
        polynomialMoment (affinePoly (rawGap r.vertices)) : ℚ) : ℝ) =
      actualPowerExpectation d k := by
  refine weighted_polynomial_cast _ d s hs hg _ _ (fun x => ?_)
  rw [MvPolynomial.eval₂_pow, affinePoly_eval]
  congr 2
  funext i
  rw [hy i]
  simp only [yVertices, Rat.cast_div, Rat.cast_natCast]

/-- A checker may supply normalized integer arrays separately. Verifying these
two vertex identities once permits the power calculation on the supplied arrays. -/
theorem logFloorCheckData_source (r : Geometry) (j : Fin 10) (d : SimplexData)
    (s : ℕ) (hs : 0 < s) (hg : ∀ i, rawGap r.vertices i = (d.gaps i : ℚ) / s)
    (hy : ∀ i, 1 - rawFactor r.vertices i j / factorTop r j = (d.y i : ℚ) / d.U)
    (floor : ℕ) : logFloorCheckData d floor ↔ (floor : ℚ) / q80 ≤ logGapQ r j := by
  have hp (k : ℕ) : powerMomentQ d k = logPowerQ r j k := by
    apply Rat.cast_injective (α := ℝ)
    change (powerMomentQ d k : ℝ) = (powerMomentQ (factorData r j) k : ℝ)
    rw [← actualPowerExpectation_eq_cast, ← actualPowerExpectation_eq_cast]
    rw [← normalized_factor_power r j d s hs hg hy k,
      ← normalized_factor_power r j (factorData r j) (gapDen (factorInput r j))
        (gapDen_pos (factorInput r j)) (gaps_eq (factorInput r j)) (y_eq (factorInput r j)) k]
  simp only [logFloorCheckData_iff, logGapFraction_value, hp, logGapQ]

end ImbalancedChen.P2Winner9FastLogCertificates
