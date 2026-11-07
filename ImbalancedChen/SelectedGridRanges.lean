import ImbalancedChen.ActualGridEnvelopes
import ImbalancedChen.HalfProductGeometry
import ImbalancedChen.ActualSieveGate

/-!
# Geometric ranges of the actually selected full rectangles

The ceiling-minus-one endpoints rewrite each exact half-open grid side as
an open-closed natural interval. A genuine source witness supplies every
range bound. In particular, the upper corner is an actual natural point
of a selected rectangle, so its product obeys the same `4 * N` bound as
every other natural point. No clipping of exterior prime pairs is used.

These are finite geometric gates, not a distribution estimate. Their
constants are uniform in the cell indices and in `1 < kappa <= 2`.
-/

namespace ImbalancedChen

open Filter Topology

noncomputable section

/-- The exact open-closed endpoint corresponding to a half-open grid edge. -/
def multiplicativeGridIocEndpoint (κ : ℝ) (i : ℕ) : ℕ :=
  Nat.ceil (κ ^ i) - 1

/-- A positive grid edge has a positive natural ceiling. -/
theorem multiplicativeGrid_ceil_pos {κ : ℝ} (hκ : 1 < κ) (i : ℕ) :
    0 < Nat.ceil (κ ^ i) := by
  have h : (0 : ℝ) < (Nat.ceil (κ ^ i) : ℝ) :=
    (pow_pos (zero_lt_one.trans hκ) i).trans_le (Nat.le_ceil _)
  exact_mod_cast h

/-- Both endpoint rounding errors are retained exactly, including integral edges. -/
theorem multiplicativeGridIocEndpoint_bounds {κ : ℝ} (hκ : 1 < κ) (i : ℕ) :
    κ ^ i - 1 ≤ (multiplicativeGridIocEndpoint κ i : ℝ) ∧
      (multiplicativeGridIocEndpoint κ i : ℝ) < κ ^ i := by
  have hc : 1 ≤ Nat.ceil (κ ^ i) := multiplicativeGrid_ceil_pos hκ i
  unfold multiplicativeGridIocEndpoint
  rw [Nat.cast_sub hc, Nat.cast_one]
  exact ⟨sub_le_sub_right (Nat.le_ceil _) 1,
    by linarith [Nat.ceil_lt_add_one (pow_pos (zero_lt_one.trans hκ) i).le]⟩

/-- The natural interval has exactly the convention required by rectangle sums. -/
theorem multiplicativeGridSide_eq_Ioc {κ : ℝ} (hκ : 1 < κ) (i : ℕ) :
    multiplicativeGridSide κ i =
      Finset.Ioc (multiplicativeGridIocEndpoint κ i)
        (multiplicativeGridIocEndpoint κ (i + 1)) := by
  ext n
  have hl := multiplicativeGrid_ceil_pos hκ i
  have hu := multiplicativeGrid_ceil_pos hκ (i + 1)
  simp only [multiplicativeGridSide, multiplicativeGridIocEndpoint,
    Finset.mem_Ico, Finset.mem_Ioc]
  omega

/-- Nonemptiness guarantees that the upper integer endpoint is in the exact side. -/
theorem multiplicativeGridIocEndpoint_mem_of_nonempty {κ : ℝ}
    (hκ : 1 < κ) {i : ℕ} (hi : (multiplicativeGridSide κ i).Nonempty) :
    multiplicativeGridIocEndpoint κ (i + 1) ∈ multiplicativeGridSide κ i := by
  obtain ⟨n, hn⟩ := hi
  rw [multiplicativeGridSide_eq_Ioc hκ] at hn ⊢
  have hn' := Finset.mem_Ioc.mp hn
  exact Finset.mem_Ioc.mpr ⟨hn'.1.trans_le hn'.2, le_rfl⟩

/-- Each selected index has an actual source witness in its full rectangle. -/
theorem actualGridIntersectingIndices_witness
    {num den N : ℕ} {T κ : ℝ} {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    ∃ a ∈ halfProductPairs num den N T, a ∈ multiplicativeGridRectangle κ ij :=
  (Finset.mem_filter.mp hij).2

/-- Selection ensures that the literal upper corner is a point of the rectangle. -/
theorem actualGridIntersectingIndices_upperCorner_mem
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    (multiplicativeGridIocEndpoint κ (ij.1 + 1),
      multiplicativeGridIocEndpoint κ (ij.2 + 1)) ∈
        multiplicativeGridRectangle κ ij := by
  obtain ⟨a, _, ha⟩ := actualGridIntersectingIndices_witness hij
  have ha' := Finset.mem_product.mp ha
  exact Finset.mem_product.mpr
    ⟨multiplicativeGridIocEndpoint_mem_of_nonempty hκ ⟨a.1, ha'.1⟩,
      multiplicativeGridIocEndpoint_mem_of_nonempty hκ ⟨a.2, ha'.2⟩⟩

/-- The first open endpoint inherits strict roughness, with its full rounding loss. -/
theorem actualGridIntersectingIndices_lowerEndpoint_gt
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ)) (hT : 0 < T)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    T ^ (((num : ℝ) / (den : ℝ)) / (1 + (num : ℝ) / (den : ℝ))) / 2 - 1 <
      (multiplicativeGridIocEndpoint κ ij.1 : ℝ) := by
  obtain ⟨a, ha, haij⟩ := actualGridIntersectingIndices_witness hij
  obtain ⟨hr, hq, hregion⟩ := (halfProductPairs_iff_prime_realRegion hden).mp ha
  have hrough := halfProduct_rpow_lt_left hb hT
    (Nat.cast_pos.mpr hr.pos) (Nat.cast_pos.mpr hq.pos)
    hregion.2.2.2 hregion.1
  have haedge := (mem_multiplicativeGridRectangle.mp haij).1.2
  rw [pow_succ] at haedge
  have hedge := mul_le_mul_of_nonneg_left hκ2
    (pow_pos (zero_lt_one.trans hκ) ij.1).le
  have hround := (multiplicativeGridIocEndpoint_bounds hκ ij.1).1
  nlinarith only [hrough, haedge, hedge, hround]

/-- The second open endpoint grows at the stronger square-root cutoff scale. -/
theorem actualGridIntersectingIndices_secondEndpoint_gt
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hT : 0 < T)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    Real.sqrt T / 2 - 1 < (multiplicativeGridIocEndpoint κ ij.2 : ℝ) := by
  obtain ⟨a, ha, haij⟩ := actualGridIntersectingIndices_witness hij
  obtain ⟨_, hq, hregion⟩ := (halfProductPairs_iff_prime_realRegion hden).mp ha
  have hq0 : (0 : ℝ) < a.2 := Nat.cast_pos.mpr hq.pos
  have hprod := mul_le_mul_of_nonneg_right hregion.2.2.1 hq0.le
  have hsqrt : Real.sqrt T ≤ (a.2 : ℝ) := by
    nlinarith [hregion.1, Real.sq_sqrt hT.le, Real.sqrt_nonneg T]
  have haedge := (mem_multiplicativeGridRectangle.mp haij).2.2
  rw [pow_succ] at haedge
  have hedge := mul_le_mul_of_nonneg_left hκ2
    (pow_pos (zero_lt_one.trans hκ) ij.2).le
  have hround := (multiplicativeGridIocEndpoint_bounds hκ ij.2).1
  nlinarith only [hsqrt, haedge, hedge, hround]

/-- Every natural point of a selected full cell has first coordinate below `2 sqrt N`. -/
theorem actualGridIntersectingIndices_first_lt_two_sqrt
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij p : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ)
    (hp : p ∈ multiplicativeGridRectangle κ ij) :
    (p.1 : ℝ) < 2 * Real.sqrt (N : ℝ) := by
  obtain ⟨a, ha, haij⟩ := actualGridIntersectingIndices_witness hij
  obtain ⟨hr, hq, hregion⟩ := (halfProductPairs_iff_prime_realRegion hden).mp ha
  have hcaps := halfProductRealRegion_coordinate_caps
    ⟨Nat.cast_pos.mpr hr.pos, Nat.cast_pos.mpr hq.pos⟩
    (div_nonneg (Nat.cast_nonneg num) (Nat.cast_nonneg den)) hregion
  have halower := (mem_multiplicativeGridRectangle.mp haij).1.1
  have hpupper := (mem_multiplicativeGridRectangle.mp hp).1.2
  rw [pow_succ] at hpupper
  have hedge := mul_le_mul_of_nonneg_left hκ2
    (pow_pos (zero_lt_one.trans hκ) ij.1).le
  linarith [hcaps.1]

/-- In particular the exact upper endpoint, without an added ceiling error, has this cap. -/
theorem actualGridIntersectingIndices_upperEndpoint_lt
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) <
      2 * Real.sqrt (N : ℝ) :=
  actualGridIntersectingIndices_first_lt_two_sqrt hden hκ hκ2 hij
    (actualGridIntersectingIndices_upperCorner_mem hκ hij)

/-- All natural points of the full rectangle obey the enlarged product bound. -/
theorem actualGridIntersectingIndices_product_le_four
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij p : ℕ × ℕ} (hij : ij ∈ actualGridIntersectingIndices num den N T κ)
    (hp : p ∈ multiplicativeGridRectangle κ ij) :
    p.1 * p.2 ≤ 4 * N := by
  obtain ⟨a, ha, haij⟩ := actualGridIntersectingIndices_witness hij
  obtain ⟨_, _, _, _, _, haN⟩ := mem_halfProductPairs.mp ha
  have haNR : (a.1 : ℝ) * (a.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast haN
  have hproduct := multiplicativeBoundaryCell_product_le
    (pow_pos (zero_lt_one.trans hκ) ij.1)
    (pow_pos (zero_lt_one.trans hκ) ij.2) (zero_lt_one.trans hκ).le
    (multiplicativeGridRectangle_mem_boundaryCell hp)
    (multiplicativeGridRectangle_mem_boundaryCell haij)
  have hκsq : κ ^ 2 ≤ (4 : ℝ) := by nlinarith
  have hbound : (p.1 : ℝ) * (p.2 : ℝ) ≤ 4 * (N : ℝ) := by
    calc
      (p.1 : ℝ) * (p.2 : ℝ) ≤ κ ^ 2 * ((a.1 : ℝ) * (a.2 : ℝ)) := hproduct
      _ ≤ κ ^ 2 * (N : ℝ) := mul_le_mul_of_nonneg_left haNR (sq_nonneg κ)
      _ ≤ 4 * (N : ℝ) := mul_le_mul_of_nonneg_right hκsq (Nat.cast_nonneg N)
  exact_mod_cast hbound

/-- The corner product bound is valid because selection rules out empty sides. -/
theorem actualGridIntersectingIndices_endpoint_product_le_four
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij : ℕ × ℕ} (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    multiplicativeGridIocEndpoint κ (ij.1 + 1) *
      multiplicativeGridIocEndpoint κ (ij.2 + 1) ≤ 4 * N :=
  actualGridIntersectingIndices_product_le_four hκ hκ2 hij
    (actualGridIntersectingIndices_upperCorner_mem hκ hij)

/-- The product cap applies to every prime pair, including exterior pairs. -/
theorem actualGridIntersectingIndices_prime_product_le_four
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij p : ℕ × ℕ} (hij : ij ∈ actualGridIntersectingIndices num den N T κ)
    (hp : p ∈ actualGridPrimeRectangle κ ij) :
    p.1 * p.2 ≤ 4 * N :=
  actualGridIntersectingIndices_product_le_four hκ hκ2 hij (Finset.mem_filter.mp hp).1

/-- The entire product carrier fits the enlarged cutoff, including exterior products. -/
theorem actualGridProductCarrier_le_four
    {num den N m : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    (hm : m ∈ actualGridProductCarrier num den N T κ) : m ≤ 4 * N := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
  exact actualGridIntersectingIndices_prime_product_le_four hκ hκ2 hij hpij

/-- A selected rectangle has positive source product, hence a positive upper cutoff. -/
theorem actualGridIntersectingIndices_one_le
    {num den N : ℕ} {T κ : ℝ} {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) : 1 ≤ N := by
  obtain ⟨a, ha, _⟩ := actualGridIntersectingIndices_witness hij
  obtain ⟨hr, hq, _, _, _, haN⟩ := mem_halfProductPairs.mp ha
  have hprod : 0 < a.1 * a.2 := Nat.mul_pos hr.pos hq.pos
  omega

/-- The first upper endpoint meets the `X^(1-eta)` gate at `X=4N`, `eta=1/3`. -/
theorem actualGridIntersectingIndices_upperEndpoint_le_twoThirds
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) ≤
      (4 * (N : ℝ)) ^ (2 / 3 : ℝ) := by
  have hN : (1 : ℝ) ≤ N := by
    exact_mod_cast actualGridIntersectingIndices_one_le hij
  calc
    (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) :=
      (actualGridIntersectingIndices_upperEndpoint_lt hden hκ hκ2 hij).le
    _ ≤ Real.sqrt (4 * (N : ℝ)) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
    _ = (4 * (N : ℝ)) ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ ≤ (4 * (N : ℝ)) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

/-- An explicit cutoff suffices for the second open endpoint to be at least two. -/
theorem actualGridIntersectingIndices_two_le_secondEndpoint
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hT : 36 ≤ T)
    (hκ : 1 < κ) (hκ2 : κ ≤ 2) {ij : ℕ × ℕ}
    (hij : ij ∈ actualGridIntersectingIndices num den N T κ) :
    2 ≤ multiplicativeGridIocEndpoint κ ij.2 := by
  have hsqrt : (6 : ℝ) ≤ Real.sqrt T :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hlo := actualGridIntersectingIndices_secondEndpoint_gt hden
    (by linarith : 0 < T) hκ hκ2 hij
  have htwo : (2 : ℝ) ≤ (multiplicativeGridIocEndpoint κ ij.2 : ℝ) := by linarith
  exact_mod_cast htwo

/-- Every fixed logarithm power is below half a positive cutoff power, even
after paying the full endpoint loss. The exponent is fixed before the threshold. -/
theorem eventually_log_pow_le_half_logCutoff_rpow_sub_one
    (A : ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧
        (Real.log (4 * (N : ℝ))) ^ A ≤ (logCutoff N) ^ alpha / 2 - 1 := by
  let gamma : ℝ := (3 / 4 : ℝ) * alpha
  have hgamma : 0 < gamma := mul_pos (by norm_num) halpha
  have hconstant : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ gamma)
      atTop (𝓝 0) := by
    simpa only [pow_zero] using tendsto_nat_log_pow_div_rpow 0 hgamma
  have hdecay : Tendsto (fun N : ℕ =>
      (4 : ℝ) ^ A * ((Real.log (N : ℝ)) ^ A / (N : ℝ) ^ gamma) +
        1 / (N : ℝ) ^ gamma) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_nat_log_pow_div_rpow A hgamma).const_mul ((4 : ℝ) ^ A)).add hconstant
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (4 : ℝ) ^ A * ((Real.log (N : ℝ)) ^ A / (N : ℝ) ^ gamma) +
        1 / (N : ℝ) ^ gamma < 1 / 2 :=
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [hsmall, hlog, eventually_threeQuarterPower_le_logCutoff,
    eventually_ge_atTop (1 : ℕ)] with N hsmallN hlogN hcut hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpowpos : 0 < (N : ℝ) ^ gamma := Real.rpow_pos_of_pos hNpos gamma
  have hratio :
      (4 : ℝ) ^ A * ((Real.log (N : ℝ)) ^ A / (N : ℝ) ^ gamma) +
        1 / (N : ℝ) ^ gamma =
      ((4 : ℝ) ^ A * (Real.log (N : ℝ)) ^ A + 1) / (N : ℝ) ^ gamma := by ring
  rw [hratio] at hsmallN
  have hsmallprod := (div_lt_iff₀ hpowpos).mp hsmallN
  have hlogFour : Real.log (4 * (N : ℝ)) ≤ 4 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hNpos.ne']
    have hfour := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlogFour0 : 0 ≤ Real.log (4 * (N : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * N by omega))
  have hlogPow := pow_le_pow_left₀ hlogFour0 hlogFour A
  rw [mul_pow] at hlogPow
  have hcutpow : (N : ℝ) ^ gamma ≤ (logCutoff N) ^ alpha := by
    calc
      (N : ℝ) ^ gamma = ((N : ℝ) ^ (3 / 4 : ℝ)) ^ alpha :=
        Real.rpow_mul (Nat.cast_nonneg N) (3 / 4 : ℝ) alpha
      _ ≤ (logCutoff N) ^ alpha :=
        Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 4 : ℝ))
          hcut.2 halpha.le
  exact ⟨hcut.1, by linarith⟩

/-- The literal logarithmic cutoff eventually exceeds the explicit finite
threshold for the second open endpoint. -/
theorem eventually_thirtySix_le_logCutoff :
    ∀ᶠ N : ℕ in atTop, 36 ≤ logCutoff N := by
  have hdecay : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ (3 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_zero] using
      tendsto_nat_log_pow_div_rpow 0 (by norm_num : (0 : ℝ) < 3 / 4)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (3 / 4 : ℝ) < 1 / 36 :=
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 36))
  filter_upwards [hsmall, eventually_threeQuarterPower_le_logCutoff,
    eventually_ge_atTop (1 : ℕ)] with N hsmallN hcut hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hNpos (3 / 4 : ℝ))).mp hsmallN
  linarith [hcut.2]

/-- At the actual cutoff the first open endpoint exceeds every fixed real
power of `log(4N)`. The threshold is uniform in all selected cells and ratios. -/
theorem eventually_actualGrid_logCutoff_lowerEndpoint
    {num den : ℕ} (hden : 0 < den) (hb : 0 < (num : ℝ) / (den : ℝ)) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ κ : ℝ, 1 < κ → κ ≤ 2 →
      ∀ ij ∈ actualGridIntersectingIndices num den N (logCutoff N) κ,
        (Real.log (4 * (N : ℝ))) ^ A ≤
          (multiplicativeGridIocEndpoint κ ij.1 : ℝ) := by
  have halpha : 0 < ((num : ℝ) / (den : ℝ)) / (1 + (num : ℝ) / (den : ℝ)) :=
    div_pos hb (by linarith)
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_log_pow_le_half_logCutoff_rpow_sub_one (Nat.ceil A) halpha,
    hlog, eventually_ge_atTop (1 : ℕ)] with N hbound hlogN hN
  intro κ hκ hκ2 ij hij
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogFour : 1 ≤ Real.log (4 * (N : ℝ)) :=
    hlogN.trans (Real.log_le_log hNpos (by nlinarith))
  calc
    (Real.log (4 * (N : ℝ))) ^ A ≤
        (Real.log (4 * (N : ℝ))) ^ (Nat.ceil A : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogFour (Nat.le_ceil A)
    _ = (Real.log (4 * (N : ℝ))) ^ Nat.ceil A := by rw [Real.rpow_natCast]
    _ ≤ (logCutoff N) ^
        (((num : ℝ) / (den : ℝ)) / (1 + (num : ℝ) / (den : ℝ))) / 2 - 1 := hbound.2
    _ ≤ (multiplicativeGridIocEndpoint κ ij.1 : ℝ) :=
      (actualGridIntersectingIndices_lowerEndpoint_gt hden hb hbound.1 hκ hκ2 hij).le

/-- All finite geometric gates for `X=4N`, `eta=1/3`, at the actual cutoff.
There is no prime-rectangle distribution hypothesis in this statement. -/
theorem eventually_actualGrid_logCutoff_ranges
    {num den : ℕ} (hden : 0 < den) (hb : 0 < (num : ℝ) / (den : ℝ)) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ κ : ℝ, 1 < κ → κ ≤ 2 →
      ∀ ij ∈ actualGridIntersectingIndices num den N (logCutoff N) κ,
        (Real.log (4 * (N : ℝ))) ^ A ≤
            (multiplicativeGridIocEndpoint κ ij.1 : ℝ) ∧
          2 ≤ multiplicativeGridIocEndpoint κ ij.2 ∧
          (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) ≤
            (4 * (N : ℝ)) ^ (2 / 3 : ℝ) ∧
          multiplicativeGridIocEndpoint κ (ij.1 + 1) *
            multiplicativeGridIocEndpoint κ (ij.2 + 1) ≤ 4 * N := by
  filter_upwards [eventually_actualGrid_logCutoff_lowerEndpoint hden hb A,
    eventually_thirtySix_le_logCutoff] with N hfirst hcut
  intro κ hκ hκ2 ij hij
  exact ⟨hfirst κ hκ hκ2 ij hij,
    actualGridIntersectingIndices_two_le_secondEndpoint hden hcut hκ hκ2 hij,
    actualGridIntersectingIndices_upperEndpoint_le_twoThirds hden hκ hκ2 hij,
    actualGridIntersectingIndices_endpoint_product_le_four hκ hκ2 hij⟩

end

end ImbalancedChen
