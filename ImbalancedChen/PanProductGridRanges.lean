import ImbalancedChen.PanProductGrid
import ImbalancedChen.RealHalfProductMassSplit

/-!
# Endpoint ranges for the dynamic Pan product grid

An actually selected cell contains a literal source pair `(r,q)`.  In the
product coordinates `(r,m=r*q)`, that witness transfers the source bounds to
the two exact open-closed grid endpoints.  The resulting factors of two pay
both the multiplicative grid width `κ ≤ 2` and the full ceiling-minus-one
rounding convention.

These are finite geometric bounds.  They do not assert any Liu--Pan scale
gate, distribution estimate, or monotonic transfer of a modulus cutoff from
the global scale `N` to a smaller cell endpoint.
-/

namespace ImbalancedChen

noncomputable section

open Filter

/-- The open product endpoint of every selected dynamic cell lies above the
source cutoff, up to the full grid-width and integer-rounding losses. -/
theorem actualPanProductGridIndices_productLowerEndpoint_gt
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij : ℕ × ℕ}
    (hij : ij ∈ actualPanProductGridIndices num den N T κ) :
    T / 2 - 1 < (multiplicativeGridIocEndpoint κ ij.2 : ℝ) := by
  obtain ⟨p, hp, hpij⟩ := (mem_actualPanProductGridIndices.mp hij).2
  obtain ⟨_, _, _, _, hpT, _⟩ := mem_halfProductPairs.mp hp
  have hpedge := ((mem_panProductGridStrip hκ).mp hpij).2.2.2
  have hside := (mem_multiplicativeGridSide.mp hpedge).2
  rw [pow_succ] at hside
  have hwidth := mul_le_mul_of_nonneg_left hκ2
    (pow_pos (zero_lt_one.trans hκ) ij.2).le
  have hround := (multiplicativeGridIocEndpoint_bounds hκ ij.2).1
  nlinarith only [hpT, hside, hwidth, hround]

/-- The closed product endpoint of every selected dynamic cell stays below
twice the original product cap.  This is an endpoint bound, not a clipping of
the full strip back to the curved source. -/
theorem actualPanProductGridIndices_productUpperEndpoint_lt
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij : ℕ × ℕ}
    (hij : ij ∈ actualPanProductGridIndices num den N T κ) :
    (multiplicativeGridIocEndpoint κ (ij.2 + 1) : ℝ) < 2 * (N : ℝ) := by
  obtain ⟨p, hp, hpij⟩ := (mem_actualPanProductGridIndices.mp hij).2
  obtain ⟨_, _, _, _, _, hpN⟩ := mem_halfProductPairs.mp hp
  have hpedge := ((mem_panProductGridStrip hκ).mp hpij).2.2.2
  have hlower := (mem_multiplicativeGridSide.mp hpedge).1
  have hupper := (multiplicativeGridIocEndpoint_bounds hκ (ij.2 + 1)).2
  have hpNR : ((p.1 * p.2 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hpN
  calc
    (multiplicativeGridIocEndpoint κ (ij.2 + 1) : ℝ) <
        κ ^ ij.2 * κ := by simpa only [pow_succ] using hupper
    _ ≤ ((p.1 * p.2 : ℕ) : ℝ) * κ :=
      mul_le_mul_of_nonneg_right hlower (zero_lt_one.trans hκ).le
    _ ≤ ((p.1 * p.2 : ℕ) : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hκ2 (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) * 2 := mul_le_mul_of_nonneg_right hpNR (by norm_num)
    _ = 2 * (N : ℝ) := by ring

/-- The closed first-coordinate endpoint stays below twice `sqrt N`.  The
ordered source condition `r ≤ q` is used before enlarging by one grid cell. -/
theorem actualPanProductGridIndices_firstUpperEndpoint_lt
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij : ℕ × ℕ}
    (hij : ij ∈ actualPanProductGridIndices num den N T κ) :
    (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) <
      2 * Real.sqrt (N : ℝ) := by
  obtain ⟨p, hp, hpij⟩ := (mem_actualPanProductGridIndices.mp hij).2
  obtain ⟨_, _, hporder, _, _, hpN⟩ := mem_halfProductPairs.mp hp
  have hpedge := ((mem_panProductGridStrip hκ).mp hpij).2.2.1
  have hlower := (mem_multiplicativeGridSide.mp hpedge).1
  have hupper := (multiplicativeGridIocEndpoint_bounds hκ (ij.1 + 1)).2
  have hsqNat : p.1 * p.1 ≤ N :=
    (Nat.mul_le_mul_left p.1 hporder).trans hpN
  have hsq : (p.1 : ℝ) * (p.1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hsqNat
  have hrroot : (p.1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [pow_two] using hsq
  calc
    (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) <
        κ ^ ij.1 * κ := by simpa only [pow_succ] using hupper
    _ ≤ (p.1 : ℝ) * κ :=
      mul_le_mul_of_nonneg_right hlower (zero_lt_one.trans hκ).le
    _ ≤ Real.sqrt (N : ℝ) * κ :=
      mul_le_mul_of_nonneg_right hrroot (zero_lt_one.trans hκ).le
    _ ≤ Real.sqrt (N : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left hκ2 (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (N : ℝ) := by ring

/-- Application-facing conjunction of all three endpoint ranges. -/
theorem actualPanProductGridIndices_endpoint_ranges
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (hκ2 : κ ≤ 2)
    {ij : ℕ × ℕ}
    (hij : ij ∈ actualPanProductGridIndices num den N T κ) :
    T / 2 - 1 < (multiplicativeGridIocEndpoint κ ij.2 : ℝ) ∧
      (multiplicativeGridIocEndpoint κ (ij.2 + 1) : ℝ) < 2 * (N : ℝ) ∧
      (multiplicativeGridIocEndpoint κ (ij.1 + 1) : ℝ) <
        2 * Real.sqrt (N : ℝ) :=
  ⟨actualPanProductGridIndices_productLowerEndpoint_gt hκ hκ2 hij,
    actualPanProductGridIndices_productUpperEndpoint_lt hκ hκ2 hij,
    actualPanProductGridIndices_firstUpperEndpoint_lt hκ hκ2 hij⟩

/-- For the manuscript cutoff `2 N^(1-κ₀)`, both product endpoints of
every selected dynamic cell eventually clear any fixed natural threshold.

This is the exact finite-size gate needed to instantiate the `N₀ ≤ Y₀` and
`N₀ ≤ Y₁` hypotheses of the pinned Liu--Pan aggregate.  It remains
uniform in all selected cells.  No modulus-cutoff comparison is asserted. -/
theorem eventually_actualPanProductGridIndices_productEndpoints_ge
    {num den : ℕ} {κm : ℝ} (_hκm0 : 0 < κm) (hκm1 : κm < 1)
    {gridκ : ℝ} (hgridκ : 1 < gridκ) (hgridκ2 : gridκ ≤ 2) (N₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ij ∈ actualPanProductGridIndices num den N
          (manuscriptHalfProductCutoff κm N) gridκ,
        N₀ ≤ multiplicativeGridIocEndpoint gridκ ij.2 ∧
          N₀ ≤ multiplicativeGridIocEndpoint gridκ (ij.2 + 1) := by
  have hexponent : 0 < 1 - κm := sub_pos.mpr hκm1
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - κm)) atTop atTop :=
    (tendsto_rpow_atTop hexponent).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in atTop,
      (N₀ : ℝ) + 1 ≤ (N : ℝ) ^ (1 - κm) :=
    hpower.eventually (eventually_ge_atTop ((N₀ : ℝ) + 1))
  filter_upwards [hlarge] with N hN
  intro ij hij
  have hlower := actualPanProductGridIndices_productLowerEndpoint_gt
    hgridκ hgridκ2 hij
  have hlower' :
      (N : ℝ) ^ (1 - κm) - 1 <
        (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    simpa [manuscriptHalfProductCutoff] using hlower
  have hN₀real : (N₀ : ℝ) ≤
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    linarith
  have hN₀ : N₀ ≤ multiplicativeGridIocEndpoint gridκ ij.2 := by
    exact_mod_cast hN₀real
  exact ⟨hN₀, hN₀.trans (multiplicativeGridIocEndpoint_le_succ hgridκ ij.2)⟩

/-- A fixed multiplicative constant is absorbed by any positive real-power
gap.  This elementary asymptotic form keeps all later endpoint constants
visible instead of hiding them in an `O`-term. -/
theorem eventually_const_mul_rpow_le_rpow (C : ℝ) {alpha beta : ℝ}
    (hgap : alpha < beta) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) ^ alpha ≤ (N : ℝ) ^ beta := by
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ (beta - alpha))
      atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hgap)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hpower.eventually (eventually_ge_atTop C),
    eventually_ge_atTop (1 : ℕ)] with N hC hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  calc
    C * (N : ℝ) ^ alpha ≤
        (N : ℝ) ^ (beta - alpha) * (N : ℝ) ^ alpha :=
      mul_le_mul_of_nonneg_right hC
        (Real.rpow_nonneg (Nat.cast_nonneg N) alpha)
    _ = (N : ℝ) ^ beta := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/-- The manuscript's licensed relation between its local loss parameters
implies the quarter-power gap used by the two-thirds endpoint gate. -/
theorem manuscript_kappaZero_lt_quarter
    {localκ κm : ℝ} (hlocalκ : 0 < localκ)
    (hκm : κm < localκ / (4 * (1 + localκ))) :
    κm < 1 / 4 := by
  calc
    κm < localκ / (4 * (1 + localκ)) := hκm
    _ < 1 / 4 := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 4 * (1 + localκ))
        (by norm_num : (0 : ℝ) < 4)]
      nlinarith

/-- At the manuscript product cutoff, every selected cell eventually meets
the Liu--Pan two-thirds gate at both exact product endpoints.

The strict condition `κ₀ < 1/4` is weaker than the manuscript's licensed
choice `κ₀ < κ/(4(1+κ))`.  The proof pays the full `-1` endpoint
rounding loss and the factor `2` in `A₂ < 2√N`; no asymptotic constant is
silently discarded. -/
theorem eventually_actualPanProductGridIndices_twoThirds_gates
    {num den : ℕ} {κm : ℝ} (_hκm0 : 0 < κm) (hκmQuarter : κm < 1 / 4)
    {gridκ : ℝ} (hgridκ : 1 < gridκ) (hgridκ2 : gridκ ≤ 2) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ij ∈ actualPanProductGridIndices num den N
          (manuscriptHalfProductCutoff κm N) gridκ,
        (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
            (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ^ (2 / 3 : ℝ) ∧
          (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
            (multiplicativeGridIocEndpoint gridκ (ij.2 + 1) : ℝ) ^ (2 / 3 : ℝ) := by
  let alpha : ℝ := ((3 / 4 : ℝ) + (1 - κm)) / 2
  let gamma : ℝ := alpha * (2 / 3 : ℝ)
  have halphaGap : alpha < 1 - κm := by
    dsimp [alpha]
    linarith
  have hgammaGap : (1 / 2 : ℝ) < gamma := by
    dsimp [gamma, alpha]
    linarith
  have halpha0 : 0 ≤ alpha := by
    dsimp [alpha]
    linarith
  filter_upwards [eventually_const_mul_rpow_le_rpow 2 halphaGap,
    eventually_const_mul_rpow_le_rpow 2 hgammaGap,
    eventually_ge_atTop (1 : ℕ)] with N hcut hroot hN
  intro ij hij
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hNreal
  have hlower := actualPanProductGridIndices_productLowerEndpoint_gt
    hgridκ hgridκ2 hij
  have hlower' :
      (N : ℝ) ^ (1 - κm) - 1 <
        (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    simpa [manuscriptHalfProductCutoff] using hlower
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ alpha :=
    Real.one_le_rpow hNreal halpha0
  have hbase : (N : ℝ) ^ alpha ≤
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) := by
    linarith
  have hfirst := actualPanProductGridIndices_firstUpperEndpoint_lt
    hgridκ hgridκ2 hij
  rw [Real.sqrt_eq_rpow] at hfirst
  have hgate₀ :
      (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
        (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
          2 * (N : ℝ) ^ (1 / 2 : ℝ) := hfirst.le
      _ ≤ (N : ℝ) ^ gamma := hroot
      _ = ((N : ℝ) ^ alpha) ^ (2 / 3 : ℝ) :=
        Real.rpow_mul hNnonneg alpha (2 / 3 : ℝ)
      _ ≤ (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNnonneg alpha) hbase (by norm_num)
  have hendpoints :
      (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ≤
        (multiplicativeGridIocEndpoint gridκ (ij.2 + 1) : ℝ) := by
    exact_mod_cast (multiplicativeGridIocEndpoint_le_succ hgridκ ij.2)
  exact ⟨hgate₀, hgate₀.trans
    (Real.rpow_le_rpow (Nat.cast_nonneg _) hendpoints (by norm_num))⟩

/-- Direct specialization of the two-thirds gates to the stronger parameter
relation stated in the manuscript. -/
theorem eventually_actualPanProductGridIndices_twoThirds_gates_of_manuscript
    {num den : ℕ} {localκ κm : ℝ} (hlocalκ : 0 < localκ)
    (hκm0 : 0 < κm) (hκm : κm < localκ / (4 * (1 + localκ)))
    {gridκ : ℝ} (hgridκ : 1 < gridκ) (hgridκ2 : gridκ ≤ 2) :
    ∀ᶠ N : ℕ in atTop,
      ∀ ij ∈ actualPanProductGridIndices num den N
          (manuscriptHalfProductCutoff κm N) gridκ,
        (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
            (multiplicativeGridIocEndpoint gridκ ij.2 : ℝ) ^ (2 / 3 : ℝ) ∧
          (multiplicativeGridIocEndpoint gridκ (ij.1 + 1) : ℝ) ≤
            (multiplicativeGridIocEndpoint gridκ (ij.2 + 1) : ℝ) ^ (2 / 3 : ℝ) :=
  eventually_actualPanProductGridIndices_twoThirds_gates hκm0
    (manuscript_kappaZero_lt_quarter hlocalκ hκm) hgridκ hgridκ2

end

end ImbalancedChen
