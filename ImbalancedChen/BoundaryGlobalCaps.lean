import ImbalancedChen.BoundaryCellContainment
import Mathlib.Analysis.Real.Sqrt

/-!
# Global boundary mass from pointwise crossing cells

Every selected integer pair may have its own positive multiplicative cell
and its own inside/outside witnesses. An inside witness gives the actual
global coordinate bounds, so no ambient box or target mass is assumed.
The three integer caps are the natural ceilings of
`(1 + δ) * sqrt N`, `(1 + δ) * N ^ (1 / (1 + b))`, and
`(1 + δ)^2 * sqrt N`; the last one is reserved for the diagonal collar.
All points in the crossing cells, including exterior products, are counted.

The finite union theorem needs only a pointwise cover by genuine crossing
cells. Constructing or enumerating a particular global grid is separate.
The product weight retains ordered-pair multiplicity on its full support.
-/

namespace ImbalancedChen

noncomputable section

/-- Membership in some positive crossing cell. The witnesses and the cell
are allowed to depend on the point. This is a geometric cover condition,
not a bound on a cardinality or an assumed collar containment. -/
def inHalfProductCrossingCell (δ T N b : ℝ) (p : ℝ × ℝ) : Prop :=
  ∃ R Q : ℝ, ∃ a c : ℝ × ℝ,
    0 < R ∧ 0 < Q ∧
    multiplicativeBoundaryCell R Q (1 + δ) a ∧
    halfProductRealRegion T N b a ∧
    multiplicativeBoundaryCell R Q (1 + δ) c ∧
    ¬ halfProductRealRegion T N b c ∧
    multiplicativeBoundaryCell R Q (1 + δ) p

/-- The first-coordinate cap, rounded outward exactly once. -/
def boundaryGlobalR (δ N : ℝ) : ℕ := Nat.ceil ((1 + δ) * Real.sqrt N)

/-- The power-boundary second-coordinate cap. -/
def boundaryGlobalQ (δ N b : ℝ) : ℕ := Nat.ceil ((1 + δ) * N ^ (1 / (1 + b)))

/-- The smaller cap used only for diagonal slices. -/
def boundaryGlobalS (δ N : ℝ) : ℕ := Nat.ceil ((1 + δ) ^ 2 * Real.sqrt N)

/-- The original region itself supplies both global upper bounds. -/
theorem halfProductRealRegion_coordinate_caps
    {T N b : ℝ} {a : ℝ × ℝ}
    (ha0 : 0 < a.1 ∧ 0 < a.2) (hb : 0 ≤ b)
    (ha : halfProductRealRegion T N b a) :
    a.1 ≤ Real.sqrt N ∧ a.2 ≤ N ^ (1 / (1 + b)) := by
  rcases ha with ⟨haT, haN, harq, hapow⟩
  have hN : 0 ≤ N := (mul_pos ha0.1 ha0.2).le.trans haN
  constructor
  · apply Real.le_sqrt_of_sq_le
    calc
      a.1 ^ 2 = a.1 * a.1 := by ring
      _ ≤ a.1 * a.2 := mul_le_mul_of_nonneg_left harq ha0.1.le
      _ ≤ N := haN
  · rw [one_div]
    apply (Real.le_rpow_inv_iff_of_pos ha0.2.le hN (by linarith : 0 < 1 + b)).2
    rw [Real.rpow_add ha0.2, Real.rpow_one]
    calc
      a.2 * a.2 ^ b ≤ a.2 * a.1 :=
        mul_le_mul_of_nonneg_left hapow.le ha0.2.le
      _ = a.1 * a.2 := by ring
      _ ≤ N := haN

/-- All points of a cell meeting the region inherit the two global caps.
An outside witness is unnecessary for this part of the argument. -/
theorem multiplicativeBoundaryCell_coordinate_caps
    {R Q δ T N b : ℝ} {a p : ℝ × ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (ha : multiplicativeBoundaryCell R Q (1 + δ) a)
    (hA : halfProductRealRegion T N b a)
    (hp : multiplicativeBoundaryCell R Q (1 + δ) p) :
    p.1 ≤ (1 + δ) * Real.sqrt N ∧
      p.2 ≤ (1 + δ) * N ^ (1 / (1 + b)) := by
  have hκ : 0 ≤ 1 + δ := by linarith
  have hpa := multiplicativeBoundaryCell_pairwise_le hκ hp ha
  have hcaps := halfProductRealRegion_coordinate_caps
    (multiplicativeBoundaryCell_pos hR hQ ha) hb hA
  exact ⟨hpa.1.trans (mul_le_mul_of_nonneg_left hcaps.1 hκ),
    hpa.2.trans (mul_le_mul_of_nonneg_left hcaps.2 hκ)⟩

/-- The squared diagonal scale fits the actual natural ceiling cap. -/
theorem boundaryGlobalS_sq_ge {δ N : ℝ} (hN : 0 ≤ N) :
    (1 + δ) ^ 4 * N ≤ (boundaryGlobalS δ N : ℝ) ^ 2 := by
  have hx : 0 ≤ (1 + δ) ^ 2 * Real.sqrt N :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hc : (1 + δ) ^ 2 * Real.sqrt N ≤ (boundaryGlobalS δ N : ℝ) :=
    Nat.le_ceil _
  calc
    (1 + δ) ^ 4 * N = ((1 + δ) ^ 2 * Real.sqrt N) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hN]
      ring
    _ ≤ (boundaryGlobalS δ N : ℝ) ^ 2 := by
      simpa only [pow_two] using mul_le_mul hc hc hx (Nat.cast_nonneg _)

/-- Genuine crossing-cell membership implies the global finite collar
with derived ceiling caps, without any separately assumed coordinate cap. -/
theorem inHalfProductCrossingCell_nat_mem_global_collar
    {δ T N b : ℝ} {p : ℕ × ℕ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hp : inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ))) :
    p ∈ halfProductBoundaryCollar (boundaryGlobalR δ N)
      (boundaryGlobalQ δ N b) (boundaryGlobalS δ N) (3 * δ) T N b := by
  rcases hp with ⟨R, Q, a, c, hR, hQ, ha, hA, hc, hC, hp⟩
  have hp0 := multiplicativeBoundaryCell_pos hR hQ hp
  have ha0 := multiplicativeBoundaryCell_pos hR hQ ha
  have hN : 0 ≤ N := (mul_pos ha0.1 ha0.2).le.trans hA.2.1
  have hcaps := multiplicativeBoundaryCell_coordinate_caps hR hQ hδ hb ha hA hp
  have hrpos : 0 < p.1 := by exact_mod_cast hp0.1
  have hqpos : 0 < p.2 := by exact_mod_cast hp0.2
  have hr : (p.1 : ℝ) ≤ (boundaryGlobalR δ N : ℝ) := hcaps.1.trans (Nat.le_ceil _)
  have hq : (p.2 : ℝ) ≤ (boundaryGlobalQ δ N b : ℝ) := hcaps.2.trans (Nat.le_ceil _)
  exact multiplicativeBoundaryCell_nat_mem_collar hR hQ hδ hδ1 hb hb1
    ha hA hc hC hp ⟨hrpos, Nat.cast_le.mp hr⟩ ⟨hqpos, Nat.cast_le.mp hq⟩
    (boundaryGlobalS_sq_ge hN)

/-- The global collar count for arbitrary finite selections from the
union of crossing cells. Cells may overlap and may vary from point to point. -/
theorem crossingCells_card_le_global_budget
    (B : Finset (ℕ × ℕ)) {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : ∀ p ∈ B, inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ))) :
    (B.card : ℝ) ≤ boundaryGridBudget (boundaryGlobalR δ N)
      (boundaryGlobalQ δ N b) (boundaryGlobalS δ N) (3 * δ) T N b := by
  apply card_le_boundaryGridBudget B _ _ _ _ _ _ _ (by linarith) hT hN
  intro p hp
  exact inHalfProductCrossingCell_nat_mem_global_collar hδ hδ1 hb hb1 (hB p hp)

/-- A closed expression with actual ceiling caps and all lattice endpoint
errors retained. There are no uncomputed sums or assumed mass estimates. -/
theorem crossingCells_card_le_global_log_power
    (B : Finset (ℕ × ℕ)) {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : ∀ p ∈ B, inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ))) :
    (B.card : ℝ) ≤
      6 * δ * (T + N) * (1 + Real.log (boundaryGlobalR δ N : ℝ)) +
        6 * δ * (boundaryGlobalS δ N : ℝ) ^ 2 +
        6 * δ * (boundaryGlobalQ δ N b : ℝ) * (boundaryGlobalQ δ N b : ℝ) ^ b +
        2 * (boundaryGlobalR δ N : ℝ) + boundaryGlobalS δ N + boundaryGlobalQ δ N b := by
  have h := (crossingCells_card_le_global_budget B hδ hδ1 hb hb1 hT hN hB).trans
    (boundaryGridBudget_le_log_power _ _ _ (3 * δ) T N b (by linarith) hT hN hb)
  convert h using 1 <;> ring

/-- The true product convolution mass, including repeated and exterior
products, obeys the same global bound on every full-support carrier. -/
theorem crossingCells_product_mass_le_global_budget
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ) {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : ∀ p ∈ B, inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ)))
    (hM : B.image (fun p => p.1 * p.2) ⊆ M) :
    finiteSourceMass M (pairProductWeight B) ≤
      boundaryGridBudget (boundaryGlobalR δ N) (boundaryGlobalQ δ N b)
        (boundaryGlobalS δ N) (3 * δ) T N b := by
  rw [finiteSourceMass_pairProductWeight B M hM]
  exact crossingCells_card_le_global_budget B hδ hδ1 hb hb1 hT hN hB

/-- The natural ceilings each cost at most one additional coordinate unit.
These terms must not be discarded when the cells are very thin. -/
theorem boundaryGlobalCaps_le_add_one {δ N b : ℝ} (hδ : 0 ≤ δ) (hN : 0 ≤ N) :
    (boundaryGlobalR δ N : ℝ) ≤ (1 + δ) * Real.sqrt N + 1 ∧
    (boundaryGlobalQ δ N b : ℝ) ≤ (1 + δ) * N ^ (1 / (1 + b)) + 1 ∧
    (boundaryGlobalS δ N : ℝ) ≤ (1 + δ) ^ 2 * Real.sqrt N + 1 := by
  have hκ : 0 ≤ 1 + δ := by linarith
  exact ⟨(Nat.ceil_lt_add_one (mul_nonneg hκ (Real.sqrt_nonneg _))).le,
    (Nat.ceil_lt_add_one (mul_nonneg hκ (Real.rpow_nonneg hN _))).le,
    (Nat.ceil_lt_add_one (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))).le⟩

/-- Uniform coarse caps after retaining and then absorbing the ceiling
errors. The square-root and power scales are at least one when `N ≥ 1`. -/
theorem boundaryGlobalCaps_le_three_five {δ N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ N) (hb : 0 ≤ b) :
    (boundaryGlobalR δ N : ℝ) ≤ 3 * Real.sqrt N ∧
    (boundaryGlobalQ δ N b : ℝ) ≤ 3 * N ^ (1 / (1 + b)) ∧
    (boundaryGlobalS δ N : ℝ) ≤ 5 * Real.sqrt N := by
  have hN0 : 0 ≤ N := by linarith
  have hs : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hP : 1 ≤ N ^ (1 / (1 + b)) :=
    Real.one_le_rpow hN (div_nonneg zero_le_one (by linarith))
  have hcaps := boundaryGlobalCaps_le_add_one (b := b) hδ hN0
  have hκ : 1 + δ ≤ 2 := by linarith
  have hκsq : (1 + δ) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hR := mul_le_mul_of_nonneg_right hκ (Real.sqrt_nonneg N)
  have hQ := mul_le_mul_of_nonneg_right hκ (Real.rpow_nonneg hN0 (1 / (1 + b)))
  have hS := mul_le_mul_of_nonneg_right hκsq (Real.sqrt_nonneg N)
  exact ⟨by linarith [hcaps.1], by linarith [hcaps.2.1], by linarith [hcaps.2.2]⟩

/-- The power scale dominates the diagonal scale throughout `0 ≤ b ≤ 1`.
Its defining product identity is exact, rather than an asymptotic claim. -/
theorem boundaryGlobal_power_scale {N b : ℝ}
    (hN : 1 ≤ N) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.sqrt N ≤ N ^ (1 / (1 + b)) ∧
      N ^ (1 / (1 + b)) * (N ^ (1 / (1 + b))) ^ b = N := by
  have hN0 : 0 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hden : 0 < 1 + b := by linarith
  constructor
  · rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hN
    apply (le_div_iff₀ hden).2
    linarith
  · have hPpos : 0 < N ^ (1 / (1 + b)) := Real.rpow_pos_of_pos hNpos _
    calc
      N ^ (1 / (1 + b)) * (N ^ (1 / (1 + b))) ^ b =
          (N ^ (1 / (1 + b))) ^ (1 + b) := by
        rw [Real.rpow_add hPpos, Real.rpow_one]
      _ = N := by
        rw [one_div, Real.rpow_inv_rpow hN0 (ne_of_gt hden)]

/-- A fully explicit global budget. The constants include all natural
ceiling errors and are uniform on the larger range `0 ≤ b ≤ 1`.
In particular this applies to the manuscript's `1/2 < b < 1`.
The expression has the required `δ N log N + N^(1/(1+b))` scale. -/
theorem boundaryGlobal_budget_le_explicit {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hTN : T ≤ N)
    (hN : 1 ≤ N) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    boundaryGridBudget (boundaryGlobalR δ N) (boundaryGlobalQ δ N b)
      (boundaryGlobalS δ N) (3 * δ) T N b ≤
      12 * δ * N * Real.log (3 * N) + 216 * δ * N +
        14 * N ^ (1 / (1 + b)) := by
  let R : ℝ := boundaryGlobalR δ N
  let Q : ℝ := boundaryGlobalQ δ N b
  let S : ℝ := boundaryGlobalS δ N
  let P : ℝ := N ^ (1 / (1 + b))
  have hN0 : 0 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hroot0 := Real.sqrt_nonneg N
  have hroot1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hP0 : 0 ≤ P := Real.rpow_nonneg hN0 _
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  obtain ⟨hR, hQ, hS⟩ := boundaryGlobalCaps_le_three_five hδ hδ1 hN hb
  change R ≤ 3 * Real.sqrt N at hR
  change Q ≤ 3 * P at hQ
  change S ≤ 5 * Real.sqrt N at hS
  obtain ⟨hrootP, hPid⟩ := boundaryGlobal_power_scale hN hb hb1
  change Real.sqrt N ≤ P at hrootP
  change P * P ^ b = N at hPid
  have hR1 : 1 ≤ R := by
    have hc : (1 + δ) * Real.sqrt N ≤ R := Nat.le_ceil _
    have hm := mul_nonneg hδ hroot0
    nlinarith
  have hRpos : 0 < R := by linarith
  have hrootN : Real.sqrt N ≤ N := Real.sqrt_le_self_iff.mpr (Or.inr hN)
  have hRN : R ≤ 3 * N := hR.trans (mul_le_mul_of_nonneg_left hrootN (by norm_num))
  have hlog : Real.log R ≤ Real.log (3 * N) :=
    (Real.log_le_log_iff hRpos (by positivity)).2 hRN
  have hlog0 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  have hproduct :
      6 * δ * (T + N) * (1 + Real.log R) ≤
        12 * δ * N * (1 + Real.log (3 * N)) := by
    calc
      6 * δ * (T + N) * (1 + Real.log R) ≤
          6 * δ * (T + N) * (1 + Real.log (3 * N)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog)
          (mul_nonneg (mul_nonneg (by norm_num) hδ) (add_nonneg hT hN0))
      _ ≤ 6 * δ * (2 * N) * (1 + Real.log (3 * N)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : T + N ≤ 2 * N)
            (mul_nonneg (by norm_num) hδ)) (by linarith)
      _ = 12 * δ * N * (1 + Real.log (3 * N)) := by ring
  have hSsq : S ^ 2 ≤ 25 * N := by
    calc
      S ^ 2 ≤ (5 * Real.sqrt N) ^ 2 := by
        simpa only [pow_two] using mul_le_mul hS hS hS0 (by positivity : 0 ≤ 5 * Real.sqrt N)
      _ = 25 * N := by rw [mul_pow, Real.sq_sqrt hN0]; ring
  have hQb : Q ^ b ≤ 3 * P ^ b := by
    calc
      Q ^ b ≤ (3 * P) ^ b := Real.rpow_le_rpow hQ0 hQ hb
      _ = (3 : ℝ) ^ b * P ^ b := Real.mul_rpow (by norm_num) hP0
      _ ≤ 3 * P ^ b := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hb1)
        (Real.rpow_nonneg hP0 b)
  have hQpow : Q * Q ^ b ≤ 9 * N := by
    calc
      Q * Q ^ b ≤ (3 * P) * (3 * P ^ b) :=
        mul_le_mul hQ hQb (Real.rpow_nonneg hQ0 b) (by positivity)
      _ = 9 * (P * P ^ b) := by ring
      _ = 9 * N := by rw [hPid]
  have hround : 2 * R + S + Q ≤ 14 * P := by linarith
  have hdiag := mul_le_mul_of_nonneg_left hSsq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hδ)
  have hpower := mul_le_mul_of_nonneg_left hQpow
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hδ)
  have hbudget := boundaryGridBudget_le_log_power (boundaryGlobalR δ N)
    (boundaryGlobalQ δ N b) (boundaryGlobalS δ N) (3 * δ) T N b
    (by linarith) hT hN0 hb
  change boundaryGridBudget _ _ _ _ _ _ _ ≤
    2 * (3 * δ) * (T + N) * (1 + Real.log R) +
      2 * (3 * δ) * S ^ 2 + 2 * (3 * δ) * Q * Q ^ b + 2 * R + S + Q at hbudget
  change boundaryGridBudget _ _ _ _ _ _ _ ≤
    12 * δ * N * Real.log (3 * N) + 216 * δ * N + 14 * P
  nlinarith only [hbudget, hproduct, hdiag, hpower, hround]

/-- The actual finite union boundary count with an honest uniform constant. -/
theorem crossingCells_card_le_explicit
    (B : Finset (ℕ × ℕ)) {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hTN : T ≤ N)
    (hN : 1 ≤ N) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hB : ∀ p ∈ B, inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ))) :
    (B.card : ℝ) ≤ 12 * δ * N * Real.log (3 * N) + 216 * δ * N +
      14 * N ^ (1 / (1 + b)) :=
  (crossingCells_card_le_global_budget B hδ hδ1 hb hb1 hT (by linarith) hB).trans
    (boundaryGlobal_budget_le_explicit hδ hδ1 hT hTN hN hb hb1)

/-- The same explicit bound for the full product mass. No restriction to
products below `N` is permitted in the full-support carrier hypothesis. -/
theorem crossingCells_product_mass_le_explicit
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ) {δ T N b : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hTN : T ≤ N)
    (hN : 1 ≤ N) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hB : ∀ p ∈ B, inHalfProductCrossingCell δ T N b ((p.1 : ℝ), (p.2 : ℝ)))
    (hM : B.image (fun p => p.1 * p.2) ⊆ M) :
    finiteSourceMass M (pairProductWeight B) ≤
      12 * δ * N * Real.log (3 * N) + 216 * δ * N + 14 * N ^ (1 / (1 + b)) := by
  rw [finiteSourceMass_pairProductWeight B M hM]
  exact crossingCells_card_le_explicit B hδ hδ1 hT hTN hN hb hb1 hB

end

end ImbalancedChen
