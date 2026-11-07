import ImbalancedChen.BoundaryGridBudget
import ImbalancedChen.HalfProductSource
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Geometric containment of a crossing multiplicative cell

A positive rectangle with side ratios `1 + δ` that meets both the real
half-product region and its complement lies in the four boundary collars
with the explicit common width `η = 3 * δ`, for `0 ≤ δ ≤ 1` and `0 ≤ b ≤ 1`.
Thus the constant is uniform throughout the manuscript's `1/2 < b < 1`.
The rectangle is closed, so the result also covers half-open cells and
their exact integer restrictions. Both witnesses and every point being
bounded lie in the same cell; no collar containment or mass estimate is
assumed. Exterior points, including products above `N`, remain present.

The lower power inequality is strict and both product cutoffs are inclusive.
The diagonal branch also has the proved bound `q² ≤ (1 + δ)^4 * N`.
Consequently its natural-coordinate cap can be chosen independently of the
power-boundary cap. The final finite counting theorem applies the existing
four-collar budget to actual points in a crossing cell.

This is a local crossing lemma, not a construction or enumeration of an
entire grid. Integer rounding means taking the exact natural points of a
real half-open cell; arbitrary outward enlargements of the cell are not
asserted to have the same ratio.
-/

namespace ImbalancedChen

noncomputable section

/-- A closed multiplicative rectangle. Positivity of its two lower endpoints
and the lower bound on its ratio are hypotheses of the geometric theorems. -/
def multiplicativeBoundaryCell (R Q κ : ℝ) (p : ℝ × ℝ) : Prop :=
  R ≤ p.1 ∧ p.1 ≤ κ * R ∧ Q ≤ p.2 ∧ p.2 ≤ κ * Q

/-- The literal real curved region, including `rq = T`, `rq = N`, and the
diagonal, but excluding the lower power curve. -/
def halfProductRealRegion (T N b : ℝ) (p : ℝ × ℝ) : Prop :=
  T ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ N ∧ p.1 ≤ p.2 ∧ p.2 ^ b < p.1

/-- Four real collars, with a separate squared diagonal cap `D`.
No intersection with the curved region is imposed. -/
def halfProductRealBoundaryCollar (η D T N b : ℝ) (p : ℝ × ℝ) : Prop :=
  |p.1 * p.2 - T| ≤ η * T ∨
  |p.1 * p.2 - N| ≤ η * N ∨
  (p.2 ^ 2 ≤ D ∧ |p.1 - p.2| ≤ η * p.2) ∨
  |p.1 - p.2 ^ b| ≤ η * p.2 ^ b

/-- An exact half-open real cell is contained in its closed version. -/
theorem multiplicativeBoundaryCell_of_halfOpen {R Q κ : ℝ} {p : ℝ × ℝ}
    (hp : R ≤ p.1 ∧ p.1 < κ * R ∧ Q ≤ p.2 ∧ p.2 < κ * Q) :
    multiplicativeBoundaryCell R Q κ p :=
  ⟨hp.1, hp.2.1.le, hp.2.2.1, hp.2.2.2.le⟩

/-- Ceiling endpoints encode the exact natural restriction of a real
half-open rectangle. In particular, they introduce no outward enlargement. -/
theorem multiplicativeBoundaryCell_of_ceil_bounds
    {R Q κ : ℝ} {p : ℕ × ℕ}
    (hp : Nat.ceil R ≤ p.1 ∧ p.1 < Nat.ceil (κ * R) ∧
      Nat.ceil Q ≤ p.2 ∧ p.2 < Nat.ceil (κ * Q)) :
    multiplicativeBoundaryCell R Q κ ((p.1 : ℝ), (p.2 : ℝ)) := by
  apply multiplicativeBoundaryCell_of_halfOpen
  exact ⟨Nat.ceil_le.mp hp.1, Nat.lt_ceil.mp hp.2.1,
    Nat.ceil_le.mp hp.2.2.1, Nat.lt_ceil.mp hp.2.2.2⟩

/-- Positivity is retained at every point of a positive cell. -/
theorem multiplicativeBoundaryCell_pos {R Q κ : ℝ} {p : ℝ × ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (hp : multiplicativeBoundaryCell R Q κ p) :
    0 < p.1 ∧ 0 < p.2 :=
  ⟨lt_of_lt_of_le hR hp.1, lt_of_lt_of_le hQ hp.2.2.1⟩

/-- Any two coordinates in the same cell differ by at most the cell ratio. -/
theorem multiplicativeBoundaryCell_pairwise_le {R Q κ : ℝ} {p a : ℝ × ℝ}
    (hκ : 0 ≤ κ) (hp : multiplicativeBoundaryCell R Q κ p)
    (ha : multiplicativeBoundaryCell R Q κ a) :
    p.1 ≤ κ * a.1 ∧ p.2 ≤ κ * a.2 := by
  exact ⟨hp.2.1.trans (mul_le_mul_of_nonneg_left ha.1 hκ),
    hp.2.2.2.trans (mul_le_mul_of_nonneg_left ha.2.2.1 hκ)⟩

/-- Products of two cell coordinates differ by at most the squared ratio. -/
theorem multiplicativeBoundaryCell_product_le {R Q κ : ℝ} {p a : ℝ × ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (hκ : 0 ≤ κ)
    (hp : multiplicativeBoundaryCell R Q κ p)
    (ha : multiplicativeBoundaryCell R Q κ a) :
    p.1 * p.2 ≤ κ ^ 2 * (a.1 * a.2) := by
  have hpa := multiplicativeBoundaryCell_pairwise_le hκ hp ha
  have hp0 := multiplicativeBoundaryCell_pos hR hQ hp
  have ha0 := multiplicativeBoundaryCell_pos hR hQ ha
  calc
    p.1 * p.2 ≤ (κ * a.1) * (κ * a.2) :=
      mul_le_mul hpa.1 hpa.2 hp0.2.le (mul_nonneg hκ ha0.1.le)
    _ = κ ^ 2 * (a.1 * a.2) := by ring

/-- Powers with exponent in `[0,1]` increase no faster than the cell ratio. -/
theorem multiplicativeBoundaryCell_rpow_le {R Q κ b : ℝ} {p a : ℝ × ℝ}
    (hQ : 0 < Q) (hκ : 1 ≤ κ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hp : multiplicativeBoundaryCell R Q κ p)
    (ha : multiplicativeBoundaryCell R Q κ a) :
    p.2 ^ b ≤ κ * a.2 ^ b := by
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hp0 : 0 ≤ p.2 := (lt_of_lt_of_le hQ hp.2.2.1).le
  have ha0 : 0 ≤ a.2 := (lt_of_lt_of_le hQ ha.2.2.1).le
  calc
    p.2 ^ b ≤ (κ * a.2) ^ b :=
      Real.rpow_le_rpow hp0 (multiplicativeBoundaryCell_pairwise_le hκ0 hp ha).2 hb
    _ = κ ^ b * a.2 ^ b := Real.mul_rpow hκ0 ha0
    _ ≤ κ * a.2 ^ b := mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le hκ hb1) (Real.rpow_nonneg ha0 b)

/-- Two-sided multiplicative comparison implies the required absolute collar.
This elementary lemma does not replace either comparison by an assumption
about an absolute error. -/
theorem boundaryCell_abs_sub_le_of_ratio {x y k : ℝ}
    (hk : 1 ≤ k) (hxy : x ≤ k * y) (hyx : y ≤ k * x) :
    |x - y| ≤ (k - 1) * y := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hmul := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hk)
    nlinarith only [hyx, hmul]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith only [hxy]

/-- Genuine local containment. A crossing is witnessed by one point inside
and one point outside the region, not by a presumed boundary condition.
Every point of that same closed cell is in one of the four collars. The
additional squared diagonal bound is derived from the inside product bound. -/
theorem multiplicativeBoundaryCell_crossing
    {R Q δ T N b : ℝ} {a c p : ℝ × ℝ}
    (hR : 0 < R) (hQ : 0 < Q) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : multiplicativeBoundaryCell R Q (1 + δ) a)
    (hA : halfProductRealRegion T N b a)
    (hc : multiplicativeBoundaryCell R Q (1 + δ) c)
    (hC : ¬ halfProductRealRegion T N b c)
    (hp : multiplicativeBoundaryCell R Q (1 + δ) p) :
    halfProductRealBoundaryCollar (3 * δ) ((1 + δ) ^ 4 * N) T N b p := by
  let κ : ℝ := 1 + δ
  have hκ : 1 ≤ κ := by dsimp [κ]; linarith
  have hκ0 : 0 ≤ κ := le_trans (by norm_num) hκ
  have hκsq : 1 ≤ κ ^ 2 := by nlinarith
  have hwidth : κ ^ 2 - 1 ≤ 3 * δ := by
    dsimp [κ]
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have habs {x y : ℝ} (hy : 0 ≤ y)
      (hxy : x ≤ κ ^ 2 * y) (hyx : y ≤ κ ^ 2 * x) :
      |x - y| ≤ (3 * δ) * y :=
    (boundaryCell_abs_sub_le_of_ratio hκsq hxy hyx).trans
      (mul_le_mul_of_nonneg_right hwidth hy)
  have ha0 := multiplicativeBoundaryCell_pos hR hQ ha
  have hc0 := multiplicativeBoundaryCell_pos hR hQ hc
  have hp0 := multiplicativeBoundaryCell_pos hR hQ hp
  have hpa := multiplicativeBoundaryCell_pairwise_le hκ0 hp ha
  have hap := multiplicativeBoundaryCell_pairwise_le hκ0 ha hp
  have hpc := multiplicativeBoundaryCell_pairwise_le hκ0 hp hc
  have hcp := multiplicativeBoundaryCell_pairwise_le hκ0 hc hp
  rcases hA with ⟨haT, haN, harq, hapow⟩
  have hN0 : 0 ≤ N := (mul_pos ha0.1 ha0.2).le.trans haN
  have hout : c.1 * c.2 < T ∨ N < c.1 * c.2 ∨ c.2 < c.1 ∨ c.1 ≤ c.2 ^ b := by
    by_cases hT : T ≤ c.1 * c.2
    · by_cases hN : c.1 * c.2 ≤ N
      · by_cases hd : c.1 ≤ c.2
        · exact Or.inr (Or.inr (Or.inr (le_of_not_gt fun hpow => hC ⟨hT, hN, hd, hpow⟩)))
        · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge hd)))
      · exact Or.inr (Or.inl (lt_of_not_ge hN))
    · exact Or.inl (lt_of_not_ge hT)
  change |p.1 * p.2 - T| ≤ (3 * δ) * T ∨
    |p.1 * p.2 - N| ≤ (3 * δ) * N ∨
    (p.2 ^ 2 ≤ κ ^ 4 * N ∧ |p.1 - p.2| ≤ (3 * δ) * p.2) ∨
    |p.1 - p.2 ^ b| ≤ (3 * δ) * p.2 ^ b
  rcases hout with hT | hN | hd | hpow
  · left
    apply habs ((mul_pos hc0.1 hc0.2).le.trans hT.le)
    · exact (multiplicativeBoundaryCell_product_le hR hQ hκ0 hp hc).trans
        (mul_le_mul_of_nonneg_left hT.le (sq_nonneg κ))
    · exact haT.trans (multiplicativeBoundaryCell_product_le hR hQ hκ0 ha hp)
  · right; left
    apply habs hN0
    · exact (multiplicativeBoundaryCell_product_le hR hQ hκ0 hp ha).trans
        (mul_le_mul_of_nonneg_left haN (sq_nonneg κ))
    · exact hN.le.trans (multiplicativeBoundaryCell_product_le hR hQ hκ0 hc hp)
  · right; right; left
    have hupper : p.1 ≤ κ ^ 2 * p.2 := by
      calc
        p.1 ≤ κ * a.1 := hpa.1
        _ ≤ κ * a.2 := mul_le_mul_of_nonneg_left harq hκ0
        _ ≤ κ * (κ * p.2) := mul_le_mul_of_nonneg_left hap.2 hκ0
        _ = κ ^ 2 * p.2 := by ring
    have hlower : p.2 ≤ κ ^ 2 * p.1 := by
      calc
        p.2 ≤ κ * c.2 := hpc.2
        _ ≤ κ * c.1 := mul_le_mul_of_nonneg_left hd.le hκ0
        _ ≤ κ * (κ * p.1) := mul_le_mul_of_nonneg_left hcp.1 hκ0
        _ = κ ^ 2 * p.1 := by ring
    have hqa : p.2 ≤ κ ^ 2 * a.1 := by
      have hca := multiplicativeBoundaryCell_pairwise_le hκ0 hc ha
      calc
        p.2 ≤ κ * c.2 := hpc.2
        _ ≤ κ * c.1 := mul_le_mul_of_nonneg_left hd.le hκ0
        _ ≤ κ * (κ * a.1) := mul_le_mul_of_nonneg_left hca.1 hκ0
        _ = κ ^ 2 * a.1 := by ring
    have haa : a.1 * a.1 ≤ N :=
      (mul_le_mul_of_nonneg_left harq ha0.1.le).trans haN
    have hdiag : p.2 ^ 2 ≤ κ ^ 4 * N := by
      calc
        p.2 ^ 2 = p.2 * p.2 := by ring
        _ ≤ (κ ^ 2 * a.1) * (κ ^ 2 * a.1) :=
          mul_le_mul hqa hqa hp0.2.le (mul_nonneg (sq_nonneg κ) ha0.1.le)
        _ = κ ^ 4 * (a.1 * a.1) := by ring
        _ ≤ κ ^ 4 * N := mul_le_mul_of_nonneg_left haa (pow_nonneg hκ0 4)
    exact ⟨hdiag, habs hp0.2.le hupper hlower⟩
  · right; right; right
    have hupper : p.1 ≤ κ ^ 2 * p.2 ^ b := by
      have hcpow := multiplicativeBoundaryCell_rpow_le hQ hκ hb hb1 hc hp
      calc
        p.1 ≤ κ * c.1 := hpc.1
        _ ≤ κ * c.2 ^ b := mul_le_mul_of_nonneg_left hpow hκ0
        _ ≤ κ * (κ * p.2 ^ b) := mul_le_mul_of_nonneg_left hcpow hκ0
        _ = κ ^ 2 * p.2 ^ b := by ring
    have hlower : p.2 ^ b ≤ κ ^ 2 * p.1 := by
      have hpapow := multiplicativeBoundaryCell_rpow_le hQ hκ hb hb1 hp ha
      calc
        p.2 ^ b ≤ κ * a.2 ^ b := hpapow
        _ ≤ κ * a.1 := mul_le_mul_of_nonneg_left hapow.le hκ0
        _ ≤ κ * (κ * p.1) := mul_le_mul_of_nonneg_left hap.1 hκ0
        _ = κ ^ 2 * p.1 := by ring
    exact habs (Real.rpow_nonneg hp0.2.le b) hupper hlower

/-- Exact bridge to the already-defined finite source-pair predicate.
The product casts, the inclusive endpoints, and the strict power boundary
are all preserved. Primality is separate from real geometric membership. -/
theorem mem_halfProductPairs_iff_prime_realRegion
    {num den N : ℕ} {T : ℝ} {p : ℕ × ℕ} (hden : 0 < den) :
    p ∈ halfProductPairs num den N T ↔
      Nat.Prime p.1 ∧ Nat.Prime p.2 ∧
        halfProductRealRegion T (N : ℝ) ((num : ℝ) / (den : ℝ))
          ((p.1 : ℝ), (p.2 : ℝ)) := by
  rcases p with ⟨r, q⟩
  rw [mem_halfProductPairs]
  constructor
  · rintro ⟨hr, hq, hrq, hpow, hT, hN⟩
    refine ⟨hr, hq, ?_, ?_, Nat.cast_le.mpr hrq, (nat_pow_lt_iff_rpow_lt hden).mp hpow⟩
    · simpa only [Nat.cast_mul] using hT
    · change (r : ℝ) * (q : ℝ) ≤ (N : ℝ)
      exact_mod_cast hN
  · rintro ⟨hr, hq, hT, hN, hrq, hpow⟩
    refine ⟨hr, hq, Nat.cast_le.mp hrq, (nat_pow_lt_iff_rpow_lt hden).mpr hpow, ?_, ?_⟩
    · simpa only [Nat.cast_mul] using hT
    · change (r : ℝ) * (q : ℝ) ≤ (N : ℝ) at hN
      change r * q ≤ N
      exact_mod_cast hN

/-- Natural points of a crossing cell lie in the finite four-collar union.
The ambient caps are explicit; the diagonal cap follows from its own
squared bound and is not silently identified with the larger `Qcap`. -/
theorem multiplicativeBoundaryCell_nat_mem_collar
    {R Q δ T N b : ℝ} {a c : ℝ × ℝ} {p : ℕ × ℕ} {Rcap Qcap S : ℕ}
    (hR : 0 < R) (hQ : 0 < Q) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : multiplicativeBoundaryCell R Q (1 + δ) a)
    (hA : halfProductRealRegion T N b a)
    (hc : multiplicativeBoundaryCell R Q (1 + δ) c)
    (hC : ¬ halfProductRealRegion T N b c)
    (hp : multiplicativeBoundaryCell R Q (1 + δ) ((p.1 : ℝ), (p.2 : ℝ)))
    (hrcap : 1 ≤ p.1 ∧ p.1 ≤ Rcap) (hqcap : 1 ≤ p.2 ∧ p.2 ≤ Qcap)
    (hS : (1 + δ) ^ 4 * N ≤ (S : ℝ) ^ 2) :
    p ∈ halfProductBoundaryCollar Rcap Qcap S (3 * δ) T N b := by
  have h := multiplicativeBoundaryCell_crossing hR hQ hδ hδ1 hb hb1 ha hA hc hC hp
  apply (mem_halfProductBoundaryCollar p Rcap Qcap S (3 * δ) T N b).mpr
  refine ⟨⟨hrcap, hqcap⟩, ?_⟩
  rcases h with h | h | ⟨hdiag, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have hle : (p.2 : ℝ) ≤ (S : ℝ) := by
      have hp0 : (0 : ℝ) ≤ (p.2 : ℝ) := Nat.cast_nonneg p.2
      have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
      nlinarith only [hdiag, hS, hp0, hS0]
    have hleNat : p.2 ≤ S := by exact_mod_cast hle
    exact Or.inr (Or.inr (Or.inl ⟨hleNat, h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The actual finite point count for any selection from a crossing cell.
Its collar containment is proved above, rather than supplied as a hypothesis.
All grid-endpoint lattice errors are the explicit slice `+1` terms in the
existing budget; there is no primality restriction on the counted points. -/
theorem multiplicativeBoundaryCell_card_le_budget
    (B : Finset (ℕ × ℕ)) {R Q δ T N b : ℝ} {a c : ℝ × ℝ} {Rcap Qcap S : ℕ}
    (hR : 0 < R) (hQ : 0 < Q) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (ha : multiplicativeBoundaryCell R Q (1 + δ) a)
    (hA : halfProductRealRegion T N b a)
    (hc : multiplicativeBoundaryCell R Q (1 + δ) c)
    (hC : ¬ halfProductRealRegion T N b c)
    (hB : ∀ p ∈ B,
      multiplicativeBoundaryCell R Q (1 + δ) ((p.1 : ℝ), (p.2 : ℝ)))
    (hrcap : ∀ p ∈ B, 1 ≤ p.1 ∧ p.1 ≤ Rcap)
    (hqcap : ∀ p ∈ B, 1 ≤ p.2 ∧ p.2 ≤ Qcap)
    (hS : (1 + δ) ^ 4 * N ≤ (S : ℝ) ^ 2) :
    (B.card : ℝ) ≤ boundaryGridBudget Rcap Qcap S (3 * δ) T N b := by
  apply card_le_boundaryGridBudget B Rcap Qcap S (3 * δ) T N b
    (by linarith) hT hN
  intro p hp
  exact multiplicativeBoundaryCell_nat_mem_collar hR hQ hδ hδ1 hb hb1 ha hA hc hC
    (hB p hp) (hrcap p hp) (hqcap p hp) hS

end

end ImbalancedChen
