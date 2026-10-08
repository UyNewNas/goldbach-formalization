import ImbalancedChen.CurvedRegionDiscrepancy
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An actual finite boundary lattice-point budget

The manuscript's boundary estimate counts integer pairs in four collars:
the two product boundaries, the diagonal, and the power boundary. This
file proves that finite counting step, with an explicit `+1` for every
integer slice. The collars have inclusive endpoints and are not intersected
with the original curved source. In particular, exterior envelope points
and points above the original product cutoff are retained.

The product projection uses fibre cardinalities, not the indicator of its
image: different ordered pairs with the same product retain their full
multiplicity. Its total mass on any carrier containing its full support is
exactly the pair cardinality. The resulting budget can therefore be used
in the finite discrepancy comparison from `CurvedRegionDiscrepancy`.

This file does not construct a geometric grid or prove that its boundary
rectangles are contained in the collars. That containment is a genuine
geometric input, expressed as a subset, rather than an assumed mass bound.
No rectangle distribution theorem or asymptotic error estimate is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- A closed real interval of length `b - a` contains at most that length
plus one distinct natural numbers. No endpoint is rounded away. -/
theorem boundaryGrid_card_le_interval_length
    (s : Finset ℕ) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ n ∈ s, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) :
    (s.card : ℝ) ≤ b - a + 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  · have hsub : s ⊆ Finset.Icc (s.min' hne) (s.max' hne) := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hmm := s.min'_le_max' hne
    have hc' : s.card + s.min' hne ≤ s.max' hne + 1 := by omega
    have hcR : (s.card : ℝ) + (s.min' hne : ℝ) ≤ (s.max' hne : ℝ) + 1 := by
      exact_mod_cast hc'
    have hmin := (hs _ (s.min'_mem hne)).1
    have hmax := (hs _ (s.max'_mem hne)).2
    linarith

/-- The `+1` term covers both closed endpoints, even for zero width. -/
theorem boundaryGrid_card_le_twice_width
    (s : Finset ℕ) (c w : ℝ) (hw : 0 ≤ w)
    (hs : ∀ n ∈ s, |(n : ℝ) - c| ≤ w) :
    (s.card : ℝ) ≤ 2 * w + 1 := by
  have h := boundaryGrid_card_le_interval_length s (c - w) (c + w)
    (by linarith) (fun n hn => by
      obtain ⟨hl, hu⟩ := abs_le.mp (hs n hn)
      constructor <;> linarith)
  linarith

/-- Count actual finite fibres by an integer coordinate. Injectivity is
required only within each fibre, so the statement applies to either
coordinate of a pair. -/
theorem boundaryGrid_card_le_sum_slice_widths {α : Type*}
    (B : Finset α) (I : Finset ℕ) (index value : α → ℕ)
    (center width : ℕ → ℝ)
    (hindex : ∀ x ∈ B, index x ∈ I)
    (hinj : ∀ x ∈ B, ∀ y ∈ B,
      index x = index y → value x = value y → x = y)
    (hwidth : ∀ i ∈ I, 0 ≤ width i)
    (hstrip : ∀ x ∈ B, |(value x : ℝ) - center (index x)| ≤ width (index x)) :
    (B.card : ℝ) ≤ ∑ i ∈ I, (2 * width i + 1) := by
  classical
  have hcount : B.card = ∑ i ∈ I, (B.filter (fun x => index x = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x hx => hindex x hx)
  rw [hcount, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i hi
  let F := B.filter (fun x => index x = i)
  have himage : (F.image value).card = F.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact hinj x hx'.1 y hy'.1 (hx'.2.trans hy'.2.symm) hxy
  change (F.card : ℝ) ≤ _
  rw [← himage]
  apply boundaryGrid_card_le_twice_width _ _ _ (hwidth i hi)
  intro n hn
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
  have hx' := Finset.mem_filter.mp hx
  simpa only [hx'.2] using hstrip x hx'.1

/-- The product collar has width `2 η X / r` in the second coordinate.
Positivity of the first coordinate is explicit, including every division. -/
theorem boundaryGrid_product_collar_card_le
    (B : Finset (ℕ × ℕ)) (R : ℕ) (η X : ℝ)
    (hη : 0 ≤ η) (hX : 0 ≤ X)
    (hR : ∀ p ∈ B, 1 ≤ p.1 ∧ p.1 ≤ R)
    (hstrip : ∀ p ∈ B, |(p.1 : ℝ) * (p.2 : ℝ) - X| ≤ η * X) :
    (B.card : ℝ) ≤
      2 * η * X * (∑ r ∈ Finset.Icc 1 R, 1 / (r : ℝ)) + R := by
  have h := boundaryGrid_card_le_sum_slice_widths B (Finset.Icc 1 R)
    Prod.fst Prod.snd (fun r => X / (r : ℝ)) (fun r => η * X / (r : ℝ))
    (fun p hp => Finset.mem_Icc.mpr (hR p hp))
    (fun _ _ _ _ hfst hsnd => Prod.ext hfst hsnd)
    (fun r _ => div_nonneg (mul_nonneg hη hX) (Nat.cast_nonneg r))
    (fun p hp => by
      have hr : (0 : ℝ) < p.1 := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hR p hp).1)
      have heq : (p.2 : ℝ) - X / (p.1 : ℝ) =
          ((p.1 : ℝ) * (p.2 : ℝ) - X) / (p.1 : ℝ) := by
        field_simp [ne_of_gt hr] <;> ring
      rw [heq, abs_div, abs_of_pos hr]
      exact div_le_div_of_nonneg_right (hstrip p hp) hr.le)
  refine h.trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- A graph collar is counted by its second-coordinate slices. This
applies to the diagonal and to the genuine real-power curve. -/
theorem boundaryGrid_graph_collar_card_le
    (B : Finset (ℕ × ℕ)) (Q : ℕ) (η : ℝ) (g : ℕ → ℝ)
    (hη : 0 ≤ η) (hg : ∀ q ∈ Finset.Icc 1 Q, 0 ≤ g q)
    (hQ : ∀ p ∈ B, 1 ≤ p.2 ∧ p.2 ≤ Q)
    (hstrip : ∀ p ∈ B, |(p.1 : ℝ) - g p.2| ≤ η * g p.2) :
    (B.card : ℝ) ≤ 2 * η * (∑ q ∈ Finset.Icc 1 Q, g q) + Q := by
  have h := boundaryGrid_card_le_sum_slice_widths B (Finset.Icc 1 Q)
    Prod.snd Prod.fst g (fun q => η * g q)
    (fun p hp => Finset.mem_Icc.mpr (hQ p hp))
    (fun _ _ _ _ hsnd hfst => Prod.ext hfst hsnd)
    (fun q hq => mul_nonneg hη (hg q hq)) hstrip
  refine h.trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The full four-collar union in an integer box. Points need not satisfy
`r ≤ q`, `q ^ b < r`, or `T ≤ r*q ≤ N`: exterior mass is intentional.
The independent diagonal cap `S` retains its smaller endpoint error. -/
def halfProductBoundaryCollar (R Q S : ℕ) (η T N b : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 R).product (Finset.Icc 1 Q)).filter fun (p : ℕ × ℕ) =>
    |(p.1 : ℝ) * (p.2 : ℝ) - T| ≤ η * T ∨
    |(p.1 : ℝ) * (p.2 : ℝ) - N| ≤ η * N ∨
    (p.2 ≤ S ∧ |(p.1 : ℝ) - (p.2 : ℝ)| ≤ η * (p.2 : ℝ)) ∨
    |(p.1 : ℝ) - (p.2 : ℝ) ^ b| ≤ η * (p.2 : ℝ) ^ b

@[simp] theorem mem_halfProductBoundaryCollar
    (p : ℕ × ℕ) (R Q S : ℕ) (η T N b : ℝ) :
    p ∈ halfProductBoundaryCollar R Q S η T N b ↔
      ((1 ≤ p.1 ∧ p.1 ≤ R) ∧ (1 ≤ p.2 ∧ p.2 ≤ Q)) ∧
      (|(p.1 : ℝ) * (p.2 : ℝ) - T| ≤ η * T ∨
        |(p.1 : ℝ) * (p.2 : ℝ) - N| ≤ η * N ∨
        (p.2 ≤ S ∧ |(p.1 : ℝ) - (p.2 : ℝ)| ≤ η * (p.2 : ℝ)) ∨
        |(p.1 : ℝ) - (p.2 : ℝ) ^ b| ≤ η * (p.2 : ℝ) ^ b) := by
  simp only [halfProductBoundaryCollar, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Icc]

/-- The finite version of the manuscript's four-boundary estimate. -/
def boundaryGridBudget (R Q S : ℕ) (η T N b : ℝ) : ℝ :=
  2 * η * (T + N) * (∑ r ∈ Finset.Icc 1 R, 1 / (r : ℝ)) +
    2 * η * (∑ q ∈ Finset.Icc 1 S, (q : ℝ)) +
    2 * η * (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ^ b) +
    2 * (R : ℝ) + S + Q

/-- Overlaps between collars cause no problem: the cardinality of their
union is bounded above, rather than assumed to be an additive partition. -/
theorem card_le_boundaryGridBudget
    (B : Finset (ℕ × ℕ)) (R Q S : ℕ) (η T N b : ℝ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : B ⊆ halfProductBoundaryCollar R Q S η T N b) :
    (B.card : ℝ) ≤ boundaryGridBudget R Q S η T N b := by
  classical
  let BT := B.filter fun (p : ℕ × ℕ) => |(p.1 : ℝ) * (p.2 : ℝ) - T| ≤ η * T
  let BN := B.filter fun (p : ℕ × ℕ) => |(p.1 : ℝ) * (p.2 : ℝ) - N| ≤ η * N
  let BD := B.filter fun (p : ℕ × ℕ) => p.2 ≤ S ∧
    |(p.1 : ℝ) - (p.2 : ℝ)| ≤ η * (p.2 : ℝ)
  let BP := B.filter fun (p : ℕ × ℕ) =>
    |(p.1 : ℝ) - (p.2 : ℝ) ^ b| ≤ η * (p.2 : ℝ) ^ b
  have hmem p (hp : p ∈ B) :=
    (mem_halfProductBoundaryCollar p R Q S η T N b).mp (hB hp)
  have hcover : B ⊆ ((BT ∪ BN) ∪ BD) ∪ BP := by
    intro p hp
    simp only [BT, BN, BD, BP, Finset.mem_union, Finset.mem_filter]
    rcases (hmem p hp).2 with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl ⟨hp, h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hp, h⟩))
    · exact Or.inl (Or.inr ⟨hp, h⟩)
    · exact Or.inr ⟨hp, h⟩
  have hc : B.card ≤ BT.card + BN.card + BD.card + BP.card := by
    have hc0 := Finset.card_le_card hcover
    have hc1 := Finset.card_union_le ((BT ∪ BN) ∪ BD) BP
    have hc2 := Finset.card_union_le (BT ∪ BN) BD
    have hc3 := Finset.card_union_le BT BN
    omega
  have hcR : (B.card : ℝ) ≤ (BT.card : ℝ) + BN.card + BD.card + BP.card := by
    exact_mod_cast hc
  have hBT := boundaryGrid_product_collar_card_le BT R η T hη hT
    (fun p hp => (hmem p (Finset.mem_filter.mp hp).1).1.1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hBN := boundaryGrid_product_collar_card_le BN R η N hη hN
    (fun p hp => (hmem p (Finset.mem_filter.mp hp).1).1.1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hBD := boundaryGrid_graph_collar_card_le BD S η (fun q => (q : ℝ)) hη
    (fun q _ => Nat.cast_nonneg q)
    (fun p hp => ⟨(hmem p (Finset.mem_filter.mp hp).1).1.2.1,
      (Finset.mem_filter.mp hp).2.1⟩)
    (fun _ hp => (Finset.mem_filter.mp hp).2.2)
  have hBP := boundaryGrid_graph_collar_card_le BP Q η (fun q => (q : ℝ) ^ b) hη
    (fun q _ => Real.rpow_nonneg (Nat.cast_nonneg q) b)
    (fun p hp => (hmem p (Finset.mem_filter.mp hp).1).1.2)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  unfold boundaryGridBudget
  nlinarith

/-- Unconditional counting of the entire specified collar union. -/
theorem halfProductBoundaryCollar_card_le
    (R Q S : ℕ) (η T N b : ℝ) (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N) :
    ((halfProductBoundaryCollar R Q S η T N b).card : ℝ) ≤
      boundaryGridBudget R Q S η T N b :=
  card_le_boundaryGridBudget _ R Q S η T N b hη hT hN (fun _ h => h)

/-- An elementary closed-form version: harmonic slices cost `1 + log R`,
and graph slices cost at most the cap times the largest height. The
expression `Q * Q ^ b` also works at `Q = 0`, without a hidden positive-cap
assumption. Choosing geometric caps is deliberately left to the caller. -/
theorem boundaryGridBudget_le_log_power
    (R Q S : ℕ) (η T N b : ℝ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N) (hb : 0 ≤ b) :
    boundaryGridBudget R Q S η T N b ≤
      2 * η * (T + N) * (1 + Real.log (R : ℝ)) +
        2 * η * (S : ℝ) ^ 2 + 2 * η * (Q : ℝ) * (Q : ℝ) ^ b +
        2 * (R : ℝ) + S + Q := by
  have hH : (∑ r ∈ Finset.Icc 1 R, 1 / (r : ℝ)) ≤
      1 + Real.log (R : ℝ) := by
    have heq : (∑ r ∈ Finset.Icc 1 R, 1 / (r : ℝ)) = (harmonic R : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div]
    rw [heq]
    exact harmonic_le_one_add_log R
  have hS : (∑ q ∈ Finset.Icc 1 S, (q : ℝ)) ≤ (S : ℝ) ^ 2 := by
    calc
      (∑ q ∈ Finset.Icc 1 S, (q : ℝ)) ≤ ∑ _q ∈ Finset.Icc 1 S, (S : ℝ) :=
        Finset.sum_le_sum fun q hq => Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2
      _ = _ := by simp [nsmul_eq_mul, pow_two]
  have hQ : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ^ b) ≤ (Q : ℝ) * (Q : ℝ) ^ b := by
    calc
      (∑ q ∈ Finset.Icc 1 Q, (q : ℝ) ^ b) ≤
          ∑ _q ∈ Finset.Icc 1 Q, (Q : ℝ) ^ b :=
        Finset.sum_le_sum fun q hq => Real.rpow_le_rpow (Nat.cast_nonneg q)
          (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2) hb
      _ = _ := by simp [nsmul_eq_mul]
  have hH' := mul_le_mul_of_nonneg_left hH
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη) (add_nonneg hT hN))
  have hS' := mul_le_mul_of_nonneg_left hS
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  have hQ' := mul_le_mul_of_nonneg_left hQ
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη)
  unfold boundaryGridBudget
  nlinarith

/-- Actual pair cardinality with no unevaluated slice sums. -/
theorem card_le_boundaryGrid_log_power
    (B : Finset (ℕ × ℕ)) (R Q S : ℕ) (η T N b : ℝ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N) (hb : 0 ≤ b)
    (hB : B ⊆ halfProductBoundaryCollar R Q S η T N b) :
    (B.card : ℝ) ≤
      2 * η * (T + N) * (1 + Real.log (R : ℝ)) +
        2 * η * (S : ℝ) ^ 2 + 2 * η * (Q : ℝ) * (Q : ℝ) ^ b +
        2 * (R : ℝ) + S + Q :=
  (card_le_boundaryGridBudget B R Q S η T N b hη hT hN hB).trans
    (boundaryGridBudget_le_log_power R Q S η T N b hη hT hN hb)

/-- The literal product convolution, retaining all ordered-pair
multiplicity, even when several pairs have the same product. -/
def pairProductWeight (B : Finset (ℕ × ℕ)) (m : ℕ) : ℝ :=
  ((B.filter fun (p : ℕ × ℕ) => p.1 * p.2 = m).card : ℝ)

theorem pairProductWeight_nonneg (B : Finset (ℕ × ℕ)) (m : ℕ) :
    0 ≤ pairProductWeight B m := Nat.cast_nonneg _

/-- The carrier contains the full product image, not only products in
the original curved source. This is an exact multiplicity identity. -/
theorem finiteSourceMass_pairProductWeight
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ)
    (hM : B.image (fun p => p.1 * p.2) ⊆ M) :
    finiteSourceMass M (pairProductWeight B) = (B.card : ℝ) := by
  classical
  have hc : B.card = ∑ m ∈ M, (B.filter (fun p => p.1 * p.2 = m)).card :=
    Finset.card_eq_sum_card_fiberwise (fun p hp => hM (Finset.mem_image_of_mem _ hp))
  unfold finiteSourceMass pairProductWeight
  exact_mod_cast hc.symm

/-- The explicit lattice-point budget bounds the actual convolution
mass, including exterior products and repeated products. -/
theorem finiteSourceMass_pairProductWeight_le_boundaryGridBudget
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ) (R Q S : ℕ) (η T N b : ℝ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : B ⊆ halfProductBoundaryCollar R Q S η T N b)
    (hM : B.image (fun p => p.1 * p.2) ⊆ M) :
    finiteSourceMass M (pairProductWeight B) ≤ boundaryGridBudget R Q S η T N b := by
  rw [finiteSourceMass_pairProductWeight B M hM]
  exact card_le_boundaryGridBudget B R Q S η T N b hη hT hN hB

/-- The finite boundary comparison with an actually proved geometric
mass budget. Neither the carrier nor the boundary is cut down to the
half-product source. -/
theorem abs_finitePrimitiveDiscrepancy_le_boundaryGridBudget
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ) (h : ℕ → ℝ)
    (R Q S : ℕ) (η T N b : ℝ) (a d : ℕ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : B ⊆ halfProductBoundaryCollar R Q S η T N b)
    (hM : B.image (fun p => p.1 * p.2) ⊆ M)
    (hh : ∀ m ∈ M, 0 ≤ h m) (hhu : ∀ m ∈ M, h m ≤ pairProductWeight B m) :
    |finitePrimitiveDiscrepancy M h a d| ≤
      |finitePrimitiveDiscrepancy M (pairProductWeight B) a d| +
        boundaryGridBudget R Q S η T N b / (Nat.totient d : ℝ) := by
  exact (abs_finitePrimitiveDiscrepancy_le_sourceMass M h (pairProductWeight B)
    a d hh hhu).trans (add_le_add le_rfl
      (div_le_div_of_nonneg_right
        (finiteSourceMass_pairProductWeight_le_boundaryGridBudget
          B M R Q S η T N b hη hT hN hB hM) (Nat.cast_nonneg _)))

/-- Summing over moduli multiplies the proved boundary budget by the
reciprocal-totient sum, not by the number of moduli. -/
theorem sum_abs_finitePrimitiveDiscrepancy_le_boundaryGridBudget
    (B : Finset (ℕ × ℕ)) (D M : Finset ℕ) (h : ℕ → ℝ)
    (R Q S : ℕ) (η T N b : ℝ) (a : ℕ → ℕ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hB : B ⊆ halfProductBoundaryCollar R Q S η T N b)
    (hM : B.image (fun p => p.1 * p.2) ⊆ M)
    (hh : ∀ m ∈ M, 0 ≤ h m) (hhu : ∀ m ∈ M, h m ≤ pairProductWeight B m) :
    (∑ d ∈ D, |finitePrimitiveDiscrepancy M h (a d) d|) ≤
      (∑ d ∈ D, |finitePrimitiveDiscrepancy M (pairProductWeight B) (a d) d|) +
        boundaryGridBudget R Q S η T N b *
          (∑ d ∈ D, 1 / (Nat.totient d : ℝ)) := by
  exact (sum_abs_finitePrimitiveDiscrepancy_le_sourceMass D M h (pairProductWeight B)
    a hh hhu).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right
        (finiteSourceMass_pairProductWeight_le_boundaryGridBudget
          B M R Q S η T N b hη hT hN hB hM)
        (Finset.sum_nonneg fun d _ => div_nonneg zero_le_one (Nat.cast_nonneg _))))

end

end ImbalancedChen
