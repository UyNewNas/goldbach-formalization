import ImbalancedChen.P5PresievedRoughEndpointAllocation
import ImbalancedChen.P5ZU1011OriginalFifteenJointSelectedSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

REAL upper-endpoint support for the ORIGINAL four-prefix bit masks plus
rough slots. Inputs are the literal full/selected-complement affine square
inequalities and full-prefix+rough exponent budget. D-well support for the
actual full and actual selected-complement label words is a CONCLUSION.
This permits whole-atom greedy allocation without an arithmetic seed.
-/
namespace ImbalancedChen.P5Z.SelectedRealEndpointSupport
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open PresievedRoughSlotAffineGates PresievedRoughEndpointAllocation
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def front : List (Fin 4) := [0, 1, 2, 3]

def selectedFront (p : Policy) : List (Fin 4) := front.filter (fun i => decide (Selected p i))

def remainderFront (p : Policy) : List (Fin 4) :=
  U1011OriginalFifteenJointSelectedSupport.remainderSlots p

theorem front_partition (p : Policy) : (selectedFront p ++ remainderFront p).Perm front := by
  simpa [selectedFront, remainderFront, front, U1011OriginalFifteenJointSelectedSupport.remainderSlots] using
    List.filter_append_perm (fun i : Fin 4 => decide (Selected p i)) front

theorem selected_sum (p : Policy) (u : Fin 4 → ℝ) :
    ((selectedFront p).map u).sum = selectedMass p u := by
  by_cases h0 : Selected p 0 <;> by_cases h1 : Selected p 1 <;>
    by_cases h2 : Selected p 2 <;> by_cases h3 : Selected p 3
  all_goals simp [selectedFront, front, selectedMass, Fin.sum_univ_four, h0, h1, h2, h3]

theorem selected_remainder_sum (p : Policy) (u : Fin 4 → ℝ) :
    selectedMass p u + ((remainderFront p).map u).sum = ∑ i : Fin 4, u i := by
  have h := ((front_partition p).map u).sum_eq
  simpa only [List.map_append, List.sum_append, selected_sum, front,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Fin.sum_univ_four] using h

theorem remainder_log_squares (p : Policy) (u : Fin 4 → ℝ) (level : ℝ)
    (hg : ∀ j : Fin 4, ¬Selected p j → selectedSquare p j u ≤ level) :
    ∀ i : ℕ, ∀ hi : i < (remainderFront p).length,
      ((((remainderFront p).take i).map u).sum + 2 * u (remainderFront p)[i]) ≤ level - selectedMass p u := by
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  intro i hi
  by_cases h0 : Selected p 0 <;> by_cases h1 : Selected p 1 <;>
    by_cases h2 : Selected p 2 <;> by_cases h3 : Selected p 3
  all_goals simp [remainderFront, U1011OriginalFifteenJointSelectedSupport.remainderSlots,
    h0, h1, h2, h3] at hi ⊢
  all_goals interval_cases i <;> simp_all [selectedSquare, selectedMass, Fin.sum_univ_four] <;> linarith

theorem front_log_squares (u : Fin 4 → ℝ) (level : ℝ)
    (hg : ∀ j : Fin 4, fullSquare j u ≤ level) :
    ∀ i : ℕ, ∀ hi : i < front.length,
      (((front.take i).map u).sum + 2 * u front[i]) ≤ level := by
  have g0 := hg 0
  have g1 := hg 1
  have g2 := hg 2
  have g3 := hg 3
  intro i hi
  simp [front] at hi
  interval_cases i <;> simp_all [front, fullSquare, Fin.sum_univ_four]

theorem endpoint_list_product {α : Type*} {N : ℕ} (hN : 1 < N) (u : α → ℝ) (l : List α) :
    (l.map (fun i => (N : ℝ) ^ u i)).prod = (N : ℝ) ^ (l.map u).sum := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, Real.rpow_add hn, ih]

theorem log_squares_support {α : Type*} {N : ℕ} (hN : 1 < N) (u : α → ℝ) (l : List α) (level : ℝ)
    (hg : ∀ i : ℕ, ∀ hi : i < l.length, ((l.take i).map u).sum + 2 * u l[i] ≤ level) :
    PrefixSquareBound (fun i => (N : ℝ) ^ u i) ((N : ℝ) ^ level) l := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  intro i hi
  have hsq : ((N : ℝ) ^ u l[i]) ^ 2 = (N : ℝ) ^ (2 * u l[i]) := by
    rw [mul_comm (2 : ℝ), Real.rpow_mul hnpos.le, Real.rpow_natCast]
  rw [endpoint_list_product hN, hsq, ← Real.rpow_add hnpos]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (hg i hi)

private theorem mapped_support {α β : Type*} (f : α → β) (weight : β → ℝ)
    (l : List α) (D : ℝ) (h : PrefixSquareBound (fun i => weight (f i)) D l) :
    PrefixSquareBound weight D (l.map f) := by
  intro i hi
  have hs := h i (by simpa only [List.length_map] using hi)
  simpa only [← List.map_take, List.map_map, List.getElem_map, Function.comp_def] using hs

private theorem append_support {α : Type*} (weight : α → ℝ) (l t : List α) (D R : ℝ)
    (hl : PrefixSquareBound weight D l) (ht : PrefixSquareBound weight R t)
    (hpos : 0 ≤ (l.map weight).prod) (hbudget : (l.map weight).prod * R ≤ D) :
    PrefixSquareBound weight D (l ++ t) := by
  intro i hi
  by_cases hfront : i < l.length
  · have hs := hl i hfront
    have htake : (l ++ t).take i = l.take i := List.take_append_of_le_length (by omega)
    simpa only [htake, List.getElem_append_left hfront] using hs
  · let k := i - l.length
    have hk : k < t.length := by dsimp [k]; simp only [List.length_append] at hi; omega
    have heq : i = l.length + k := by dsimp [k]; omega
    rw [heq]
    have htake : (l ++ t).take (l.length + k) = l ++ t.take k := by
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    have hget : (l ++ t)[l.length + k] = t[k] := by
      simpa only [Nat.add_comm] using (List.getElem_append_right' l hk).symm
    rw [htake, hget, List.map_append, List.prod_append]
    have h := mul_le_mul_of_nonneg_left (ht k hk) hpos
    exact (by simpa only [mul_assoc] using h).trans hbudget

def wholeLabels (r : ℕ) : List (Fin 4 ⊕ Fin r) := front.map Sum.inl ++ (List.finRange r).map Sum.inr

def remainingLabels (p : Policy) (r : ℕ) : List (Fin 4 ⊕ Fin r) :=
  (remainderFront p).map Sum.inl ++ (List.finRange r).map Sum.inr

def exponent {r : ℕ} (u : Fin 4 → ℝ) (v : Fin r → ℝ) : Fin 4 ⊕ Fin r → ℝ := Sum.elim u v

/-- Full AND selected-complement REAL endpoint D-well support are proved
from the original log squares and original physical residual budget.
There is no arithmetic source or prime-seed hypothesis. -/
theorem original_endpoint_append_support {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : Fin 4 → ℝ) (v : Fin r → ℝ) (level ell : ℝ)
    (hfull : ∀ j : Fin 4, fullSquare j u ≤ level)
    (hselected : ∀ j : Fin 4, ¬Selected p j → selectedSquare p j u ≤ level)
    (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < ell)
    (hbudget : (∑ i : Fin 4, u i) + ell ≤ level) :
    PrefixSquareBound (fun i => (N : ℝ) ^ exponent u v i) ((N : ℝ) ^ level) (wholeLabels r) ∧
    PrefixSquareBound (fun i => (N : ℝ) ^ exponent u v i)
      ((N : ℝ) ^ (level - selectedMass p u)) (remainingLabels p r) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  let weight := fun i : Fin 4 ⊕ Fin r => (N : ℝ) ^ exponent u v i
  have hr := endpoints_original_dwell hN v ell hv0 hvanti hcubes
  have ht : PrefixSquareBound weight ((N : ℝ) ^ ell) ((List.finRange r).map Sum.inr) :=
    mapped_support Sum.inr weight _ _ hr
  have hfront (l : List (Fin 4)) (D : ℝ)
      (hlog : ∀ i : ℕ, ∀ hi : i < l.length, ((l.take i).map u).sum + 2 * u l[i] ≤ D)
      (hb : (l.map u).sum + ell ≤ D) :
      PrefixSquareBound weight ((N : ℝ) ^ D) (l.map Sum.inl ++ (List.finRange r).map Sum.inr) := by
    have hl := mapped_support Sum.inl weight l ((N : ℝ) ^ D) (log_squares_support hN u l D hlog)
    apply append_support weight _ _ _ _ hl ht
    · apply List.prod_nonneg
      intro z hz
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
      exact Real.rpow_nonneg hnpos.le _
    · have heq : ((l.map Sum.inl).map weight).prod = (N : ℝ) ^ (l.map u).sum := by
        simpa only [List.map_map, Function.comp_def, weight, exponent, Sum.elim_inl] using endpoint_list_product hN u l
      rw [heq, ← Real.rpow_add hnpos]
      exact Real.rpow_le_rpow_of_exponent_le hn.le hb
  refine ⟨hfront front level (front_log_squares u level hfull) ?_,
    hfront (remainderFront p) (level - selectedMass p u) (remainder_log_squares p u level hselected) ?_⟩
  · simpa [front, Fin.sum_univ_four] using hbudget
  · linarith [selected_remainder_sum p u]

end
end ImbalancedChen.P5Z.SelectedRealEndpointSupport
