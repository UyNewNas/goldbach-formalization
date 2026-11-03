import ImbalancedChen.P4AFiniteCapTaggedConstructor
import ImbalancedChen.P4AOriginalFull87SourceDispatch

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED.

Actual full87 source caps are converted to a fixed finite scalar alphabet.
A positive one-step buffer is subtracted even on exact grid boundaries.
Every accepted candidate satisfies every original full/selected square,
the selected licence and the original comparison-cap improvement.
Every rejected original action is localized to one of its own finitely
many comparison/square collars. None is declared a null equality region.

The result is an ancestor-frozen Option candidate. `none` means inherit;
it does not erase an earlier policy. The actual full-sixth parent and
the arithmetic mass payment of these approximation collars are not
asserted or replaced by a licence record.
-/

namespace ImbalancedChen.P4AOriginalFull87FiniteCapCandidates

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P4AOriginalFull87SourceDictionary
open P4AOriginalFull87SourceDispatch

def step (m : ℕ) : ℝ := (299 / 500 : ℝ) / ((m : ℝ) + 1)

theorem step_pos (m : ℕ) : 0 < step m := by unfold step; positivity

theorem step_mul (m : ℕ) : step m * ((m : ℝ) + 1) = (299 / 500 : ℝ) := by
  exact div_mul_cancel₀ _ (by positivity : (m : ℝ) + 1 ≠ 0)

/-- The scalar mesh and its strictly positive buffer can be chosen
before every N and every source point. -/
theorem exists_small_step (eta : ℝ) (heta : 0 < eta) :
    ∃ m : ℕ, 0 < step m ∧ 2 * step m < eta := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((2 * (299 / 500 : ℝ)) / eta)
  have hmul := (div_lt_iff₀ heta).mp hm
  refine ⟨m, step_pos m, ?_⟩
  unfold step
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
  nlinarith

/-- One pre-N finite scalar table; its size does not depend on N. -/
def values (m : ℕ) (i : Fin (m + 2)) : ℝ := step m * (i.val : ℝ) - step m

theorem values_le (m : ℕ) (i : Fin (m + 2)) : values m i ≤ (299 / 500 : ℝ) := by
  have hi : i.val ≤ m + 1 := by omega
  have hir : (i.val : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hi
  have hh := mul_le_mul_of_nonneg_left hir (step_pos m).le
  rw [step_mul] at hh
  unfold values
  linarith [step_pos m]

theorem boundedCap_values (m : ℕ) (i : Fin (m + 2)) :
    P4AFiniteCapTaggedConstructor.boundedCap (values m) i = values m i :=
  P4AFiniteCapTaggedConstructor.boundedCap_eq _ _ (values_le m i)

def index (m : ℕ) (x : ℝ) : Fin (m + 2) :=
  ⟨min (m + 1) ⌊x / step m⌋₊, by have hh := min_le_left (m + 1) ⌊x / step m⌋₊; omega⟩

def rounded (m : ℕ) (x : ℝ) : ℝ := values m (index m x)

/-- Exact grid ties still have a positive buffer. The error interval is
[step, 2*step), rather than an unbuffered [0,step) interval. -/
theorem rounded_error (m : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxmax : x ≤ (299 / 500 : ℝ)) :
    step m ≤ x - rounded m x ∧ x - rounded m x < 2 * step m := by
  have hs := step_pos m
  have hx0 : 0 ≤ x / step m := div_nonneg hx hs.le
  have hxl : x / step m ≤ (m : ℝ) + 1 := by
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_comm, step_mul] using hxmax
  have hf := Nat.floor_le hx0
  have hfn : ⌊x / step m⌋₊ ≤ m + 1 := by
    exact_mod_cast hf.trans hxl
  have hlo : step m * (⌊x / step m⌋₊ : ℝ) ≤ x := by
    have hh := (le_div_iff₀ hs).mp hf
    simpa only [mul_comm] using hh
  have hhi : x < step m * ((⌊x / step m⌋₊ : ℝ) + 1) := by
    have hh := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (x / step m))
    simpa only [mul_comm] using hh
  simp only [rounded, values, index, min_eq_right hfn]
  constructor <;> linarith

theorem rounded_lt (m : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxmax : x ≤ (299 / 500 : ℝ)) :
    rounded m x < x := by
  have he := (rounded_error m x hx hxmax).1
  linarith [step_pos m]

def accepted (m : ℕ) (c : Cell) (t : Point) : Prop :=
  comparison c t < rounded m (newCap c t) ∧
  (∀ j, prefixSquareExpr t j < rounded m (newCap c t)) ∧
  (∀ j ∉ selected c, selectedSquareExpr (selected c) t j < rounded m (newCap c t))

/-- The original full87 source itself supplies positivity and its fixed
153/256 ceiling; these are not inputs about a separately invented cap. -/
theorem source_rounded_error (m : ℕ) {c : Cell} {t : Point} (hs : Source c t) :
    step m ≤ newCap c t - rounded m (newCap c t) ∧
      newCap c t - rounded m (newCap c t) < 2 * step m :=
  rounded_error m _ (source_cap_positive hs).le
    ((source_physical_ceiling hs).le.trans (by norm_num))

theorem source_rounded_licence (m : ℕ) {c : Cell} {t : Point} (hs : Source c t) :
    rounded m (newCap c t) < v (∑ j ∈ selected c, t j) :=
  (rounded_lt m _ (source_cap_positive hs).le
    ((source_physical_ceiling hs).le.trans (by norm_num))).trans
      (source_selected_license hs)

theorem accepted_original_gates (m : ℕ) {c : Cell} {t : Point}
    (hs : Source c t) (ha : accepted m c t) :
    comparison c t < rounded m (newCap c t) ∧
      rounded m (newCap c t) < v (∑ j ∈ selected c, t j) ∧
      (∀ j, prefixSquareExpr t j < rounded m (newCap c t)) ∧
      (∀ j ∉ selected c, selectedSquareExpr (selected c) t j < rounded m (newCap c t)) :=
  ⟨ha.1, source_rounded_licence m hs, ha.2⟩

/-- This is actual complete rejection coverage, retaining all original
full and selected-complement rows. The later arithmetic supplier must pay
these collars; they have not been declared zero by pointwise convergence. -/
theorem rejected_source_in_collars (m : ℕ) {c : Cell} {t : Point}
    (hs : Source c t) (ha : ¬accepted m c t) :
    (0 < newCap c t - comparison c t ∧
      newCap c t - comparison c t < 2 * step m) ∨
    (∃ j, 0 < newCap c t - prefixSquareExpr t j ∧
      newCap c t - prefixSquareExpr t j < 2 * step m) ∨
    (∃ j, j ∉ selected c ∧ 0 < newCap c t - selectedSquareExpr (selected c) t j ∧
      newCap c t - selectedSquareExpr (selected c) t j < 2 * step m) := by
  have herr := (source_rounded_error m hs).2
  have hfull := (source_full_selected hs).1
  have hsel := (source_full_selected hs).2
  by_cases hc : comparison c t < rounded m (newCap c t)
  · by_cases hf : ∀ j, prefixSquareExpr t j < rounded m (newCap c t)
    · have hn : ¬∀ j ∉ selected c,
          selectedSquareExpr (selected c) t j < rounded m (newCap c t) :=
        fun hh => ha ⟨hc, hf, hh⟩
      push_neg at hn
      obtain ⟨j, hj, hbad⟩ := hn
      right; right
      refine ⟨j, hj, sub_pos.mpr (hsel j hj), ?_⟩
      linarith
    · push_neg at hf
      obtain ⟨j, hbad⟩ := hf
      right; left
      refine ⟨j, sub_pos.mpr (hfull j), ?_⟩
      linarith
  · left
    have hbad := le_of_not_gt hc
    exact ⟨sub_pos.mpr (source_improvement_terminal hs).1, by linarith⟩

/-- None is the inherited case, including every rejected near-wall
candidate. The constructor never chooses a different owner on rejection. -/
def selectedIndex (m : ℕ) (N : ℝ) (pre : List ℕ) : Option (Fin (m + 2)) :=
  (ownerAtPrefix N pre).bind fun c =>
    if accepted m c (point8 N pre) then some (index m (newCap c (point8 N pre))) else none

def selectedScalar (m : ℕ) (N : ℝ) (pre : List ℕ) : Option ℝ :=
  (selectedIndex m N pre).map (values m)

theorem selectedIndex_append (m : ℕ) (N : ℝ) (later pre : List ℕ)
    (hl : 8 ≤ pre.length) : selectedIndex m N (later ++ pre) = selectedIndex m N pre := by
  simp only [selectedIndex, ownerAtPrefix_append N later pre hl, point8_append N later pre hl]

theorem selectedScalar_append (m : ℕ) (N : ℝ) (later pre : List ℕ)
    (hl : 8 ≤ pre.length) : selectedScalar m N (later ++ pre) = selectedScalar m N pre := by
  simp only [selectedScalar, selectedIndex_append m N later pre hl]

theorem selectedScalar_of_source (m : ℕ) (N : ℝ) (pre : List ℕ)
    (hl : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (ha : accepted m c (primeHistoryLogCoordinates N 8 pre)) :
    selectedScalar m N pre = some (rounded m (newCap c (primeHistoryLogCoordinates N 8 pre))) := by
  unfold selectedScalar selectedIndex
  rw [(ownerAtPrefix_rank_eight N pre hl c).mpr hs]
  simp only [Option.bind_some, point8, rosserAncestor_self_of_length 8 pre hl,
    if_pos ha, Option.map_some, rounded]

theorem selectedScalar_rejected (m : ℕ) (N : ℝ) (pre : List ℕ)
    (hl : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (ha : ¬accepted m c (primeHistoryLogCoordinates N 8 pre)) : selectedScalar m N pre = none := by
  unfold selectedScalar selectedIndex
  rw [(ownerAtPrefix_rank_eight N pre hl c).mpr hs]
  simp only [Option.bind_some, point8, rosserAncestor_self_of_length 8 pre hl,
    if_neg ha, Option.map_none]

theorem selectedScalar_mem_alphabet (m : ℕ) (N : ℝ) (pre : List ℕ) (a : ℝ)
    (ha : selectedScalar m N pre = some a) :
    a ∈ P4AFiniteCapTaggedConstructor.capAlphabet (values m) := by
  unfold selectedScalar at ha
  cases hi : selectedIndex m N pre with
  | none => simp [hi] at ha
  | some i =>
      simp only [hi, Option.map_some, Option.some.injEq] at ha
      rw [← ha, ← boundedCap_values m i]
      exact P4AFiniteCapTaggedConstructor.boundedCap_mem _ i

end
end ImbalancedChen.P4AOriginalFull87FiniteCapCandidates
