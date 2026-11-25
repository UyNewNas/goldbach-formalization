import ImbalancedChen.P2FiniteMarkedGamma5ActualRootCells
import ImbalancedChen.P2FiniteMarkedGamma5RadialNaturalMass
import ImbalancedChen.Part5OriginalH430EmittedWordBox
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

One ordinary radial payment for the original U4 selected-history sums.
The original root prime, dependent LevelIndex, positive levelMark and
complete old word remain literal. A fixed shape and old word have total
positive coefficient at most one: the old word determines the root prime,
and the existing emitted-history theorem supplies the within-root bound.

Only then are the finite pre-N shape, RootCode and split factors charged.
No estimate is summed once per moving root prime or history position.
The selected-history masks are retained as discrete coefficients here;
this is not their global smooth realization, a nonradial wall payment,
a J identification or a prime-product distribution licence.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate

noncomputable section
open Filter Finset Real
open P2EnhancedLowerPhysicalTransition (StepShape)
open Part5OriginalH430PhysicalRoots (Root)
open Part5OriginalH430FrozenRootRefinement (RootCode)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand)
open Part5OriginalH430RequestedBranches (edgeShape)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430EmittedWordBox
  (selectedWordMark actual_shape_word_mark occurrence_old)
open P2FiniteMarkedGamma5ActualRootCells
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open P2FiniteMarkedGamma5PhysicalExtension (physicalProfile_bounds)
open P2FiniteMarkedGamma5EulerWordBudget (finPhysicalProfile finToPhysical)
open P2FiniteMarkedGamma5RadialProfileCollar (radialWidth)
open P2FiniteMarkedGamma5RadialNaturalMass
open scoped Classical Topology BigOperators

/-- All shapes at the original at-most-430 emitted depth. This finite set
does not depend on N, any root prime, any word, or any selected subfamily. -/
def shapeWords : Finset (List StepShape) :=
  (range 431).biUnion fun d =>
    (univ : Finset (Fin d → StepShape)).image List.ofFn

theorem mem_shapeWords_of_length (s : List StepShape) (hs : s.length ≤ 430) :
    s ∈ shapeWords := by
  unfold shapeWords
  apply mem_biUnion.mpr
  refine ⟨s.length, mem_range.mpr (by omega), ?_⟩
  exact mem_image.mpr ⟨s.get, mem_univ _, List.ofFn_get s⟩

theorem level_shapes_mem {N n p dep : ℕ} {t : ℝ}
    (l : LevelIndex N n .U4 t p dep) :
    (levelOccurrence l).path.map edgeShape ∈ shapeWords := by
  have hlen := (history_facts (levelOccurrence_source l).1).2.1
  apply mem_shapeWords_of_length
  simp only [List.length_map]
  omega

private def shapeTerm {N : ℕ} (s : List StepShape) (w : List ℕ)
    (o : Occurrence N) : ℝ :=
  if o.path.map edgeShape = s ∧ o.current.old = w then mark o else 0

private theorem shapeTerm_nonneg {N : ℕ} (s : List StepShape) (w : List ℕ)
    (o : Occurrence N) : 0 ≤ shapeTerm s w o := by
  unfold shapeTerm
  split_ifs
  · exact (mark_pos o).le
  · exact le_rfl

private theorem selectedWordMark_eq_map {N : ℕ}
    (s : List StepShape) (w : List ℕ) (L : List (Occurrence N)) :
    selectedWordMark s w L = (L.map (shapeTerm s w)).sum := by
  induction L with
  | nil => rfl
  | cons o os ih =>
    change shapeTerm s w o + selectedWordMark s w os =
      shapeTerm s w o + (os.map (shapeTerm s w)).sum
    rw [ih]

private theorem sum_get_map {α : Type*} (L : List α) (f : α → ℝ) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  calc
    _ = (List.ofFn (fun i : Fin L.length => f (L.get i))).sum :=
      (Fin.sum_ofFn _).symm
    _ = _ := by
      change (List.ofFn (fun i : Fin L.length => f L[i.val])).sum = _
      rw [List.ofFn_getElem_eq_map]

private theorem selectedWordMark_filter_le {N : ℕ}
    (s : List StepShape) (w : List ℕ) (P : Occurrence N → Bool)
    (L : List (Occurrence N)) :
    selectedWordMark s w (L.filter P) ≤ selectedWordMark s w L := by
  induction L with
  | nil => exact le_rfl
  | cons o os ih =>
    cases hP : P o with
    | false =>
      have h := ih.trans
        (le_add_of_nonneg_left (shapeTerm_nonneg s w o))
      simpa only [List.filter_cons, hP, Bool.false_eq_true, if_false,
        selectedWordMark, shapeTerm] using h
    | true =>
      simpa only [List.filter_cons, hP, Bool.true_eq_true, if_true,
        selectedWordMark, shapeTerm] using
        add_le_add_left ih (shapeTerm s w o)

/-- Restrict positive original list positions to any actual level subset.
The existing selectedWordMark is a sum of the same mark, without signs. -/
private theorem level_shape_sum_le {N n p dep : ℕ} {t : ℝ}
    (B : Finset (LevelIndex N n .U4 t p dep))
    (s : List StepShape) (w : List ℕ) :
    (∑ l ∈ B,
      if (levelOccurrence l).path.map edgeShape = s ∧
        (levelOccurrence l).current.old = w then levelMark l else 0) ≤
      selectedWordMark s w (rootHistory N n .U4 t p) := by
  let L := levelRequests N n .U4 t p dep
  change (∑ l ∈ B, shapeTerm s w (L.get l)) ≤ _
  calc
    _ ≤ ∑ l : Fin L.length, shapeTerm s w (L.get l) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ B)
        (fun l _ _ => shapeTerm_nonneg s w (L.get l))
    _ = (L.map (shapeTerm s w)).sum := sum_get_map L _
    _ = selectedWordMark s w L := (selectedWordMark_eq_map s w L).symm
    _ ≤ _ := selectedWordMark_filter_le s w
      (fun o => decide (o.remaining = dep)) (rootHistory N n .U4 t p)

def shapePrefixWeight (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (s : List StepShape) (w : List ℕ) : ℝ :=
  ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
    if (levelOccurrence l).path.map edgeShape = s ∧
      (levelOccurrence l).current.old = w then levelMark l else 0

/-- The full positive p/position coefficient is at most one at a fixed
shape and old word. The head argument also handles the empty word:
no actual old word is empty, so that case contributes zero. -/
theorem shapePrefixWeight_le_one (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (s : List StepShape) (w : List ℕ) :
    shapePrefixWeight N n dep t c B s w ≤ 1 := by
  let A := originalRootCellBand N n .U4 t c
  let G := fun p : ℕ => ∑ l ∈ B p,
    if (levelOccurrence l).path.map edgeShape = s ∧
      (levelOccurrence l).current.old = w then levelMark l else 0
  have hz (p : ℕ) (hne : p ≠ w.headD 0) : G p = 0 := by
    dsimp only [G]
    apply sum_eq_zero
    intro l hl
    by_cases h : (levelOccurrence l).path.map edgeShape = s ∧
        (levelOccurrence l).current.old = w
    · have hw : w = p :: Part5OriginalH430EmittedWordBox.letters
          (levelOccurrence l).path :=
        h.2.symm.trans (occurrence_old (levelOccurrence_source l).1)
      have hp : p = w.headD 0 := by rw [hw]; rfl
      exact False.elim (hne hp)
    · simp only [if_neg h]
  change (∑ p ∈ A, G p) ≤ 1
  by_cases hp : w.headD 0 ∈ A
  · rw [sum_eq_single (w.headD 0) (fun p _ hne => hz p hne)
      (fun hnot => False.elim (hnot hp))]
    exact (level_shape_sum_le (B (w.headD 0)) s w).trans
      ((le_abs_self _).trans (actual_shape_word_mark .U4 t (w.headD 0) s w))
  · have hzero : (∑ p ∈ A, G p) = 0 :=
      sum_eq_zero (fun p hmem => hz p (fun he => hp (he ▸ hmem)))
    rw [hzero]
    exact zero_le_one

def prefixWeight (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (w : List ℕ) : ℝ :=
  ∑ p ∈ originalRootCellBand N n .U4 t c, ∑ l ∈ B p,
    if (levelOccurrence l).current.old = w then levelMark l else 0

theorem prefixWeight_nonneg (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) (w : List ℕ) :
    0 ≤ prefixWeight N n dep t c B w := by
  unfold prefixWeight
  apply sum_nonneg
  intro p hp
  apply sum_nonneg
  intro l hl
  split_ifs
  · exact (mark_pos (levelOccurrence l)).le
  · exact le_rfl

/-- A zero old rank is allowed in the ambient split sum. It has no actual
U4 history prefix, because the original root prime remains the first slot. -/
theorem prefixWeight_nil (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    prefixWeight N n dep t c B [] = 0 := by
  unfold prefixWeight
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro l hl
  have ho := occurrence_old (levelOccurrence_source l).1
  simp [ho]

/-- Exact finite partition of the original positive coefficient by shapes.
All occurrences remain in their original dependent LevelIndex. -/
theorem prefixWeight_eq_shape_sum (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) (w : List ℕ) :
    prefixWeight N n dep t c B w =
      ∑ s ∈ shapeWords, shapePrefixWeight N n dep t c B s w := by
  unfold prefixWeight shapePrefixWeight
  symm
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  have hs := level_shapes_mem l
  by_cases hw : (levelOccurrence l).current.old = w
  · simp [hw, hs]
  · simp [hw]

theorem prefixWeight_le_shapeCard (N n dep : ℕ) (t : ℝ) (c : RootCode n)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) (w : List ℕ) :
    prefixWeight N n dep t c B w ≤ (shapeWords.card : ℝ) := by
  rw [prefixWeight_eq_shape_sum]
  calc
    _ ≤ ∑ _s ∈ shapeWords, (1 : ℝ) :=
      sum_le_sum (fun s _ => shapePrefixWeight_le_one N n dep t c B s w)
    _ = _ := by simp

/-- Full coordinates retain the k old slots first, then the two fresh
slots and all r tail slots. This operation does not sort or erase them. -/
def tuplePrefix {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ) : List ℕ :=
  List.ofFn (fun i : Fin k => u (i.castAdd (2 + r)))

@[simp] theorem tuplePrefix_length {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ) :
    (tuplePrefix u).length = k := List.length_ofFn

abbrev Split := Fin (frozenSourceRankBound + 1) × Fin (frozenSourceRankBound + 1)

def admissibleSplit (s : Split) : Prop :=
  s.1.val + 2 + s.2.val ≤ frozenSourceRankBound

def outerSlice (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) : ℝ :=
  ∑ u ∈ naturalOuterTuples N k r logQ h,
    if old = tuplePrefix u then
      finPhysicalProfile logQ (N : ℝ) (radialWidth h)
        ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ))
    else 0

/-- Original root-prime and original marked-position sums. The only
extension is the previously constructed radial outer profile, restricted
to exactly the complete old word of that same position. -/
def selectedOuterMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, if admissibleSplit s then
      outerSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
        (levelOccurrence l).current.old
    else 0

/-- The same old-word restriction on the original bounded prime-tuple
enumerator. This is a discrete source weight, not a global smooth mask. -/
def boundedProfileWeight (N k r : ℕ) (logQ h : ℝ) (old : List ℕ)
    (v : Fin (k + (2 + r)) → Fin (2 * N + 1)) : ℝ :=
  if old = tuplePrefix (tupleValues v) then
    finPhysicalProfile logQ (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ))
  else 0

def boundedProfileSlice (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) : ℝ :=
  ∑ v ∈ Part3.labelledPrimeTuples (k + (2 + r)) (2 * N),
    boundedProfileWeight N k r logQ h old v

def boundedInnerSlice (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) : ℝ :=
  ∑ v ∈ Part3.labelledPrimeTuples (k + (2 + r)) (2 * N),
    if (Part3.labelledProduct v : ℝ) ≤ (N : ℝ) then
      boundedProfileWeight N k r logQ h old v
    else 0

/-- The existing natural-support image preserves the old-word filter too.
Zero profile values can be removed without changing this weighted sum. -/
theorem outerSlice_eq_bounded_outer (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) :
    outerSlice N k r logQ h old =
      ∑ v ∈ Part3.labelledPrimeTuples (k + (2 + r)) (2 * N),
        if (N : ℝ) < (Part3.labelledProduct v : ℝ) then
          boundedProfileWeight N k r logQ h old v
        else 0 := by
  calc
    _ = ∑ v ∈ P2FiniteMarkedGamma5RadialProfileCollar.profileOuterTuples
          N k r logQ h, boundedProfileWeight N k r logQ h old v := by
      unfold outerSlice naturalOuterTuples
      rw [sum_image
        (fun _ _ _ _ hvs => tupleValues_injective N (k + (2 + r)) hvs)]
      rfl
    _ = _ := by
      unfold P2FiniteMarkedGamma5RadialProfileCollar.profileOuterTuples
      rw [sum_filter]
      apply sum_congr rfl
      intro v hv
      by_cases hz : finPhysicalProfile logQ (N : ℝ) (radialWidth h)
          ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => ((v i).val : ℝ)) = 0
      · have hw : boundedProfileWeight N k r logQ h old v = 0 := by
          unfold boundedProfileWeight
          split_ifs <;> simp only [hz]
        simp [hz, hw]
      · simp [hz]

theorem boundedProfileSlice_split (N k r : ℕ) (logQ h : ℝ) (old : List ℕ) :
    boundedProfileSlice N k r logQ h old =
      boundedInnerSlice N k r logQ h old + outerSlice N k r logQ h old := by
  rw [outerSlice_eq_bounded_outer]
  unfold boundedProfileSlice boundedInnerSlice
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  by_cases hprod : (Part3.labelledProduct v : ℝ) ≤ (N : ℝ)
  · simp [hprod, not_lt_of_ge hprod]
  · simp [hprod, lt_of_not_ge hprod]

def selectedProfileMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, if admissibleSplit s then
      boundedProfileSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
        (levelOccurrence l).current.old
    else 0

def selectedInnerMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, if admissibleSplit s then
      boundedInnerSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
        (levelOccurrence l).current.old
    else 0

/-- Exact radial decomposition of the same actual-history profile sum.
The inner term is still a smooth profile sum, not ordinaryBad: identifying
its nonradial excess with sharp Gamma5 costs remains a separate task.
These are raw ordinary weights levelMark; no thetaConversion is removed. -/
theorem selectedProfileMass_split (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedProfileMass N n dep t h B =
      selectedInnerMass N n dep t h B + selectedOuterMass N n dep t h B := by
  unfold selectedProfileMass selectedInnerMass selectedOuterMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l hl
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro sp hsp
  by_cases ha : admissibleSplit sp
  · simp only [if_pos ha, boundedProfileSlice_split]
  · simp only [if_neg ha, add_zero]

private theorem history_sum_comm {ι : Type*} {N n dep : ℕ} {t : ℝ}
    (A : Finset ℕ) (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep))
    (I : Finset ι) (f : (p : ℕ) → LevelIndex N n .U4 t p dep → ι → ℝ) :
    (∑ p ∈ A, ∑ l ∈ B p, ∑ i ∈ I, f p l i) =
      ∑ i ∈ I, ∑ p ∈ A, ∑ l ∈ B p, f p l i := by
  calc
    _ = ∑ p ∈ A, ∑ i ∈ I, ∑ l ∈ B p, f p l i :=
      sum_congr rfl (fun p _ => sum_comm)
    _ = _ := sum_comm

/-- Same original Q on a root cell, with the actual p and all its dependent
positions preserved. No representative prime or new endpoint is chosen. -/
theorem selectedOuterMass_eq_cells (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedOuterMass N n dep t h B =
      ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B p, levelMark l *
          ∑ s : Split, if admissibleSplit s then
            outerSlice N s.1.val s.2.val (log (cellQ N n c)) h
              (levelOccurrence l).current.old
          else 0 := by
  calc
    _ = ∑ c : RootCode n, ∑ p ∈ originalRootCellBand N n .U4 t c,
        ∑ l ∈ B p, levelMark l *
          ∑ s : Split, if admissibleSplit s then
            outerSlice N s.1.val s.2.val (log (rootQ N n .U4 t p)) h
              (levelOccurrence l).current.old
          else 0 := by
      symm
      simp only [originalRootCellBand, sum_filter]
      rw [sum_comm]
      simp [selectedOuterMass]
    _ = _ := by
      apply sum_congr rfl
      intro c hc
      apply sum_congr rfl
      intro p hp
      rw [originalRootCellBand_Q hp]

/-- Exact full-tuple dictionary. The coefficient is an original positive
history sum; no product-image injectivity or mark normalization is assumed. -/
theorem selectedOuterMass_eq_prefix_sum (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedOuterMass N n dep t h B =
      ∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
        ∑ u ∈ naturalOuterTuples N s.1.val s.2.val (log (cellQ N n c)) h,
          prefixWeight N n dep t c B (tuplePrefix u) *
            finPhysicalProfile (log (cellQ N n c)) (N : ℝ) (radialWidth h)
              ((N : ℝ) ^ frozenLeafCutoffFloor) (fun i => (u i : ℝ))
      else 0 := by
  rw [selectedOuterMass_eq_cells]
  apply sum_congr rfl
  intro c hc
  simp_rw [mul_sum]
  rw [history_sum_comm]
  apply sum_congr rfl
  intro s hs
  by_cases ha : admissibleSplit s
  · simp only [if_pos ha, outerSlice]
    simp_rw [mul_sum]
    rw [history_sum_comm]
    apply sum_congr rfl
    intro u hu
    unfold prefixWeight
    rw [sum_mul]
    apply sum_congr rfl
    intro p hp
    rw [sum_mul]
    apply sum_congr rfl
    intro l hl
    split_ifs <;> simp
  · simp [ha]

theorem selectedOuterMass_le_ambient_sum (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) :
    selectedOuterMass N n dep t h B ≤ (shapeWords.card : ℝ) *
      ∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
        naturalOuterMass N s.1.val s.2.val (log (cellQ N n c)) h
      else 0 := by
  rw [selectedOuterMass_eq_prefix_sum]
  rw [mul_sum]
  apply sum_le_sum
  intro c hc
  rw [mul_sum]
  apply sum_le_sum
  intro s hs
  by_cases ha : admissibleSplit s
  · simp only [if_pos ha, naturalOuterMass, mul_sum]
    apply sum_le_sum
    intro u hu
    apply mul_le_mul_of_nonneg_right
      (prefixWeight_le_shapeCard N n dep t c B (tuplePrefix u))
    exact (physicalProfile_bounds (log (cellQ N n c)) (N : ℝ) (radialWidth h)
      ((N : ℝ) ^ frozenLeafCutoffFloor)
      (finToPhysical s.1.val s.2.val (fun i => (u i : ℝ)))).1
  · simp [ha]

/-- An exact finite cardinal factor, kept symbolic. It depends on the
fixed root precision n and original rank K, never on N or B. -/
def aggregateCard (n : ℕ) : ℕ :=
  shapeWords.card * Fintype.card (RootCode n) * Fintype.card Split

/-- One width pays the entire original positive selected-history radial
sum, for every depth, parameter and level subfamily after N. No epsilon
is paid separately for each moving root prime or history position. -/
theorem absolute_selected_outer_payment (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (dep : ℕ) (t : ℝ)
        (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          selectedOuterMass N n dep t h B ≤ ε := by
  let e := ε / ((aggregateCard n : ℝ) + 1)
  have hden : 0 < (aggregateCard n : ℝ) + 1 := by positivity
  have he' : 0 < e := div_pos he hden
  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_natural_outer_payment he'
  refine ⟨h, hp, h8, hw, hw1, ?_⟩
  filter_upwards [H, eventually_gt_atTop (1 : ℕ)] with N hpaid hN
  intro dep t B
  let z := P2FiniteMarkedGamma5RadialRoughMass.norm N
  have hz : 0 ≤ z :=
    div_nonneg (log_nonneg (by exact_mod_cast hN.le)) (Nat.cast_nonneg _)
  have hsum :
      (∑ c : RootCode n, ∑ s : Split, z *
        (if admissibleSplit s then
          naturalOuterMass N s.1.val s.2.val (log (cellQ N n c)) h
        else 0)) ≤
        (Fintype.card (RootCode n) : ℝ) * (Fintype.card Split : ℝ) * e := by
    calc
      _ ≤ ∑ _c : RootCode n, ∑ _s : Split, e := by
        apply sum_le_sum
        intro c hc
        apply sum_le_sum
        intro s hs
        by_cases ha : admissibleSplit s
        · simpa only [if_pos ha] using
            hpaid s.1.val s.2.val (log (cellQ N n c)) ha
        · simpa only [if_neg ha, mul_zero] using he'.le
      _ = _ := by
        simp only [sum_const, card_univ, nsmul_eq_mul]
        ring
  calc
    _ ≤ z * ((shapeWords.card : ℝ) *
        ∑ c : RootCode n, ∑ s : Split, if admissibleSplit s then
          naturalOuterMass N s.1.val s.2.val (log (cellQ N n c)) h
        else 0) :=
      mul_le_mul_of_nonneg_left
        (selectedOuterMass_le_ambient_sum N n dep t h B) hz
    _ = (shapeWords.card : ℝ) *
        (∑ c : RootCode n, ∑ s : Split, z *
          (if admissibleSplit s then
            naturalOuterMass N s.1.val s.2.val (log (cellQ N n c)) h
          else 0)) := by
      rw [mul_left_comm z]
      simp only [mul_sum]
    _ ≤ (shapeWords.card : ℝ) *
        ((Fintype.card (RootCode n) : ℝ) * (Fintype.card Split : ℝ) * e) :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (aggregateCard n : ℝ) * e := by
      simp only [aggregateCard, Nat.cast_mul]
      ring
    _ ≤ ((aggregateCard n : ℝ) + 1) * e :=
      mul_le_mul_of_nonneg_right (by linarith) he'.le
    _ = ε := by
      dsimp only [e]
      rw [mul_comm, div_mul_cancel₀ _ hden.ne']

/-- The payment is exactly the excess beyond the original complete-product
cut M <= N in the same marked profile sum. It does not compare the inner
smooth restrictions with ordinaryBad or the converted seed mass. -/
theorem absolute_selected_profile_excess_payment (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (dep : ℕ) (t : ℝ)
        (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          (selectedProfileMass N n dep t h B -
            selectedInnerMass N n dep t h B) ≤ ε := by
  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_selected_outer_payment n he
  refine ⟨h, hp, h8, hw, hw1, ?_⟩
  filter_upwards [H] with N hpaid
  intro dep t B
  have hs : selectedProfileMass N n dep t h B - selectedInnerMass N n dep t h B =
      selectedOuterMass N n dep t h B := by
    rw [selectedProfileMass_split]
    ring
  rw [hs]
  exact hpaid dep t B


/-- All original remaining-depth values, with each original dependent
position family retained. The root history has fuel 430, and
rootHistory_computed_data gives remaining + path.length = 430.
This is a finite payment budget, not a claim that every generation is
simultaneously an original counting source. -/
def allDepthSelectedOuterMass (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) : ℝ :=
  ∑ dep : Fin 431, selectedOuterMass N n dep.val t h (B dep)

def allDepthSelectedProfileMass (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) : ℝ :=
  ∑ dep : Fin 431, selectedProfileMass N n dep.val t h (B dep)

def allDepthSelectedInnerMass (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) : ℝ :=
  ∑ dep : Fin 431, selectedInnerMass N n dep.val t h (B dep)

/-- Exact radial decomposition after summing the fixed 431 original
remaining-depth slots; every depth keeps its own original B dep p. -/
theorem allDepthSelectedProfileMass_split (N n : ℕ) (t h : ℝ)
    (B : (dep : Fin 431) → (p : ℕ) →
      Finset (LevelIndex N n .U4 t p dep.val)) :
    allDepthSelectedProfileMass N n t h B =
      allDepthSelectedInnerMass N n t h B +
        allDepthSelectedOuterMass N n t h B := by
  simp only [allDepthSelectedProfileMass, allDepthSelectedInnerMass,
    allDepthSelectedOuterMass, selectedProfileMass_split, sum_add_distrib]

/-- One width pays the sum over every original depth. The extra factor
431 is fixed before N and before all selected position subfamilies. -/
theorem absolute_all_depth_selected_outer_payment
    (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (t : ℝ)
        (B : (dep : Fin 431) → (p : ℕ) →
          Finset (LevelIndex N n .U4 t p dep.val)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          allDepthSelectedOuterMass N n t h B ≤ ε := by
  have he' : 0 < ε / (431 : ℝ) := div_pos he (by norm_num)
  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_selected_outer_payment n he'
  refine ⟨h, hp, h8, hw, hw1, ?_⟩
  filter_upwards [H] with N hpaid
  intro t B
  unfold allDepthSelectedOuterMass
  rw [mul_sum]
  calc
    _ ≤ ∑ _dep : Fin 431, ε / (431 : ℝ) := by
      apply sum_le_sum
      intro dep hdep
      exact hpaid dep.val t (B dep)
    _ = ε := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The raw marked profile's complete M > N excess, summed over all
original remaining depths, has one absolute radial payment. The M <= N
inner profile still requires its separate nonradial comparison. -/
theorem absolute_all_depth_selected_profile_excess_payment
    (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 / 8 ∧
      0 < radialWidth h ∧ radialWidth h ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ (t : ℝ)
        (B : (dep : Fin 431) → (p : ℕ) →
          Finset (LevelIndex N n .U4 t p dep.val)),
        P2FiniteMarkedGamma5RadialRoughMass.norm N *
          (allDepthSelectedProfileMass N n t h B -
            allDepthSelectedInnerMass N n t h B) ≤ ε := by
  obtain ⟨h, hp, h8, hw, hw1, H⟩ := absolute_all_depth_selected_outer_payment n he
  refine ⟨h, hp, h8, hw, hw1, ?_⟩
  filter_upwards [H] with N hpaid
  intro t B
  have hs : allDepthSelectedProfileMass N n t h B -
      allDepthSelectedInnerMass N n t h B =
        allDepthSelectedOuterMass N n t h B := by
    rw [allDepthSelectedProfileMass_split]
    ring
  rw [hs]
  exact hpaid t B


end
end ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate
