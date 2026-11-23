import ImbalancedChen.P2TableActionSoundness

/-!
SOURCE_ONLY / UNCOMPILED / OPEN30.

This module is staged next to P2TableActionSoundness.lean; its directory must
be a source root for the sibling import above. The table has exactly 400
integer numerators (two arrays of 200), at the original Q = 2^80 scale.

Only proved action constructors are admitted: the two ordinary Buchstab
actions, and upper positive-count transport to an earlier argument. No
arbitrary `licensed : eval <= H/h` field exists. A weight certificate states
only the nonnegativity and logarithmic enclosure of each scalar coefficient.
Each action's soundness is derived from the actual Wu source functions by
the previous module, before soundness of a bank or of any iteration is used.

All action evaluations read the SAME previous 400-entry table. Retention
maxima accumulated while processing the finite bank are never read by an
action. The soundness theorem holds for every finite round count, including
430, and does not assume a final table bound or a saved table array.

The zero seed is semantically proved. The adopted 2327/100000 seed on sixty
upper cells is NOT licensed here. Ordinary actions are homogeneous: from
zero they remain zero, as the explicit theorem below records. This is
therefore not a construction of the adopted positive 400 entries. There is
no W1/W2 constructor: the previous module's W1 feedback bound alone does
not establish its switched-cost/baseline license, and its Wu source family
has not been identified with the manuscript's enhanced stable-prefix family.
-/

namespace ImbalancedChen.P2SimultaneousTableSourceOnly

noncomputable section
open scoped BigOperators
open Wu2008DoubleSieve
open ImbalancedChen.P2TableActionSourceOnly

/-- Bool=true is the upper array; Bool=false is the lower array. -/
abbrev Table := Bool → Fin 200 → ℤ

theorem entry_count : Fintype.card (Bool × Fin 200) = 400 := by norm_num

def zeroTable : Table := fun _ _ => 0
def Nonnegative (X : Table) : Prop := ∀ upper i, 0 ≤ X upper i
def Below (X Y : Table) : Prop := ∀ upper i, X upper i ≤ Y upper i

/-- Semantic enclosures at the original cells' right endpoints. -/
def Sound (δ : ℝ) (X : Table) : Prop := ∀ upper i,
  (X upper i : ℝ) / tableQ ≤
    wuImprovementLimit upper δ (tableGrid (i.val+1))

/-- Total read adapter. Only in-range reads occur in actual action sums. -/
def read (X : Table) (upper : Bool) (j : ℕ) : ℤ :=
  if hj : j < 200 then X upper ⟨j, hj⟩ else 0

theorem read_mono {X Y : Table} (hXY : Below X Y) (upper : Bool) (j : ℕ) :
    read X upper j ≤ read Y upper j := by
  unfold read
  split_ifs with hj
  · exact hXY upper ⟨j,hj⟩
  · exact le_rfl

theorem read_nonnegative {X : Table} (hX : Nonnegative X) (upper : Bool) (j : ℕ) :
    0 ≤ read X upper j := by
  unfold read
  split_ifs with hj
  · exact hX upper ⟨j,hj⟩
  · exact le_rfl

theorem read_sound {δ : ℝ} {X : Table} (hX : Sound δ X)
    (upper : Bool) (j : ℕ) (hj : j < 200) :
    (read X upper j : ℝ) / tableQ ≤
      wuImprovementLimit upper δ (tableGrid (j+1)) := by
  simpa only [read, dif_pos hj] using hX upper ⟨j,hj⟩

/-- A local coefficient enclosure, not an action-result license. -/
structure LogWeights where
  numerator : ℕ → ℤ
  nonnegative : ∀ j < 200, 0 ≤ numerator j
  log_lower : ∀ j < 200, (numerator j : ℝ) / tableQ ≤
    Real.log (tableGrid (j+1) / tableGrid j)

/-- A fully supplied coefficient certificate, independent of any producer.
Nonzero saved logarithmic coefficients require their own scalar proofs. -/
def zeroLogWeights : LogWeights where
  numerator := fun _ => 0
  nonnegative := fun _ _ => le_rfl
  log_lower := by
    intro j hj
    simp only [Int.cast_zero, zero_div]
    apply Real.log_nonneg
    have hj0 : 0 < tableGrid j :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (tableGrid_bounds (by omega)).1
    apply (le_div_iff₀ hj0).2
    simpa only [one_mul] using tableGrid_mono (Nat.le_succ j)

/-- The finite bank cannot contain an action without a constructor whose
semantic proof appears below. In particular W1/W2 are not silently admitted. -/
inductive Action where
  | buchstabUpper (i : Fin 200) (hi : 50 ≤ i.val)
  | buchstabLower (i : Fin 200) (hi : 50 ≤ i.val)
  | upperTransport (i j : Fin 200) (hij : i.val ≤ j.val)

def Action.target : Action → Bool × Fin 200
  | .buchstabUpper i _ => (true, i)
  | .buchstabLower i _ => (false, i)
  | .upperTransport i _ _ => (true, i)

/-- Every eligible ordinary target is included once on each side. This
concrete bank has 300 proved actions, not the unlicensed 106 W1/W2 actions. -/
def fullOrdinaryBank : List Action :=
  List.ofFn (fun i : Fin 150 => Action.buchstabUpper
    ⟨i.val+50, by omega⟩ (by omega)) ++
  List.ofFn (fun i : Fin 150 => Action.buchstabLower
    ⟨i.val+50, by omega⟩ (by omega))

theorem fullOrdinaryBank_length : fullOrdinaryBank.length = 300 := by
  simp [fullOrdinaryBank]

/-- Original per-product Euclidean floors, with old-table reads only. -/
def suffixNumerator (W : LogWeights) (X : Table) (upper : Bool) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (200-k),
    read X upper (k+j) * W.numerator (k+j) / (tableQ : ℤ)

def evaluate (W : LogWeights) (old : Table) : Action → ℤ
  | .buchstabUpper i _ => suffixNumerator W old false (max 50 (i.val-49))
  | .buchstabLower i _ => suffixNumerator W old true (i.val-49)
  | .upperTransport _ j _ => old true j

theorem suffixNumerator_scaled (W : LogWeights) (X : Table) (upper : Bool) (k : ℕ) :
    (suffixNumerator W X upper k : ℝ) / tableQ =
      ∑ j ∈ Finset.range (200-k),
        roundedProduct tableQ (read X upper (k+j)) (W.numerator (k+j)) := by
  unfold suffixNumerator
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  exact (roundedProduct_eq_ediv _ _ _).symm

theorem suffixNumerator_mono (W : LogWeights) {X Y : Table}
    (hXY : Below X Y) (upper : Bool) {k : ℕ} (hk : k ≤ 200) :
    suffixNumerator W X upper k ≤ suffixNumerator W Y upper k := by
  unfold suffixNumerator
  apply Finset.sum_le_sum
  intro j hj
  have hjn := Finset.mem_range.mp hj
  exact Int.ediv_le_ediv (by exact_mod_cast tableQ_pos)
    (mul_le_mul_of_nonneg_right (read_mono hXY upper (k+j))
      (W.nonnegative (k+j) (by omega)))

theorem evaluate_mono (W : LogWeights) {X Y : Table} (hXY : Below X Y) (a : Action) :
    evaluate W X a ≤ evaluate W Y a := by
  cases a with
  | buchstabUpper i hi =>
      exact suffixNumerator_mono W hXY false (by omega)
  | buchstabLower i hi =>
      exact suffixNumerator_mono W hXY true (by omega)
  | upperTransport i j hij => exact hXY true j

private theorem target_parameter_bounds (i : Fin 200) (hi : 50 ≤ i.val) :
    2 ≤ tableGrid (i.val+1) ∧ tableGrid (i.val+1) ≤ 5 := by
  have hlo := tableGrid_mono (show 50 ≤ i.val+1 by omega)
  have hhi := (tableGrid_bounds (show i.val+1 ≤ 200 by omega)).2
  constructor
  · simpa [tableGrid] using hlo
  · exact hhi

/-- Action soundness is proved separately for every legal constructor.
Only old input-entry enclosures and local coefficient enclosures are used. -/
theorem evaluate_sound (W : LogWeights) {δ : ℝ} {old : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hn : Nonnegative old) (hsound : Sound δ old) (a : Action) :
    (evaluate W old a : ℝ) / tableQ ≤
      wuImprovementLimit a.target.1 δ (tableGrid (a.target.2.val+1)) := by
  cases a with
  | buchstabUpper i hi =>
      have hk : max 50 (i.val-49) ≤ 200 := by omega
      have ht := rounded_original_grid_tail_sound false
        (read old false) W.numerator hδ hδhi tableQ_pos hk
        (show (if false then 0 else 50 : ℕ) ≤ max 50 (i.val-49) by exact le_max_left _ _)
        (fun j hj => read_nonnegative hn false j) W.nonnegative
        (fun j hj => read_sound hsound false j hj) W.log_lower
      rw [← suffixNumerator_scaled, tableGrid_upper_start hi] at ht
      have hb := target_parameter_bounds i hi
      exact ht.trans (buchstab_upper_integral_sound hδ hδhi hb.1 hb.2)
  | buchstabLower i hi =>
      have ht := rounded_original_grid_tail_sound true
        (read old true) W.numerator hδ hδhi tableQ_pos (show i.val-49 ≤ 200 by omega)
        (show (if true then 0 else 50 : ℕ) ≤ i.val-49 by omega)
        (fun j hj => read_nonnegative hn true j) W.nonnegative
        (fun j hj => read_sound hsound true j hj) W.log_lower
      rw [← suffixNumerator_scaled, tableGrid_lower_start hi] at ht
      have hb := target_parameter_bounds i hi
      exact ht.trans (buchstab_lower_integral_sound hδ hδhi hb.1 hb.2)
  | upperTransport i j hij =>
      have hi := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
      have hj := tableGrid_bounds (show j.val+1 ≤ 200 by omega)
      exact (hsound true j).trans
        (wuImprovementLimit_upper_antitone hδ hδhi
          ⟨hi.1, hi.2.trans (by norm_num)⟩
          ⟨hj.1, hj.2.trans (by norm_num)⟩ (tableGrid_mono (by omega)))

/-- The old argument is fixed across the complete bank recursion. -/
def simultaneousStep (W : LogWeights) (old : Table) : List Action → Table
  | [] => old
  | a :: bank => fun upper i =>
      if a.target = (upper,i) then
        max (simultaneousStep W old bank upper i) (evaluate W old a)
      else simultaneousStep W old bank upper i

theorem simultaneousStep_retains (W : LogWeights) (old : Table) (bank : List Action) :
    Below old (simultaneousStep W old bank) := by
  induction bank with
  | nil => exact fun _ _ => le_rfl
  | cons a bank ih =>
      intro upper i
      simp only [simultaneousStep]
      split_ifs
      · exact (ih upper i).trans (le_max_left _ _)
      · exact ih upper i

theorem simultaneousStep_nonnegative (W : LogWeights) {old : Table}
    (hn : Nonnegative old) (bank : List Action) :
    Nonnegative (simultaneousStep W old bank) := by
  intro upper i
  exact (hn upper i).trans (simultaneousStep_retains W old bank upper i)

theorem simultaneousStep_mono (W : LogWeights) {X Y : Table}
    (hXY : Below X Y) (bank : List Action) :
    Below (simultaneousStep W X bank) (simultaneousStep W Y bank) := by
  induction bank with
  | nil => exact hXY
  | cons a bank ih =>
      intro upper i
      simp only [simultaneousStep]
      split_ifs
      · exact max_le_max (ih upper i) (evaluate_mono W hXY a)
      · exact ih upper i

theorem simultaneousStep_sound (W : LogWeights) {δ : ℝ} {old : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hn : Nonnegative old) (hsound : Sound δ old) (bank : List Action) :
    Sound δ (simultaneousStep W old bank) := by
  induction bank with
  | nil => exact hsound
  | cons a bank ih =>
      intro upper i
      simp only [simultaneousStep]
      split_ifs with heq
      · have ha := evaluate_sound W hδ hδhi hn hsound a
        rw [heq] at ha
        rcases le_total (simultaneousStep W old bank upper i) (evaluate W old a) with hab | hba
        · rw [max_eq_right hab]
          exact ha
        · rw [max_eq_left hba]
          exact ih upper i
      · exact ih upper i

def iterateFrom (W : LogWeights) (bank : List Action) (seed : Table) : ℕ → Table
  | 0 => seed
  | rounds+1 => simultaneousStep W (iterateFrom W bank seed rounds) bank

theorem iterateFrom_nonnegative (W : LogWeights) (bank : List Action) {seed : Table}
    (hn : Nonnegative seed) (rounds : ℕ) :
    Nonnegative (iterateFrom W bank seed rounds) := by
  induction rounds with
  | zero => exact hn
  | succ n ih => exact simultaneousStep_nonnegative W ih bank

theorem iterateFrom_sound (W : LogWeights) (bank : List Action) {δ : ℝ} {seed : Table}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10)
    (hn : Nonnegative seed) (hsound : Sound δ seed) (rounds : ℕ) :
    Sound δ (iterateFrom W bank seed rounds) := by
  induction rounds with
  | zero => exact hsound
  | succ n ih =>
      exact simultaneousStep_sound W hδ hδhi (iterateFrom_nonnegative W bank hn n) ih bank

theorem iterateFrom_le_succ (W : LogWeights) (bank : List Action)
    (seed : Table) (rounds : ℕ) :
    Below (iterateFrom W bank seed rounds) (iterateFrom W bank seed (rounds+1)) := by
  exact simultaneousStep_retains W _ bank

theorem iterateFrom_mono (W : LogWeights) (bank : List Action) (seed : Table) :
    ∀ m n, m ≤ n → Below (iterateFrom W bank seed m) (iterateFrom W bank seed n) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact fun _ _ => le_rfl
  | succ n hmn ih =>
      intro upper i
      exact (ih upper i).trans (iterateFrom_le_succ W bank seed n upper i)

theorem zeroTable_nonnegative : Nonnegative zeroTable := by
  intro upper i
  exact le_rfl

theorem zeroTable_sound {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    Sound δ zeroTable := by
  intro upper i
  have hb := tableGrid_bounds (show i.val+1 ≤ 200 by omega)
  simpa only [zeroTable, Int.cast_zero, zero_div] using
    wuImprovementLimit_nonneg upper hδ (by linarith : δ < 1 / 2)
      hb.1 (hb.2.trans (by norm_num))

/-- Every finite generation is sound, with a proved seed and no terminal
table-bound assumption. This specializes directly to 430 generations. -/
theorem zero_seed_iteration_sound (W : LogWeights) (bank : List Action) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (rounds : ℕ) :
    Sound δ (iterateFrom W bank zeroTable rounds) := by
  exact iterateFrom_sound W bank hδ hδhi zeroTable_nonnegative
    (zeroTable_sound hδ hδhi) rounds

theorem zero_seed_430_sound (W : LogWeights) (bank : List Action) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    Sound δ (iterateFrom W bank zeroTable 430) := by
  exact zero_seed_iteration_sound W bank hδ hδhi 430

/-- A fully specified, genuinely licensed finite-bank instantiation. -/
theorem concrete_ordinary_zero_seed_430_sound {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    Sound δ (iterateFrom zeroLogWeights fullOrdinaryBank zeroTable 430) := by
  exact zero_seed_430_sound zeroLogWeights fullOrdinaryBank hδ hδhi

theorem evaluate_zero (W : LogWeights) (a : Action) : evaluate W zeroTable a = 0 := by
  cases a <;> simp [evaluate, suffixNumerator, read, zeroTable]

theorem simultaneousStep_zero (W : LogWeights) (bank : List Action) :
    simultaneousStep W zeroTable bank = zeroTable := by
  induction bank with
  | nil => rfl
  | cons a bank ih =>
      funext upper i
      simp [simultaneousStep, ih, evaluate_zero, zeroTable]

/-- The missing positive seed/action license cannot be hidden by iterating
ordinary homogeneous actions: every zero-seed entry is exactly zero. -/
theorem zero_seed_iteration_eq_zero (W : LogWeights) (bank : List Action) (rounds : ℕ) :
    iterateFrom W bank zeroTable rounds = zeroTable := by
  induction rounds with
  | zero => rfl
  | succ n ih =>
      simp only [iterateFrom, ih, simultaneousStep_zero]

end
end ImbalancedChen.P2SimultaneousTableSourceOnly
