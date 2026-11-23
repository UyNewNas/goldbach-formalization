import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Source-only, uncompiled. Concrete finite atom sums and retention maxima
for common-refinement error propagation. The hypotheses concern literal atom
weights and their local coefficient errors, never final H/h soundness.
For the adopted action bank the nonnegative atom masses and their <=12 bound
still require the original action-integral certificates. -/

namespace ImbalancedChen.P5RenewalFiniteError

noncomputable section

open Classical
open scoped BigOperators

/-- Both original 200-cell defect arrays live in this one state space. -/
abbrev OriginalState := Bool × Fin 200

variable {State Act Atom : Type*}

/-- One finite positive-transition action, with its actual atom weights. -/
def actionValue (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (X : State → ℝ) (a : Act) : ℝ :=
  base a + ∑ i ∈ atoms a, weight a i * X (child a i)

/-- Literal finite coefficient perturbation, evaluated on the same old
table. This has no action-result or final soundness field. -/
def localBudget (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (Y : State → ℝ) (a : Act) : ℝ :=
  |baseA a - baseB a| +
    ∑ i ∈ atoms a, |weightA a i - weightB a i| * |Y (child a i)|

theorem actionValue_sub_same (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (X Y : State → ℝ) (a : Act) :
    actionValue atoms child base weight X a - actionValue atoms child base weight Y a =
      ∑ i ∈ atoms a, weight a i * (X (child a i) - Y (child a i)) := by
  simp only [actionValue, mul_sub, Finset.sum_sub_distrib]
  ring

/-- A one-sided defect enclosure transports through a positive action. -/
theorem actionValue_oriented (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (X Y : State → ℝ)
    (a : Act) (E : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i ∈ atoms a, 0 ≤ weight a i) (hmass : (∑ i ∈ atoms a, weight a i) ≤ 12)
    (hXY : ∀ s, X s ≤ Y s + E) :
    actionValue atoms child base weight X a ≤ actionValue atoms child base weight Y a + 12 * E := by
  have hsum := Finset.sum_le_sum (s := atoms a) (fun i hi =>
    mul_le_mul_of_nonneg_left (hXY (child a i)) (hw i hi))
  have hmassE := mul_le_mul_of_nonneg_right hmass hE
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul] at hsum
  unfold actionValue
  linarith only [hsum, hmassE]

/-- Absolute sup error has the same coefficient mass, with no atom count
factor and no sign assumption on the old defect values. -/
theorem actionValue_lipschitz (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (X Y : State → ℝ)
    (a : Act) (E : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i ∈ atoms a, 0 ≤ weight a i) (hmass : (∑ i ∈ atoms a, weight a i) ≤ 12)
    (hXY : ∀ s, |X s - Y s| ≤ E) :
    |actionValue atoms child base weight X a - actionValue atoms child base weight Y a| ≤ 12 * E := by
  rw [actionValue_sub_same]
  calc
    _ ≤ ∑ i ∈ atoms a, |weight a i * (X (child a i) - Y (child a i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ atoms a, weight a i * |X (child a i) - Y (child a i)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ atoms a, weight a i * E :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hXY (child a i)) (hw i hi))
    _ = (∑ i ∈ atoms a, weight a i) * E := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hmass hE

theorem actionValue_coefficient_error
    (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (Y : State → ℝ) (a : Act) :
    |actionValue atoms child baseA weightA Y a - actionValue atoms child baseB weightB Y a| ≤
      localBudget atoms child baseA baseB weightA weightB Y a := by
  have heq : actionValue atoms child baseA weightA Y a - actionValue atoms child baseB weightB Y a =
      (baseA a - baseB a) + ∑ i ∈ atoms a, (weightA a i - weightB a i) * Y (child a i) := by
    simp only [actionValue, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |baseA a - baseB a| + |∑ i ∈ atoms a, (weightA a i - weightB a i) * Y (child a i)| :=
      abs_add_le _ _
    _ ≤ |baseA a - baseB a| + ∑ i ∈ atoms a, |(weightA a i - weightB a i) * Y (child a i)| :=
      add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _
    _ = _ := by simp only [localBudget, abs_mul]

/-- Local coefficient and inherited table errors add once per generation. -/
theorem actionValue_total_error
    (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (X Y : State → ℝ) (a : Act) (E delta : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i ∈ atoms a, 0 ≤ weightA a i) (hmass : (∑ i ∈ atoms a, weightA a i) ≤ 12)
    (hXY : ∀ s, |X s - Y s| ≤ E)
    (hlocal : localBudget atoms child baseA baseB weightA weightB Y a ≤ delta) :
    |actionValue atoms child baseA weightA X a - actionValue atoms child baseB weightB Y a| ≤
      12 * E + delta := by
  have htri :
      |actionValue atoms child baseA weightA X a - actionValue atoms child baseB weightB Y a| ≤
        |actionValue atoms child baseA weightA X a - actionValue atoms child baseA weightA Y a| +
        |actionValue atoms child baseA weightA Y a - actionValue atoms child baseB weightB Y a| := by
    have heq : actionValue atoms child baseA weightA X a - actionValue atoms child baseB weightB Y a =
        (actionValue atoms child baseA weightA X a - actionValue atoms child baseA weightA Y a) +
        (actionValue atoms child baseA weightA Y a - actionValue atoms child baseB weightB Y a) := by ring
    rw [heq]
    exact abs_add_le _ _
  exact htri.trans (add_le_add
    (actionValue_lipschitz atoms child baseA weightA X Y a E hE hw hmass hXY)
    ((actionValue_coefficient_error atoms child baseA baseB weightA weightB Y a).trans hlocal))

/-- Alternatives are retained by maximum, and all evaluations read the
same old table. No intermediate retention maximum is read by an action. -/
def maxActions (target : Act → State) (old : State → ℝ) (value : Act → ℝ) :
    List Act → State → ℝ
  | [] => old
  | a :: bank => fun s => if target a = s then max (maxActions target old value bank s) (value a)
      else maxActions target old value bank s

/-- A bank of any length preserves the same oriented uniform error. -/
theorem maxActions_oriented (target : Act → State) (oldA oldB : State → ℝ)
    (valueA valueB : Act → ℝ) (bank : List Act) (E : ℝ)
    (hold : ∀ s, oldA s ≤ oldB s + E)
    (hvalue : ∀ a ∈ bank, valueA a ≤ valueB a + E) :
    ∀ s, maxActions target oldA valueA bank s ≤ maxActions target oldB valueB bank s + E := by
  revert hvalue
  induction bank with
  | nil => intro _; exact hold
  | cons a bank ih =>
    intro hvalue s
    have htail := ih (fun b hb => hvalue b (List.mem_cons_of_mem _ hb)) s
    have ha := hvalue a (List.mem_cons_self _ _)
    simp only [maxActions]
    split_ifs
    · exact max_le
        (htail.trans (add_le_add_right (le_max_left _ _) _))
        (ha.trans (add_le_add_right (le_max_right _ _) _))
    · exact htail

theorem maxActions_lipschitz (target : Act → State) (oldA oldB : State → ℝ)
    (valueA valueB : Act → ℝ) (bank : List Act) (E : ℝ)
    (hold : ∀ s, |oldA s - oldB s| ≤ E)
    (hvalue : ∀ a ∈ bank, |valueA a - valueB a| ≤ E) :
    ∀ s, |maxActions target oldA valueA bank s - maxActions target oldB valueB bank s| ≤ E := by
  have hforward := maxActions_oriented target oldA oldB valueA valueB bank E
    (fun s => by have h := (abs_le.mp (hold s)).2; linarith only [h])
    (fun a ha => by have h := (abs_le.mp (hvalue a ha)).2; linarith only [h])
  have hbackward := maxActions_oriented target oldB oldA valueB valueA bank E
    (fun s => by have h := (abs_le.mp (hold s)).1; linarith only [h])
    (fun a ha => by have h := (abs_le.mp (hvalue a ha)).1; linarith only [h])
  intro s
  exact abs_le.mpr ⟨by linarith only [hbackward s], by linarith only [hforward s]⟩

theorem step_error (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (target : Act → State) (bank : List Act)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (X Y : State → ℝ) (E delta : ℝ) (hE : 0 ≤ E) (hdelta : 0 ≤ delta)
    (hw : ∀ a ∈ bank, ∀ i ∈ atoms a, 0 ≤ weightA a i)
    (hmass : ∀ a ∈ bank, (∑ i ∈ atoms a, weightA a i) ≤ 12)
    (hXY : ∀ s, |X s - Y s| ≤ E)
    (hlocal : ∀ a ∈ bank, localBudget atoms child baseA baseB weightA weightB Y a ≤ delta) :
    ∀ s, |maxActions target X (actionValue atoms child baseA weightA X) bank s -
      maxActions target Y (actionValue atoms child baseB weightB Y) bank s| ≤ 12 * E + delta := by
  apply maxActions_lipschitz
  · intro s
    exact (hXY s).trans (by nlinarith only [hE, hdelta])
  · intro a ha
    exact actionValue_total_error atoms child baseA baseB weightA weightB X Y a E delta
      hE (hw a ha) (hmass a ha) hXY (hlocal a ha)

/-- The exact finite geometric amplification; no large power is evaluated. -/
def amplification : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + 12 * amplification n

theorem amplification_nonneg (n : ℕ) : 0 ≤ amplification n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => simp only [amplification]; positivity

theorem amplification_succ_pos (n : ℕ) : 0 < amplification (n + 1) := by
  have h := amplification_nonneg n
  simp only [amplification]
  linarith only [h]

theorem amplification_eq_geometric (n : ℕ) : amplification n = ((12 : ℝ) ^ n - 1) / 11 := by
  induction n with
  | zero => norm_num [amplification]
  | succ n ih => rw [amplification, ih, pow_succ]; ring

/-- Different levels may use different finite atoms and alternatives, while
every action at a level still reads precisely that level's old table. -/
def iterate (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (base : ℕ → Act → ℝ) (weight : ℕ → Act → Atom → ℝ) (seed : State → ℝ) :
    ℕ → State → ℝ
  | 0 => seed
  | n + 1 => maxActions (target n) (iterate atoms child target bank base weight seed n)
      (actionValue (atoms n) (child n) (base n) (weight n)
        (iterate atoms child target bank base weight seed n)) (bank n)

/-- One local delta reserve propagates through n levels with exact geometric
loss. The seed is shared; any seed approximation must be counted as a local
level instead of being silently omitted. -/
theorem iterate_error (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (baseA baseB : ℕ → Act → ℝ) (weightA weightB : ℕ → Act → Atom → ℝ)
    (seed : State → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hw : ∀ n a, a ∈ bank n → ∀ i ∈ atoms n a, 0 ≤ weightA n a i)
    (hmass : ∀ n a, a ∈ bank n → (∑ i ∈ atoms n a, weightA n a i) ≤ 12)
    (hlocal : ∀ n a, a ∈ bank n → localBudget (atoms n) (child n) (baseA n) (baseB n)
      (weightA n) (weightB n) (iterate atoms child target bank baseB weightB seed n) a ≤ delta)
    (n : ℕ) : ∀ s,
      |iterate atoms child target bank baseA weightA seed n s -
        iterate atoms child target bank baseB weightB seed n s| ≤ delta * amplification n := by
  induction n with
  | zero => intro s; simp only [iterate, sub_self, abs_zero, amplification, mul_zero, le_refl]
  | succ n ih =>
    have hE : 0 ≤ delta * amplification n := mul_nonneg hdelta (amplification_nonneg n)
    have hs := step_error (atoms n) (child n) (target n) (bank n)
      (baseA n) (baseB n) (weightA n) (weightB n)
      (iterate atoms child target bank baseA weightA seed n)
      (iterate atoms child target bank baseB weightB seed n)
      (delta * amplification n) delta hE hdelta (hw n) (hmass n) ih (hlocal n)
    intro s
    simpa only [iterate, amplification, mul_add, mul_one, mul_assoc, add_comm,
      mul_left_comm, mul_comm] using hs s

theorem depth_430_plus_11 : (430 : ℕ) + 11 = 441 := by omega

/-- 430 simultaneous renewal rounds followed by eleven finite root/leaf
levels have precisely the manuscript's 441-level geometric error budget. -/
theorem iterate_430_rounds_11_depth
    (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (baseA baseB : ℕ → Act → ℝ) (weightA weightB : ℕ → Act → Atom → ℝ)
    (seed : State → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hw : ∀ n a, a ∈ bank n → ∀ i ∈ atoms n a, 0 ≤ weightA n a i)
    (hmass : ∀ n a, a ∈ bank n → (∑ i ∈ atoms n a, weightA n a i) ≤ 12)
    (hlocal : ∀ n a, a ∈ bank n → localBudget (atoms n) (child n) (baseA n) (baseB n)
      (weightA n) (weightB n) (iterate atoms child target bank baseB weightB seed n) a ≤ delta) :
    ∀ s,
      |iterate atoms child target bank baseA weightA seed (430 + 11) s -
        iterate atoms child target bank baseB weightB seed (430 + 11) s| ≤
          delta * (((12 : ℝ) ^ 441 - 1) / 11) := by
  have h := iterate_error atoms child target bank baseA baseB weightA weightB seed
    delta hdelta hw hmass hlocal (430 + 11)
  simpa only [depth_430_plus_11, amplification_eq_geometric] using h

/-- The actual signed eleven-term root, including its factor one fourth. -/
def rootValue (X : Fin 11 → ℝ) : ℝ :=
  (3 * X 0 + X 1 - X 2 - X 3 + X 4 + X 5 - 2 * X 6 - X 7 - X 8 - X 9 - X 10) / 4

def rootCoefficient : Fin 11 → ℝ :=
  ![3/4, 1/4, -1/4, -1/4, 1/4, 1/4, -1/2, -1/4, -1/4, -1/4, -1/4]

theorem rootValue_eq_sum (X : Fin 11 → ℝ) : rootValue X = ∑ i, rootCoefficient i * X i := by
  simp only [rootValue, rootCoefficient, Fin.sum_univ_succ]
  norm_num
  <;> ring

theorem rootCoefficient_norm : (∑ i : Fin 11, |rootCoefficient i|) = (7 / 2 : ℝ) := by
  norm_num [rootCoefficient, Fin.sum_univ_succ]

theorem rootValue_lipschitz (X Y : Fin 11 → ℝ) (E : ℝ) (_hE : 0 ≤ E)
    (hXY : ∀ i, |X i - Y i| ≤ E) : |rootValue X - rootValue Y| ≤ (7 / 2 : ℝ) * E := by
  rw [rootValue_eq_sum, rootValue_eq_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 11, |rootCoefficient i * X i - rootCoefficient i * Y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 11, |rootCoefficient i| * |X i - Y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← mul_sub, abs_mul]
    _ ≤ ∑ i : Fin 11, |rootCoefficient i| * E :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hXY i) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, rootCoefficient_norm]

/-- Upper costs and lower gains may be enclosed in their own directions.
Their signed root error is controlled by the same exact coefficient norm. -/
theorem rootValue_oriented (X Y : Fin 11 → ℝ) (E : ℝ)
    (hplus : ∀ i, 0 ≤ rootCoefficient i → X i ≤ Y i + E)
    (hminus : ∀ i, rootCoefficient i < 0 → Y i ≤ X i + E) :
    rootValue X ≤ rootValue Y + (7 / 2 : ℝ) * E := by
  have hterm : ∀ i : Fin 11, rootCoefficient i * (X i - Y i) ≤ |rootCoefficient i| * E := by
    intro i
    by_cases hc : 0 ≤ rootCoefficient i
    · have h := mul_le_mul_of_nonneg_left (hplus i hc) hc
      rw [abs_of_nonneg hc]
      nlinarith only [h]
    · have hc0 : rootCoefficient i < 0 := lt_of_not_ge hc
      have h := mul_le_mul_of_nonpos_left (hminus i hc0) hc0.le
      rw [abs_of_neg hc0]
      nlinarith only [h]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, rootCoefficient_norm] at hsum
  rw [rootValue_eq_sum, rootValue_eq_sum]
  linarith only [hsum]

/-- An explicit positive local reserve, selected below any earlier positive
precision cap, pays the full 441-level loss after the actual root norm. -/
theorem exists_local_reserve (reserve deltaMax : ℝ) (hreserve : 0 < reserve)
    (hdeltaMax : 0 < deltaMax) :
    ∃ delta : ℝ, 0 < delta ∧ delta < deltaMax ∧
      (7 / 2 : ℝ) * (delta * (((12 : ℝ) ^ 441 - 1) / 11)) < reserve := by
  have hA : 0 < amplification 441 := amplification_succ_pos 440
  let delta : ℝ := min (deltaMax / 2) (reserve / (7 * amplification 441))
  have hdelta : 0 < delta := lt_min (half_pos hdeltaMax) (div_pos hreserve (by positivity))
  have hdeltaMax' : delta < deltaMax :=
    (min_le_left _ _).trans_lt (half_lt_self hdeltaMax)
  have hbudget : delta * (7 * amplification 441) ≤ reserve :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  refine ⟨delta, hdelta, hdeltaMax', ?_⟩
  rw [← amplification_eq_geometric]
  nlinarith only [hbudget, hreserve]

/-- Final finite root reserve receiver. It asserts no table soundness: its
entry errors are supplied by iterate_error with 430+11 levels, once the
actual local positive atom/mass and coefficient budgets are established. -/
theorem root_reserve_of_entry_errors
    (X Y : Fin 11 → ℝ) (reserve delta : ℝ) (hdelta : 0 ≤ delta)
    (hentry : ∀ i, |X i - Y i| ≤ delta * amplification 441)
    (hreserve : (7 / 2 : ℝ) * (delta * (((12 : ℝ) ^ 441 - 1) / 11)) < reserve) :
    |rootValue X - rootValue Y| < reserve := by
  have h := rootValue_lipschitz X Y (delta * amplification 441)
    (mul_nonneg hdelta (amplification_nonneg 441)) hentry
  rw [amplification_eq_geometric] at h
  exact h.trans_lt hreserve

end

end ImbalancedChen.P5RenewalFiniteError
