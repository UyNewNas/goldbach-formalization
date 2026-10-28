import ImbalancedChen.P2OriginalSelectedMaskPhysicalSquares
import ImbalancedChen.P2LowerCapPlanIntegerRetention

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected SourceForm supplies one literal mask and one buffered cap.
This file evaluates BOTH of its list square tests on the same integer
prime vector. The selected product is multiplied into every complement
prefix square; an unrelated all-false Trace mask is never substituted.

The manuscript's per-prime tests do not assert (b*s)*r^2 <= Q for the
whole rough product r. We therefore retain the actual prefix squares.
The last prime > 1 makes the full prefix product strictly smaller than
Q, even though SquareGates stores its inequalities in closed form.
-/

namespace ImbalancedChen.P2OriginalSelectedIntegerPrefixSquares

noncomputable section
open scoped Classical
open P2EnhancedLowerPhysicalNode P2LowerCapPlanIntegerRetention
open P2OriginalSelectedMaskPhysicalSquares
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerCompactTraceBinding
open P2OriginalLowerWholeBoxBranchSelect

/-- Literal integer prefix products, at one unchanged total level. -/
def IntegerSquareGates (N : ℕ) (cap : ℝ) : ℕ → List ℕ → Prop
  | _, [] => True
  | B, p :: ps => (B : ℝ) * (p : ℝ)^2 ≤ (N : ℝ)^cap ∧
      IntegerSquareGates N cap (B*p) ps

/-- Indexed form used by the coefficient support compiler. For the
    complement word, B is the product of all original selected slots. -/
theorem integerSquareGates_at {N B : ℕ} {cap : ℝ}
    (ps : List ℕ) (hgates : IntegerSquareGates N cap B ps)
    (i : ℕ) (hi : i < ps.length) :
    ((B * (ps.take i).prod : ℕ) : ℝ) * (ps[i] : ℝ)^2 ≤ (N : ℝ)^cap := by
  induction ps generalizing B i with
  | nil => simp at hi
  | cons p ps ih =>
      change (B : ℝ) * (p : ℝ)^2 ≤ (N : ℝ)^cap ∧
        IntegerSquareGates N cap (B*p) ps at hgates
      cases i with
      | zero => simpa using hgates.1
      | succ i =>
          have hitail : i < ps.length := by simpa using hi
          simpa [Nat.mul_assoc] using ih hgates.2 i hitail

/-- Reuse the existing integer-history dictionary, without reversing
    the caller's physical chronological list. -/
theorem coordinate_list_power {N : ℕ} (hN : 1 < (N : ℝ))
    (ps : List ℕ) (hpos : ∀ p ∈ ps, 0 < p) :
    (N : ℝ)^((ps.map (coordinate N)).sum) = (ps.prod : ℝ) := by
  simpa [physicalWord] using physicalWord_power hN ps.reverse
    (fun p hp => hpos p (List.mem_reverse.mp hp))

/-- Exact logarithmic-to-integer conversion with an already selected
    product B. The initial exponent T is evaluated, not postulated to
    be zero. This is essential for the selected-complement test. -/
theorem squareGates_to_integer {N : ℕ} (hN : 1 < (N : ℝ))
    (ps : List ℕ) (hpos : ∀ p ∈ ps, 0 < p)
    {cap T : ℝ} {B : ℕ} (hbase : (N : ℝ)^T = (B : ℝ))
    (hgates : SquareGates cap T (ps.map (coordinate N))) :
    IntegerSquareGates N cap B ps := by
  induction ps generalizing T B with
  | nil => trivial
  | cons p ps ih =>
      have hp : 0 < p := hpos p (List.mem_cons_self p ps)
      have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hN
      change T + 2 * coordinate N p ≤ cap ∧
        SquareGates cap (T + coordinate N p) (ps.map (coordinate N)) at hgates
      have hsq : (N : ℝ)^(2 * coordinate N p) = (p : ℝ)^2 := by
        rw [mul_comm (2 : ℝ) (coordinate N p),
          Real.rpow_mul hNpos.le, coordinate_power hN hp]
        norm_num
      have heval : (N : ℝ)^(T + 2 * coordinate N p) =
          (B : ℝ) * (p : ℝ)^2 := by
        rw [Real.rpow_add hNpos, hbase, hsq]
      have hnext : (N : ℝ)^(T + coordinate N p) = ((B*p : ℕ) : ℝ) := by
        rw [Real.rpow_add hNpos, hbase, coordinate_power hN hp, Nat.cast_mul]
      constructor
      · rw [← heval]
        exact Real.rpow_le_rpow_of_exponent_le hN.le hgates.1
      · exact ih (fun q hq => hpos q (List.mem_cons_of_mem p hq)) hnext hgates.2

/-- A nonempty prime word has product strictly below its final square
    bound. No square of the WHOLE word is used. -/
theorem integerSquareGates_product_lt {N B : ℕ} {cap : ℝ}
    (ps : List ℕ) (hB : 0 < B) (hprime : ∀ p ∈ ps, 1 < p)
    (hne : ps ≠ []) (hgates : IntegerSquareGates N cap B ps) :
    ((B * ps.prod : ℕ) : ℝ) < (N : ℝ)^cap := by
  induction ps generalizing B with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
      have hp : 1 < p := hprime p (List.mem_cons_self p ps)
      change (B : ℝ) * (p : ℝ)^2 ≤ (N : ℝ)^cap ∧
        IntegerSquareGates N cap (B*p) ps at hgates
      by_cases htail : ps = []
      · subst ps
        have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
        have hBpos : 0 < (B : ℝ) := Nat.cast_pos.mpr hB
        have hsq : (p : ℝ) < (p : ℝ)^2 := by nlinarith
        have h := (mul_lt_mul_of_pos_left hsq hBpos).trans_le hgates.1
        simpa only [List.prod_cons, List.prod_nil, Nat.mul_one, Nat.cast_mul] using h
      · have h := ih (Nat.mul_pos hB (lt_trans Nat.zero_lt_one hp))
          (fun q hq => hprime q (List.mem_cons_of_mem p hq)) htail hgates.2
        simpa only [List.prod_cons, Nat.mul_assoc] using h

def logSlots (N : ℕ) (slots : List (ℕ × Bool)) : List Slot :=
  slots.map (fun a => ⟨coordinate N a.1, a.2⟩)

def selectedPrimes (slots : List (ℕ × Bool)) : List ℕ :=
  (slots.filter (fun a => a.2)).map Prod.fst

def remainingPrimes (slots : List (ℕ × Bool)) : List ℕ :=
  (slots.filter (fun a => !a.2)).map Prod.fst

/-- Literal mask factorization, including repeated integer values.
    No squarefreeness, coprimality, or replacement mask is needed. -/
theorem selected_mul_remaining (slots : List (ℕ × Bool)) :
    (selectedPrimes slots).prod * (remainingPrimes slots).prod =
      (slots.map Prod.fst).prod := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
      cases a with
      | mk p selected =>
          cases selected <;>
            simpa [selectedPrimes, remainingPrimes, Nat.mul_assoc,
              Nat.mul_comm, Nat.mul_left_comm] using
              congrArg (fun z : ℕ => p * z) ih

@[simp] theorem selectedWord_logSlots (N : ℕ) (slots : List (ℕ × Bool)) :
    selectedWord (logSlots N slots) = (selectedPrimes slots).map (coordinate N) := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
      cases a with
      | mk p selected =>
          cases selected <;>
            simp [logSlots, selectedWord, selectedPrimes] at ih ⊢ <;> exact ih

@[simp] theorem remainingWord_logSlots (N : ℕ) (slots : List (ℕ × Bool)) :
    remainingWord (logSlots N slots) = (remainingPrimes slots).map (coordinate N) := by
  induction slots with
  | nil => rfl
  | cons a slots ih =>
      cases a with
      | mk p selected =>
          cases selected <;>
            simp [logSlots, remainingWord, remainingPrimes] at ih ⊢ <;> exact ih

/-- Both integer gate lists are derived from the SAME physical slots.
    The selected product occurs explicitly as the initial prefix B. -/
theorem physical_slots_to_integer {N : ℕ} (hN : 1 < (N : ℝ))
    (slots : List (ℕ × Bool)) (hpos : ∀ a ∈ slots, 0 < a.1)
    (cap : ℝ)
    (hfull : SquareGates cap 0 ((logSlots N slots).map Slot.exponent))
    (hselected : SquareGates cap (selectedWord (logSlots N slots)).sum
      (remainingWord (logSlots N slots))) :
    IntegerSquareGates N cap 1 (slots.map Prod.fst) ∧
      IntegerSquareGates N cap (selectedPrimes slots).prod (remainingPrimes slots) := by
  have hall : ∀ p ∈ slots.map Prod.fst, 0 < p := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hpos a ha
  have hsel : ∀ p ∈ selectedPrimes slots, 0 < p := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hpos a (List.mem_filter.mp ha).1
  have hrem : ∀ p ∈ remainingPrimes slots, 0 < p := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact hpos a (List.mem_filter.mp ha).1
  constructor
  · apply squareGates_to_integer hN (slots.map Prod.fst) hall
      (T := 0) (B := 1) (by simp)
    simpa [logSlots, List.map_map, Function.comp_def] using hfull
  · rw [selectedWord_logSlots, remainingWord_logSlots] at hselected
    exact squareGates_to_integer hN (remainingPrimes slots) hrem
      (coordinate_list_power hN (selectedPrimes slots) hsel) hselected

def integerPointSlot {mesh : ℕ} (code : Code mesh)
    (mask : Finset (Fin 5)) (p : Fin 5 → ℕ) (i : Fin 5) : ℕ × Bool :=
  (p i, (code i).2 || decide (i ∈ mask))

def integerPrefixSlots {mesh : ℕ} (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (p : Fin 5 → ℕ) : List (ℕ × Bool) :=
  match rank.val with
  | 3 => [integerPointSlot code mask p 0, integerPointSlot code mask p 1,
      integerPointSlot code mask p 2]
  | 4 => [integerPointSlot code mask p 0, integerPointSlot code mask p 1,
      integerPointSlot code mask p 2, integerPointSlot code mask p 3]
  | 5 => [integerPointSlot code mask p 0, integerPointSlot code mask p 1,
      integerPointSlot code mask p 2, integerPointSlot code mask p 3,
      integerPointSlot code mask p 4]
  | _ => []

theorem log_integerPrefixSlots (N : ℕ) (S : CompactStart)
    {mesh : ℕ} (rank : Fin 6) (code : Code mesh)
    (mask : Finset (Fin 5)) (p : Fin 5 → ℕ) :
    logSlots N (integerPrefixSlots rank code mask p) =
      pointPrefixSlots S rank code mask (fun i => coordinate N (p i)) := by
  fin_cases rank <;> rfl

/-- Actual branch selection, at the actual exponent code, now proves
    the literal full AND selected-complement integer squares. This
    eliminates the per-prime vector-to-integer gate obligation.

    No all-false Trace marks, ideal parent cap, or whole-rho square is
    introduced. The named branch b and its buffered cap occur in every
    part of the conclusion. -/
theorem selected_source_integer_squares (S : CompactStart)
    {N mesh : ℕ} (hN : 1 < (N : ℝ)) (bank : CandidateBank mesh)
    (buffer : ℚ) (rank : Fin 6)
    (hrank : rank.val = 3 ∨ rank.val = 4 ∨ rank.val = 5)
    (p : Fin 5 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hx : ∀ i, coordinate N (p i) ∈ Set.Icc (S.epsilon : ℝ)
      (startCutoff S.start : ℝ))
    (data : P2OriginalLowerBufferedAffineBoxes.BranchData)
    (hsel : select S bank buffer rank
      (prefixCode rank.val (actualCode S mesh (fun i => coordinate N (p i)))) = some data) :
    ∃ b ∈ bank.alternatives rank
        (prefixCode rank.val (actualCode S mesh (fun i => coordinate N (p i)))),
      supportCheck S rank
        (prefixCode rank.val (actualCode S mesh (fun i => coordinate N (p i)))) buffer b ∧
      data = b.asBranchData ∧
      let code := prefixCode rank.val (actualCode S mesh (fun i => coordinate N (p i)))
      let slots := integerPrefixSlots rank code b.form.supportMask p
      let cap := (bufferedCap S code buffer b : ℝ)
      IntegerSquareGates N cap 1 (slots.map Prod.fst) ∧
        IntegerSquareGates N cap (selectedPrimes slots).prod (remainingPrimes slots) ∧
        ((slots.map Prod.fst).prod : ℝ) < (N : ℝ)^cap := by
  obtain ⟨b, hb, hcheck, hdata, hsquares⟩ :=
    selected_source_actual_square_gates S bank buffer rank
      (fun i => coordinate N (p i)) hx data hsel
  refine ⟨b, hb, hcheck, hdata, ?_⟩
  let code := prefixCode rank.val (actualCode S mesh (fun i => coordinate N (p i)))
  let slots := integerPrefixSlots rank code b.form.supportMask p
  let cap := (bufferedCap S code buffer b : ℝ)
  have hvalues : ∀ i, 1 < p i := fun i => (hp i).one_lt
  have hslotgt : ∀ a ∈ slots, 1 < a.1 := by
    dsimp [slots]
    fin_cases rank <;> simp [integerPrefixSlots, integerPointSlot, hvalues]
  have hslotpos : ∀ a ∈ slots, 0 < a.1 :=
    fun a ha => lt_trans Nat.zero_lt_one (hslotgt a ha)
  have hslots : logSlots N slots = pointPrefixSlots S rank code
      b.form.supportMask (fun i => coordinate N (p i)) :=
    log_integerPrefixSlots N S rank code b.form.supportMask p
  have hfull : SquareGates cap 0 ((logSlots N slots).map Slot.exponent) := by
    rw [hslots]
    exact hsquares.1
  have hselected : SquareGates cap (selectedWord (logSlots N slots)).sum
      (remainingWord (logSlots N slots)) := by
    rw [hslots]
    exact hsquares.2
  have hboth := physical_slots_to_integer hN slots hslotpos cap hfull hselected
  have hne : slots.map Prod.fst ≠ [] := by
    rcases hrank with h3 | h4 | h5
    · simp [slots, integerPrefixSlots, h3]
    · simp [slots, integerPrefixSlots, h4]
    · simp [slots, integerPrefixSlots, h5]
  have hprimeword : ∀ q ∈ slots.map Prod.fst, 1 < q := by
    intro q hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact hslotgt a ha
  have hprod := integerSquareGates_product_lt (slots.map Prod.fst)
    (by decide : 0 < (1 : ℕ)) hprimeword hne hboth.1
  exact ⟨hboth.1, hboth.2, by simpa only [Nat.one_mul] using hprod⟩

end
end ImbalancedChen.P2OriginalSelectedIntegerPrefixSquares
