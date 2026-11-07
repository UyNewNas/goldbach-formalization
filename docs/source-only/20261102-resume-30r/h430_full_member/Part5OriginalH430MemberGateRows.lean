import ImbalancedChen.Part5OriginalH430ActiveKnotPullbacks

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The COMPLETE literal LocalDomain has a finite list of strict/weak rows.
The list includes every W1/W2 parent gate, physical ceiling, new square,
strict bank endpoint and both Buchstab directions.  The row coefficients
are computed from the original action, its unchanged physical ceiling
and its unchanged native coordinates.  There is no supplied domain
equivalence or estimate field.  Clearing normalized bank denominators
uses the positive residual already required by LocalDomain itself.
-/

namespace ImbalancedChen.Part5OriginalH430MemberGateRows

noncomputable section
open Set Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition

structure GateRow where
  strict : Bool
  level : ℝ
  query : ℝ
  constant : ℝ

def weakRow (a b c : ℝ) : GateRow := ⟨false, a, b, c⟩
def strictRow (a b c : ℝ) : GateRow := ⟨true, a, b, c⟩

def GateRow.value (r : GateRow) (L s : ℝ) : ℝ :=
  r.level * L + r.query * s + r.constant

def GateRow.accepts (r : GateRow) (L s : ℝ) : Prop :=
  if r.strict then 0 < r.value L s else 0 ≤ r.value L s

def AllRows (rows : List GateRow) (L s : ℝ) : Prop :=
  ∀ r ∈ rows, r.accepts L s

@[simp] theorem weakUpper_accepts (c L s : ℝ) :
    (weakRow 0 (-1) c).accepts L s ↔ s ≤ c := by
  dsimp [GateRow.accepts, GateRow.value, weakRow]
  constructor <;> intro h <;> linarith

@[simp] theorem weakLower_accepts (c L s : ℝ) :
    (weakRow 0 1 (-c)).accepts L s ↔ c ≤ s := by
  dsimp [GateRow.accepts, GateRow.value, weakRow]
  constructor <;> intro h <;> linarith

@[simp] theorem strictUpper_accepts (c L s : ℝ) :
    (strictRow 0 (-1) c).accepts L s ↔ s < c := by
  dsimp [GateRow.accepts, GateRow.value, strictRow]
  constructor <;> intro h <;> linarith

@[simp] theorem strictLower_accepts (c L s : ℝ) :
    (strictRow 0 1 (-c)).accepts L s ↔ c < s := by
  dsimp [GateRow.accepts, GateRow.value, strictRow]
  constructor <;> intro h <;> linarith

@[simp] theorem allRows_nil (L s : ℝ) : AllRows [] L s := by
  simp [AllRows]

@[simp] theorem allRows_cons (r : GateRow) (rs : List GateRow) (L s : ℝ) :
    AllRows (r :: rs) L s ↔ r.accepts L s ∧ AllRows rs L s := by
  simp [AllRows]

@[simp] theorem allRows_append (rs ts : List GateRow) (L s : ℝ) :
    AllRows (rs ++ ts) L s ↔ AllRows rs L s ∧ AllRows ts L s := by
  simp [AllRows, forall_and]

def oneRows (C : ℝ) (z : Point) : List GateRow :=
  [strictRow 0 0 (z 0), weakRow 0 0 (C-z 0), weakRow 1 0 (-(2*z 0))]

def pairRows (C : ℝ) (z : Point) : List GateRow :=
  [strictRow 0 0 (z 0), strictRow 0 0 (z 1-z 0),
   weakRow 0 0 (C-z 1), weakRow 1 0 (-(2*z 1)),
   weakRow 1 0 (-(z 1+2*z 0))]

def intervalRows (c d : ℝ) (x : ℝ) : List GateRow :=
  [strictRow (-c) 0 x, strictRow d 0 (-x)]

def W2singleRows (p : W2Parameters) (j : Fin 3) (x : ℝ) : List GateRow :=
  intervalRows (a0 p) (![b p, a2 p, a3 p] j) x

def W2pairRows (p : W2Parameters) (j : Fin 4) (z : Point) : List GateRow :=
  ![[strictRow (-(a0 p)) 0 (z 0), strictRow 0 0 (z 1-z 0),
      strictRow (a2 p) 0 (-(z 1)), strictRow 1 0 (-(z 1+2*z 0))],
    [strictRow (-(a0 p)) 0 (z 0), strictRow (a1 p) 0 (-(z 0)),
      strictRow (-(a2 p)) 0 (z 1), strictRow (a3 p) 0 (-(z 1))],
    [strictRow (-(a0 p)) 0 (z 0), strictRow 0 0 (z 1-z 0),
      strictRow (a1 p) 0 (-(z 1))],
    [strictRow (-(a0 p)) 0 (z 0), strictRow (a1 p) 0 (-(z 0)),
      strictRow (-(a1 p)) 0 (z 1), strictRow (a2 p) 0 (-(z 1))]] j

/-- Cap rows keep their original positive bank constant.  No new physical
level is introduced to replace the residual in these rows. -/
def capRow (c C : ℝ) : GateRow := weakRow (-(1/c)) 0 C

/-- One finite catalogue for all original transition constructors. -/
def localRows (C : ℝ) (shape : StepShape) (z : Point) : List GateRow :=
  strictRow 1 0 0 ::
  match shape with
  | .retain => []
  | .transport i => [weakRow 0 (-1) (gridArgument i)]
  | .buchstabUpper => oneRows C z ++
      [weakRow 1 0 (-(3*z 0)), weakRow 1 (-(z 0)) 0,
       weakRow (-1) 0 (6*z 0)]
  | .buchstabLower => weakRow 0 1 (-2) :: (oneRows C z ++
      [weakRow 1 (-(z 0)) 0, weakRow (-1) 0 (6*z 0)])
  | .w1Fixed i j => [weakRow 0 (-1) (W1Target i), capRow (W1Anchor j) C]
  | .w1Singleton i j => oneRows C z ++
      intervalRows (1/W1Anchor j) (1/W1Target i) (z 0) ++
      [weakRow 0 (-1) (W1Target i), capRow (W1Target i) C]
  | .w2Fixed j anchor =>
      [weakRow 0 (-1) (originalW2At j).s,
       capRow (if anchor then (originalW2At j).s0 else (originalW2At j).phi1) C]
  | .w2Singleton j piece => oneRows C z ++
      W2singleRows (originalW2At j) piece (z 0) ++
      [weakRow 0 (-1) (originalW2At j).s, capRow (originalW2At j).s C]
  | .w2Pair j piece => pairRows C z ++ W2pairRows (originalW2At j) piece z ++
      [weakRow 0 (-1) (originalW2At j).s, capRow (originalW2At j).s C]

/-- A fixed-size per-edge catalogue, independent of the physical mesh. -/
theorem localRows_length_le_twelve (C : ℝ) (shape : StepShape) (z : Point) :
    (localRows C shape z).length ≤ 12 := by
  cases shape with
  | retain => norm_num [localRows]
  | transport i => norm_num [localRows]
  | buchstabUpper => norm_num [localRows, oneRows]
  | buchstabLower => norm_num [localRows, oneRows]
  | w1Fixed i j => norm_num [localRows]
  | w1Singleton i j => norm_num [localRows, oneRows, intervalRows]
  | w2Fixed j anchor => norm_num [localRows]
  | w2Singleton j piece => norm_num [localRows, oneRows, W2singleRows, intervalRows]
  | w2Pair j piece => fin_cases piece <;> norm_num [localRows, pairRows, W2pairRows]

theorem oneRows_iff (n : PhysicalNode) (z : Point) :
    AllRows (oneRows n.ceiling z) (residual n) n.argument ↔ OneGate n (z 0) := by
  simp [AllRows, oneRows, GateRow.accepts, GateRow.value, strictRow, weakRow,
    OneGate, ← sub_eq_add_neg, sub_nonneg]

theorem pairRows_iff (n : PhysicalNode) (z : Point) :
    AllRows (pairRows n.ceiling z) (residual n) n.argument ↔
      PairGate n (z 0) (z 1) := by
  simp [AllRows, pairRows, GateRow.accepts, GateRow.value, strictRow, weakRow,
    PairGate, ← sub_eq_add_neg, sub_nonneg, sub_pos]

theorem intervalRows_iff {L s c d x : ℝ} (hL : 0 < L) :
    AllRows (intervalRows c d x) L s ↔ x/L ∈ Ioo c d := by
  simp only [AllRows, intervalRows, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, GateRow.accepts, GateRow.value, strictRow, if_true,
    zero_mul, add_zero, mem_Ioo]
  rw [lt_div_iff₀ hL, div_lt_iff₀ hL]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem W2singleRows_iff {L s : ℝ} (hL : 0 < L)
    (p : W2Parameters) (j : Fin 3) (x : ℝ) :
    AllRows (W2singleRows p j x) L s ↔ x/L ∈ W2SingletonDomain p j := by
  fin_cases j <;>
    simpa [W2singleRows, W2SingletonDomain, W2Singleton2, W2Singleton3,
      W2Singleton4] using (intervalRows_iff (s := s) (x := x) hL)

private theorem pair_sum_iff {L x y : ℝ} (hL : 0 < L) :
    y/L+2*(x/L) < 1 ↔ y+2*x < L := by
  have he : y/L+2*(x/L) = (y+2*x)/L := by ring
  rw [he, div_lt_iff₀ hL, one_mul]

theorem W2pairRows_iff {n : PhysicalNode} (hL : 0 < residual n)
    (p : W2Parameters) (j : Fin 4) (z : Point) :
    AllRows (W2pairRows p j z) (residual n) n.argument ↔
      normalized n z ∈ W2PairDomain p j := by
  fin_cases j
  all_goals
    dsimp only [W2pairRows, W2PairDomain, W2Pair5, W2Pair6, W2Pair7, W2Pair8]
    simp only [allRows_cons, allRows_nil, and_true, GateRow.accepts, GateRow.value,
      strictRow, if_true, zero_mul, one_mul, zero_add, add_zero, normalized,
      Set.mem_setOf_eq, lt_div_iff₀ hL, div_lt_iff₀ hL,
      div_lt_div_iff_of_pos_right hL, pair_sum_iff hL]
  · constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> repeat' constructor <;> linarith
  · constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> repeat' constructor <;> linarith
  · constructor <;> rintro ⟨h1,h2,h3⟩ <;> repeat' constructor <;> linarith
  · constructor <;> rintro ⟨h1,h2,h3,h4⟩ <;> repeat' constructor <;> linarith

theorem capRow_iff (c C L s : ℝ) :
    (capRow c C).accepts L s ↔ L/c ≤ C := by
  have he : (capRow c C).value L s = C-L/c := by
    dsimp [GateRow.value, capRow, weakRow]
    ring
  change 0 ≤ (capRow c C).value L s ↔ _
  rw [he, sub_nonneg]

private theorem buchstabUpper_rows {L s x : ℝ} (hx : 0 < x) :
    (0 ≤ L-3*x ∧ 0 ≤ L-x*s ∧ 0 ≤ 6*x-L) ↔
      L/x-1 ∈ buchstabUpperDomain s := by
  change _ ↔ max 2 (s-1) ≤ L/x-1 ∧ L/x-1 ≤ 5
  rw [max_le_iff]
  constructor
  · rintro ⟨h1,h2,h3⟩
    have ha : (3 : ℝ) ≤ L/x := (le_div_iff₀ hx).mpr (by linarith)
    have hb : s ≤ L/x := (le_div_iff₀ hx).mpr (by nlinarith)
    have hc : L/x ≤ 6 := (div_le_iff₀ hx).mpr (by linarith)
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · rintro ⟨⟨h1,h2⟩,h3⟩
    have ha := (le_div_iff₀ hx).mp (show (3 : ℝ) ≤ L/x by linarith)
    have hb := (le_div_iff₀ hx).mp (show s ≤ L/x by linarith)
    have hc := (div_le_iff₀ hx).mp (show L/x ≤ 6 by linarith)
    exact ⟨by linarith, by nlinarith, by linarith⟩

private theorem buchstabLower_rows {L s x : ℝ} (hx : 0 < x) :
    (0 ≤ L-x*s ∧ 0 ≤ 6*x-L) ↔ L/x-1 ∈ buchstabLowerDomain s := by
  change _ ↔ s-1 ≤ L/x-1 ∧ L/x-1 ≤ 5
  constructor
  · rintro ⟨h1,h2⟩
    have ha : s ≤ L/x := (le_div_iff₀ hx).mpr (by nlinarith)
    have hb : L/x ≤ 6 := (div_le_iff₀ hx).mpr (by linarith)
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1,h2⟩
    have ha := (le_div_iff₀ hx).mp (show s ≤ L/x by linarith)
    have hb := (div_le_iff₀ hx).mp (show L/x ≤ 6 by linarith)
    exact ⟨by nlinarith, by linarith⟩

/-- Exact full local dictionary, including the lower s=2 closed stratum.
The target equivalence is proved from the original definitions. -/
theorem localDomain_iff_rows (n : PhysicalNode) (shape : StepShape) (z : Point) :
    LocalDomain n shape z ↔
      AllRows (localRows n.ceiling shape z) (residual n) n.argument := by
  by_cases hL : 0 < residual n
  · simp only [LocalDomain, hL, true_and, localRows, allRows_cons,
      GateRow.accepts, GateRow.value, strictRow, if_true, one_mul, zero_mul,
      add_zero, hL, true_and]
    cases shape with
    | retain => simp
    | transport i =>
        simp [AllRows, GateRow.accepts, GateRow.value, weakRow] <;> linarith
    | buchstabUpper =>
        rw [allRows_append, oneRows_iff]
        by_cases hg : OneGate n (z 0)
        · simp only [hg, true_and]
          simpa [AllRows, GateRow.accepts, GateRow.value, weakRow,
            buchstabArgument, ← sub_eq_add_neg, add_comm, mul_comm] using
              (buchstabUpper_rows hg.1).symm
        · simp [hg]
    | buchstabLower =>
        rw [allRows_cons, allRows_append, oneRows_iff]
        by_cases hg : OneGate n (z 0)
        · have he := (buchstabLower_rows (L := residual n) (s := n.argument) hg.1).symm
          simpa [AllRows, GateRow.accepts, GateRow.value, weakRow, hg,
            buchstabArgument, ← sub_eq_add_neg, sub_nonneg, add_comm, mul_comm] using
            and_congr_right (fun _ : 2 ≤ n.argument => he)
        · simp [AllRows, GateRow.accepts, GateRow.value, weakRow, hg]
    | w1Fixed i j =>
        simp [AllRows, capRow_iff, GateRow.accepts, GateRow.value, weakRow,
          ← sub_eq_add_neg, sub_nonneg]
    | w1Singleton i j =>
        rw [allRows_append, allRows_append, oneRows_iff, intervalRows_iff hL]
        simp [AllRows, capRow_iff, GateRow.accepts, GateRow.value, weakRow,
          normalized, W1Domain, ← sub_eq_add_neg, sub_nonneg, and_assoc]
    | w2Fixed j anchor =>
        simp [AllRows, capRow_iff, GateRow.accepts, GateRow.value, weakRow,
          ← sub_eq_add_neg, sub_nonneg]
    | w2Singleton j piece =>
        rw [allRows_append, allRows_append, oneRows_iff, W2singleRows_iff hL]
        simp [AllRows, capRow_iff, GateRow.accepts, GateRow.value, weakRow,
          normalized, ← sub_eq_add_neg, sub_nonneg, and_assoc]
    | w2Pair j piece =>
        rw [allRows_append, allRows_append, pairRows_iff, W2pairRows_iff hL]
        simp [AllRows, capRow_iff, GateRow.accepts, GateRow.value, weakRow,
          ← sub_eq_add_neg, sub_nonneg, and_assoc]
  · simp [LocalDomain, hL, localRows, AllRows, GateRow.accepts, GateRow.value, strictRow]

theorem row_difference (r : GateRow) (L M s t : ℝ) :
    r.value L s-r.value M t = r.level*(L-M)+r.query*(s-t) := by
  dsimp [GateRow.value]
  ring

theorem row_difference_bound (r : GateRow) (L M s t : ℝ) :
    |r.value L s-r.value M t| ≤ |r.level|*|L-M|+|r.query|*|s-t| := by
  rw [row_difference]
  simpa only [abs_mul] using abs_add_le (r.level*(L-M)) (r.query*(s-t))

/-- Changed strict AND changed weak rows are paid by CLOSED strips.
The nonzero-displacement clause excludes exact identity rows outright. -/
theorem changed_row_strip (r : GateRow) {L M s t : ℝ}
    (h : ¬ (r.accepts L s ↔ r.accepts M t)) :
    r.value L s ≠ r.value M t ∧
      |r.value L s| ≤ |r.level|*|L-M|+|r.query|*|s-t| := by
  have hne : r.value L s ≠ r.value M t := by
    intro he
    apply h
    simp only [GateRow.accepts, he]
  refine ⟨hne, ?_⟩
  have hstrip : |r.value L s| ≤ |r.value L s-r.value M t| := by
    have hb := abs_le.mp (le_refl |r.value L s-r.value M t|)
    cases hr : r.strict <;> simp only [GateRow.accepts, hr, if_true, if_false] at h
    all_goals
      by_cases ha : 0 ≤ r.value L s
      · rw [abs_of_nonneg ha]
        by_contra hn
        have hc : 0 < r.value L s := lt_of_le_of_lt (abs_nonneg _) (lt_of_not_ge hn)
        have hd : 0 < r.value M t := by linarith [hb.2]
        exact h ⟨fun _ => by positivity, fun _ => by positivity⟩
      · have ha' := lt_of_not_ge ha
        rw [abs_of_neg ha']
        by_contra hn
        have hd : r.value M t < 0 := by linarith [hb.1]
        exact h ⟨fun hh => by linarith, fun hh => by linarith⟩
  exact hstrip.trans (row_difference_bound r L M s t)

/-- Literal identity/inherit comparisons are transported, even at zero. -/
theorem exact_row_transport (r : GateRow) {L M s t : ℝ}
    (ha : r.level = 0) (hb : r.query = 0 ∨ s=t) :
    r.accepts L s ↔ r.accepts M t := by
  rcases hb with hb | hb <;> simp [GateRow.accepts, GateRow.value, ha, hb]

theorem changed_localDomain_strip {p q : PhysicalNode} (hC : p.ceiling=q.ceiling)
    (shape : StepShape) (z : Point)
    (hchange : ¬ (LocalDomain p shape z ↔ LocalDomain q shape z)) :
    ∃ r ∈ localRows p.ceiling shape z,
      r.value (residual p) p.argument ≠ r.value (residual q) q.argument ∧
      |r.value (residual p) p.argument| ≤
        |r.level|*|residual p-residual q|+|r.query|*|p.argument-q.argument| := by
  have hex : ∃ r ∈ localRows p.ceiling shape z,
      ¬ (r.accepts (residual p) p.argument ↔ r.accepts (residual q) q.argument) := by
    by_contra hn
    push_neg at hn
    apply hchange
    rw [localDomain_iff_rows, localDomain_iff_rows, ← hC]
    exact ⟨fun hp r hr => (hn r hr).mp (hp r hr),
      fun hq r hr => (hn r hr).mpr (hq r hr)⟩
  obtain ⟨r,hr,h⟩ := hex
  exact ⟨r,hr,changed_row_strip r h⟩

end
end ImbalancedChen.Part5OriginalH430MemberGateRows
