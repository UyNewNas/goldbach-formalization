import ImbalancedChen.P4AOriginalFourthFifthAffinePrograms

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

All point-dependent original sixth guards are expanded into affine
comparisons. Saved rows, all eleven source actions and all nineteen later
actions remain in their original order. Later eligibility compares the
EXACT program for the current raw predecessor, not a rounded cap.
The code never asserts that an archived row passes its geometric checks.
-/
namespace ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P4AOriginalFourthFifthAffinePrograms
open P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology

abbrev SixPoint := Certificates.P2OriginalSixthElevenLogSemantics.Physical
abbrev ElevenCell := Certificates.P2OriginalSixthElevenLogSemantics.Cell
abbrev LaterCell := P4AOriginalSixthLaterLiteral.Cell

def selectedA (mask : ℕ) : Affine 6 :=
  Affine.sum Finset.univ (fun i => if Certificates.P2OriginalSixthElevenLogSemantics.bit mask i.val then X i else K 0)
def subsetA (mask : ℕ) : Affine 6 :=
  Affine.sum Finset.univ (fun i : Fin 5 => if Certificates.P2OriginalSixthElevenLogSemantics.bit mask i.val then X i.castSucc else K 0)
def fullA (j : Fin 6) : Affine 6 :=
  (Affine.sum Finset.univ (fun i : Fin 6 => if i < j then X i else K 0)).add ((X j).scale 2)
def remainingA (mask : ℕ) (j : Fin 6) : Affine 6 :=
  ((selectedA mask).add
    (Affine.sum Finset.univ (fun i : Fin 6 =>
      if i < j ∧ Certificates.P2OriginalSixthElevenLogSemantics.bit mask i.val = false then X i else K 0))).add ((X j).scale 2)
def sum5A : Affine 6 := Affine.sum Finset.univ (fun i : Fin 5 => X i.castSucc)
def sum6A : Affine 6 := sum5A.add (X 5)
def h3A : Affine 6 := ((X 0).add (X 1)).add ((X 2).scale 3)
def h5A : Affine 6 :=
  ((((X 0).add (X 1)).add (X 2)).add (X 3)).add ((X 4).scale 3)
def r0A : Affine 6 := ascending (X 0)
def wA : Affine 6 := (K (153 / 256)).sub ((X 2).scale (3 / 8))
def clippedA : Affine 6 := (sum5A.add ((X 5).scale 4)).sub (K Certificates.P2OriginalSixthElevenLogSemantics.eta)
def asc33A : Affine 6 := ascending ((X 0).add (X 5))
def desc33A : Affine 6 := descending ((X 0).add (X 5))
def asc34A : Affine 6 := ascending ((X 1).add (X 5))

@[simp] theorem eval_selectedA (m : ℕ) (t : SixPoint) :
    (selectedA m).eval t = Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m t := by
  simp [selectedA, Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, apply_ite]
@[simp] theorem eval_subsetA (m : ℕ) (t : SixPoint) :
    (subsetA m).eval t = Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t := by
  simp [subsetA, Certificates.P2OriginalSixthElevenLogSemantics.subsetSum, apply_ite]
@[simp] theorem eval_fullA (j : Fin 6) (t : SixPoint) :
    (fullA j).eval t = Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t := by
  simp [fullA, Certificates.P2OriginalSixthElevenLogSemantics.fullSquare, apply_ite]
@[simp] theorem eval_remainingA (m : ℕ) (j : Fin 6) (t : SixPoint) :
    (remainingA m j).eval t = Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare m j t := by
  simp [remainingA, Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare, apply_ite]
@[simp] theorem eval_sum5A (t : SixPoint) : sum5A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.S5 t := by
  simp [sum5A, Certificates.P2OriginalSixthElevenLogSemantics.S5, Fin.sum_univ_succ]
@[simp] theorem eval_sum6A (t : SixPoint) : sum6A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.S6 t := by
  simp [sum6A, Certificates.P2OriginalSixthElevenLogSemantics.S6]
@[simp] theorem eval_h3A (t : SixPoint) : h3A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.H3 t := by simp [h3A, Certificates.P2OriginalSixthElevenLogSemantics.H3]
@[simp] theorem eval_h5A (t : SixPoint) : h5A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.H5 t := by simp [h5A, Certificates.P2OriginalSixthElevenLogSemantics.H5]
@[simp] theorem eval_r0A (t : SixPoint) : r0A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.R0 t := by
  simp [r0A, Certificates.P2OriginalSixthElevenLogSemantics.R0, VariableEnvelope.A]
@[simp] theorem eval_wA (t : SixPoint) : wA.eval t = Certificates.P2OriginalSixthElevenLogSemantics.W t := by
  simp [wA, Certificates.P2OriginalSixthElevenLogSemantics.W]; ring
@[simp] theorem eval_clippedA (t : SixPoint) : clippedA.eval t = Certificates.P2OriginalSixthElevenLogSemantics.clippedCap t := by
  simp [clippedA, Certificates.P2OriginalSixthElevenLogSemantics.clippedCap]
@[simp] theorem eval_asc33A (t : SixPoint) : asc33A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.ascending33 t := by
  simp [asc33A, Certificates.P2OriginalSixthElevenLogSemantics.ascending33, VariableEnvelope.A]; ring
@[simp] theorem eval_desc33A (t : SixPoint) : desc33A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.descending33 t := by
  simp [desc33A, Certificates.P2OriginalSixthElevenLogSemantics.descending33, VariableEnvelope.C]; ring
@[simp] theorem eval_asc34A (t : SixPoint) : asc34A.eval t = Certificates.P2OriginalSixthElevenLogSemantics.ascending34 t := by
  simp [asc34A, Certificates.P2OriginalSixthElevenLogSemantics.ascending34, VariableEnvelope.A]; ring

/-- The midpoint is used ONLY to choose the same original stored plane.
The selected plane is subsequently evaluated at the variable point. -/
def savedOldPlaneA (i : P4AOriginalSavedSixthArchive.Row) (mask : ℕ) : Affine 6 :=
  let s := Certificates.P2OriginalSixthElevenLogSemantics.subsetSum mask (P4AOriginalSavedSixthArchive.midpoint i)
  if VariableEnvelope.A s ≤ VariableEnvelope.C s ∧
      VariableEnvelope.A s ≤ VariableEnvelope.cap then ascending (subsetA mask)
  else if VariableEnvelope.C s ≤ VariableEnvelope.cap then descending (subsetA mask)
  else K VariableEnvelope.cap

def savedOldUpper (i : P4AOriginalSavedSixthArchive.Row) : Program 6 :=
  maxRows (fun _ : ℕ => []) (fun m => atom (savedOldPlaneA i m)) (atom wA)
    (Finset.Icc 1 31).toList

def savedEndpoint (i : P4AOriginalSavedSixthArchive.Row) : Program 6 :=
  .inf (atom (ascending (selectedA (P4AOriginalSavedSixthArchive.selectedMask i))))
    (atom (descending (selectedA (P4AOriginalSavedSixthArchive.selectedMask i))))

@[simp] theorem savedOldPlaneA_exact (i : P4AOriginalSavedSixthArchive.Row) (mask : ℕ) (t : SixPoint) :
    (savedOldPlaneA i mask).eval t = P4AOriginalSavedSixthArchive.oldPlane i mask t := by
  unfold savedOldPlaneA P4AOriginalSavedSixthArchive.oldPlane
  split_ifs <;> simp
@[simp] theorem savedOldUpper_exact (i : P4AOriginalSavedSixthArchive.Row) (t : SixPoint) :
    (savedOldUpper i).eval t = P4AOriginalSavedSixthArchive.oldUpper i t := by
  simp [savedOldUpper, eval_maxRows, P4AOriginalSavedSixthArchive.oldUpper, Program.eval]
@[simp] theorem savedEndpoint_exact (i : P4AOriginalSavedSixthArchive.Row) (t : SixPoint) :
    (savedEndpoint i).eval t = P4AOriginalSavedSixthArchive.endpoint i t := by
  simp [savedEndpoint, Program.eval, P4AOriginalSavedSixthArchive.endpoint, VariableEnvelope.v_eq_min]

def savedSourceTests (i : P4AOriginalSavedSixthArchive.Row) : List (Gate 6) :=
  static (P4AOriginalSavedSixthArchive.denominator i = 400 ∧ 32 ≤ P4AOriginalSavedSixthArchive.selectedMask i ∧ P4AOriginalSavedSixthArchive.selectedMask i < 64) ++
  halfOpenBox (P4AOriginalSavedSixthArchive.lowerCorner i) (P4AOriginalSavedSixthArchive.upperCorner i) ++
  [LE (atom (K (1 / 50))) (atom (X 5)),
   LE (savedEndpoint i) (atom (sum6A.add ((X 5).scale 3))),
   LT (savedOldUpper i) (savedEndpoint i)] ++
  indexed Finset.univ (fun j => LT (atom (fullA j)) (savedEndpoint i)) ++
  indexed (Finset.univ.filter fun j : Fin 6 => Certificates.P2OriginalSixthElevenLogSemantics.bit (P4AOriginalSavedSixthArchive.selectedMask i) j.val = false)
    (fun j => LT (atom (remainingA (P4AOriginalSavedSixthArchive.selectedMask i) j)) (savedEndpoint i))

@[simp] theorem savedSourceTests_exact (i : P4AOriginalSavedSixthArchive.Row) (t : SixPoint) :
    Passed t (savedSourceTests i) ↔ P4AOriginalSavedSixthArchive.Source i t := by
  simp only [savedSourceTests, passed_append, passed_static, passed_halfOpenBox, passed_indexed,
    passed_cons, passed_nil, holds_LT, holds_LE]
  simp [Program.eval, P4AOriginalSavedSixthArchive.Source, P4AOriginalSavedSixthArchive.InBox,
    sub_le_iff_le_add, add_comm, and_assoc, and_left_comm, and_comm]

def fifthAtSix (d : OriginalData) (b : ℚ) : Program 6 :=
  (fifthProgram d b).pull Fin.castSucc

def savedTests (d : OriginalData) (b : ℚ) (i : P4AOriginalSavedSixthArchive.Row) : List (Gate 6) :=
  savedSourceTests i ++
  [LT (atom h3A) (atom (K (b : ℝ))), LT (atom h5A) (atom (K (b : ℝ))),
   LE (fifthAtSix d b) (savedOldUpper i)]

def savedProgram (d : OriginalData) (b : ℚ) : Program 6 :=
  maxRows (savedTests d b) savedEndpoint (fifthAtSix d b)
    (Finset.univ : Finset P4AOriginalSavedSixthArchive.Row).toList

@[simp] theorem savedTests_exact (d : OriginalData) (b : ℚ) (i : P4AOriginalSavedSixthArchive.Row) (t : SixPoint) :
    Passed t (savedTests d b i) ↔ P4AOriginalSavedSixthArchive.Source i t ∧
      Certificates.P2OriginalSixthElevenLogSemantics.H3 t < (b : ℝ) ∧ Certificates.P2OriginalSixthElevenLogSemantics.H5 t < (b : ℝ) ∧
      (fifthAtSix d b).eval t ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
  simp only [savedTests, passed_append, savedSourceTests_exact, passed_cons, passed_nil,
    holds_LT, holds_LE, Program.eval, eval_h3A, eval_h5A, Affine.eval_const,
    savedOldUpper_exact, and_true]

def elevenOldA (c : ElevenCell) : Affine 6 :=
  match c.family with
  | .singleton | .tent33 => r0A
  | .pair17 => descending ((X 0).add (X 4))
  | .pair12 => ascending ((X 2).add (X 3))
def elevenNewA (c : ElevenCell) : Affine 6 :=
  if c.family = .tent33 then asc33A.sub (K Certificates.P2OriginalSixthElevenLogSemantics.eta) else clippedA

@[simp] theorem elevenOldA_exact (c : ElevenCell) (t : SixPoint) :
    (elevenOldA c).eval t = Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  cases hf : c.family <;>
    simp [elevenOldA, Certificates.P2OriginalSixthElevenLogSemantics.oldCap, hf, VariableEnvelope.A, VariableEnvelope.C] <;> ring
@[simp] theorem elevenNewA_exact (c : ElevenCell) (t : SixPoint) :
    (elevenNewA c).eval t = Certificates.P2OriginalSixthElevenLogSemantics.newCap c t := by
  unfold elevenNewA Certificates.P2OriginalSixthElevenLogSemantics.newCap
  split_ifs <;> simp

def branchTest (desc : Bool) (upper s : Affine 6) : Gate 6 :=
  if desc then LE (atom (descending s)) (atom upper)
  else LE (atom s) (atom ((upper.scale 2).sub (K 1)))

@[simp] theorem branchTest_exact (desc : Bool) (upper s : Affine 6) (t : SixPoint) :
    (branchTest desc upper s).holds t ↔ Certificates.P2OriginalSixthElevenLogSemantics.branchLicense desc (upper.eval t) (s.eval t) := by
  cases desc <;>
    simp [branchTest, Certificates.P2OriginalSixthElevenLogSemantics.branchLicense, LE, Gate.holds, Program.eval, VariableEnvelope.C,
      mul_div_assoc]

def priorityTests (c : ElevenCell) : List (Gate 6) :=
  match c with
  | .singleton34_1371 => [LT (atom desc33A) (atom (elevenNewA c))]
  | .singleton50_1353 | .singleton50_1355 =>
      [LT (atom desc33A) (atom (elevenNewA c)), LT (atom asc34A) (atom (elevenNewA c))]
  | .tent33_1371 | .tent33_1867 => [LT (atom asc33A) (atom clippedA)]
  | _ => []
def winnerTests (c : ElevenCell) : List (Gate 6) :=
  match c.family with
  | .pair17 => [LT (atom (K Certificates.P2OriginalSixthElevenLogSemantics.mu)) (atom ((X 0).add (X 4)))]
  | .pair12 => [LT (atom ((X 2).add (X 3))) (atom (K Certificates.P2OriginalSixthElevenLogSemantics.mu))]
  | _ => []
def pairAboveTests (c : ElevenCell) : List (Gate 6) :=
  if c.family = .pair17 ∨ c.family = .pair12 then
    [LT (atom r0A) (atom (elevenOldA c))] else []

@[simp] theorem priorityTests_exact (c : ElevenCell) (t : SixPoint) :
    Passed t (priorityTests c) ↔ Certificates.P2OriginalSixthElevenLogSemantics.priority c t := by
  cases c <;> simp [priorityTests, Certificates.P2OriginalSixthElevenLogSemantics.priority, Passed, LT, Gate.holds, Program.eval]
@[simp] theorem winnerTests_exact (c : ElevenCell) (t : SixPoint) :
    Passed t (winnerTests c) ↔ Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane c t := by
  cases hf : c.family <;>
    simp [winnerTests, Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane, hf, Passed, LT, Gate.holds, Program.eval]
@[simp] theorem pairAboveTests_exact (c : ElevenCell) (t : SixPoint) :
    Passed t (pairAboveTests c) ↔
      (c.family = .pair17 ∨ c.family = .pair12 → Certificates.P2OriginalSixthElevenLogSemantics.R0 t < Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t) := by
  by_cases hp : c.family = .pair17 ∨ c.family = .pair12 <;>
    simp [pairAboveTests, hp, Passed, LT, Gate.holds, Program.eval]

/-- Every named physical field is represented; in particular oldBranches
are weak inequalities, not changed to strict inequalities by a trim. -/
def elevenSourceTests (c : ElevenCell) : List (Gate 6) :=
  [LT (atom (K 0)) (atom (X 5)),
   LT (atom (X 5)) (atom (X 4)), LT (atom (X 4)) (atom (X 3)),
   LT (atom (X 3)) (atom (X 2)), LT (atom (X 2)) (atom (X 1)),
   LT (atom (X 1)) (atom (X 0)), LT (atom (X 0)) (atom (K Certificates.P2OriginalSixthElevenLogSemantics.mu)),
   LT (atom (X 5)) (atom (K (1 / 50))), LT (atom (K (53 / 4608))) (atom (X 5)),
   LT (atom h3A) (atom r0A), LT (atom h5A) (atom r0A), LE (atom wA) (atom r0A),
   LE (atom r0A) (atom (elevenOldA c)), LT (atom (elevenOldA c)) (atom (elevenNewA c)),
   LT (atom (elevenNewA c)) (atom (ascending (selectedA c.selectedMask))),
   LT (atom (elevenNewA c)) (atom (descending (selectedA c.selectedMask))),
   LT (atom (X 5)) (atom (r0A.sub sum6A)),
   LT (atom ((elevenNewA c).sub sum6A)) (atom ((X 5).scale 3))] ++
  indexed (Finset.Icc 1 31) (fun m => branchTest (c.descending m) (elevenOldA c) (subsetA m)) ++
  indexed (Finset.Icc 1 7) (fun m => branchTest (c.descending m) r0A (subsetA m)) ++
  indexed Finset.univ (fun j => LT (atom (fullA j)) (atom (elevenNewA c))) ++
  indexed (Finset.univ.filter fun j : Fin 6 => Certificates.P2OriginalSixthElevenLogSemantics.bit c.selectedMask j.val = false)
    (fun j => LT (atom (remainingA c.selectedMask j)) (atom (elevenNewA c))) ++
  pairAboveTests c ++ winnerTests c ++ priorityTests c

private theorem physicalCell_iff (c : ElevenCell) (t : SixPoint) : Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ↔
    0 < t 5 ∧
    (t 5 < t 4 ∧ t 4 < t 3 ∧ t 3 < t 2 ∧ t 2 < t 1 ∧ t 1 < t 0) ∧
    t 0 < Certificates.P2OriginalSixthElevenLogSemantics.mu ∧ t 5 < 1 / 50 ∧ 53 / 4608 < t 5 ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H3 t < Certificates.P2OriginalSixthElevenLogSemantics.R0 t ∧ Certificates.P2OriginalSixthElevenLogSemantics.H5 t < Certificates.P2OriginalSixthElevenLogSemantics.R0 t ∧ Certificates.P2OriginalSixthElevenLogSemantics.W t ≤ Certificates.P2OriginalSixthElevenLogSemantics.R0 t ∧
    (∀ m ∈ Finset.Icc 1 31, Certificates.P2OriginalSixthElevenLogSemantics.branchLicense (c.descending m) (Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t) (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t)) ∧
    (∀ m ∈ Finset.Icc 1 7, Certificates.P2OriginalSixthElevenLogSemantics.branchLicense (c.descending m) (Certificates.P2OriginalSixthElevenLogSemantics.R0 t) (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t)) ∧
    Certificates.P2OriginalSixthElevenLogSemantics.R0 t ≤ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t ∧
    (c.family = .pair17 ∨ c.family = .pair12 → Certificates.P2OriginalSixthElevenLogSemantics.R0 t < Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t) ∧
    Certificates.P2OriginalSixthElevenLogSemantics.winnerPlane c t ∧ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t < Certificates.P2OriginalSixthElevenLogSemantics.newCap c t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.newCap c t < (1 + Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask t) / 2 ∧
    Certificates.P2OriginalSixthElevenLogSemantics.newCap c t < 57 / 64 - 3 * Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask t / 2 ∧
    (∀ j, Certificates.P2OriginalSixthElevenLogSemantics.fullSquare j t < Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) ∧
    (∀ j, Certificates.P2OriginalSixthElevenLogSemantics.bit c.selectedMask j.val = false → Certificates.P2OriginalSixthElevenLogSemantics.remainingSquare c.selectedMask j t < Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) ∧
    t 5 < Certificates.P2OriginalSixthElevenLogSemantics.R0 t - Certificates.P2OriginalSixthElevenLogSemantics.S6 t ∧ Certificates.P2OriginalSixthElevenLogSemantics.newResidual c t < 3 * t 5 ∧ Certificates.P2OriginalSixthElevenLogSemantics.priority c t := by
  constructor
  · intro h
    exact ⟨h.rpos, h.order, h.largest, h.oldCutoff, h.compactCutoff,
      h.history3, h.history5, h.oldW, h.oldBranches, h.first3Branches,
      h.comparison, h.pairAbove, h.winner, h.positiveGap, h.selectedAscending,
      h.selectedDescending, h.fullSquares, h.remainingSquares, h.oldArgument,
      h.newArgument, h.priority⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩

@[simp] theorem elevenSourceTests_exact (c : ElevenCell) (t : SixPoint) :
    Passed t (elevenSourceTests c) ↔ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t := by
  rw [physicalCell_iff]
  simp only [elevenSourceTests, passed_append, passed_indexed, priorityTests_exact,
    winnerTests_exact, pairAboveTests_exact, branchTest_exact]
  simp [Passed, LT, LE, Gate.holds, Program.eval, Certificates.P2OriginalSixthElevenLogSemantics.newResidual,
    VariableEnvelope.A, VariableEnvelope.C, mul_div_assoc,
    and_assoc, and_left_comm, and_comm]

def elevenTests (d : OriginalData) (b : ℚ) (c : ElevenCell) : List (Gate 6) :=
  elevenSourceTests c ++
  [LT (atom h5A) (fifthAtSix d b), LE (fifthAtSix d b) (atom (elevenOldA c))]

def elevenProgram (d : OriginalData) (b : ℚ) : Program 6 :=
  maxRows (elevenTests d b) (fun c => atom (elevenNewA c)) (savedProgram d b) Certificates.P2OriginalSixthElevenLogSemantics.allCells

@[simp] theorem elevenTests_exact (d : OriginalData) (b : ℚ) (c : ElevenCell) (t : SixPoint) :
    Passed t (elevenTests d b c) ↔ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ∧
      Certificates.P2OriginalSixthElevenLogSemantics.H5 t < (fifthAtSix d b).eval t ∧ (fifthAtSix d b).eval t ≤ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t := by
  simp only [elevenTests, passed_append, elevenSourceTests_exact, passed_cons, passed_nil,
    holds_LT, holds_LE, Program.eval, eval_h5A, elevenOldA_exact, and_true]

/-- Literal affine pullback of the original chart; no original row is
replaced by a precomputed claim about a polytope or its vertices. -/
def chartA : Fin 6 → Affine 6 :=
  ![X 0, X 1, X 2, r0A.sub sum5A, r0A.sub h5A, X 5]
def laterRowA (c : LaterCell) (r : P4AOriginalSixthLaterLiteral.Affine) : Affine 6 :=
  (K (r 0)).add (Affine.sum Finset.univ fun j : Fin 6 =>
    (if P4AOriginalSixthLaterLiteral.mapped c then chartA j else X j).scale (r j.succ))
def laterEndpointA (c : LaterCell) : Affine 6 :=
  ((if P4AOriginalSixthLaterLiteral.descending c then descending (selectedA (P4AOriginalSixthLaterLiteral.mask c))
    else ascending (selectedA (P4AOriginalSixthLaterLiteral.mask c)))).sub (K Certificates.P2OriginalSixthElevenLogSemantics.eta)
def laterComparisonA (c : LaterCell) : Affine 6 :=
  if P4AOriginalSixthLaterLiteral.comparisonChart c = 0 then r0A
  else if P4AOriginalSixthLaterLiteral.comparisonChart c = 1 then desc33A else asc34A

@[simp] theorem chartA_exact (j : Fin 6) (t : SixPoint) :
    (chartA j).eval t = Certificates.P2OriginalSixthElevenLogSemantics.chart t j := by
  fin_cases j <;> simp [chartA, Certificates.P2OriginalSixthElevenLogSemantics.chart]
@[simp] theorem laterRowA_exact (c : LaterCell) (r : P4AOriginalSixthLaterLiteral.Affine) (t : SixPoint) :
    (laterRowA c r).eval t = P4AOriginalSixthLaterSemantics.eval r (P4AOriginalSixthLaterSemantics.coordinates c t) := by
  unfold laterRowA P4AOriginalSixthLaterSemantics.eval P4AOriginalSixthLaterSemantics.coordinates
  by_cases hm : P4AOriginalSixthLaterLiteral.mapped c = true
  · simp [hm]
  · have hm' : P4AOriginalSixthLaterLiteral.mapped c = false := Bool.eq_false_iff.mpr hm
    simp [hm']
@[simp] theorem laterEndpointA_exact (c : LaterCell) (t : SixPoint) :
    (laterEndpointA c).eval t = P4AOriginalSixthLaterSemantics.endpoint c t := by
  unfold laterEndpointA P4AOriginalSixthLaterSemantics.endpoint P4AOriginalSixthLaterSemantics.selectedSum
  by_cases hd : P4AOriginalSixthLaterLiteral.descending c = true
  · simp [hd, VariableEnvelope.C, mul_div_assoc]
  · have hd' : P4AOriginalSixthLaterLiteral.descending c = false := Bool.eq_false_iff.mpr hd
    simp [hd', VariableEnvelope.A]
@[simp] theorem laterComparisonA_exact (c : LaterCell) (t : SixPoint) :
    (laterComparisonA c).eval t = P4AOriginalSixthLaterSemantics.comparison c t := by
  unfold laterComparisonA P4AOriginalSixthLaterSemantics.comparison
  split_ifs <;> simp

def laterSourceTests (c : LaterCell) : List (Gate 6) :=
  (P4AOriginalSixthLaterLiteral.rows c).map fun r => LT (atom (K 0)) (atom (laterRowA c r))

@[simp] theorem laterSourceTests_exact (c : LaterCell) (t : SixPoint) :
    Passed t (laterSourceTests c) ↔ P4AOriginalSixthLaterSemantics.Source c t := by
  simp [laterSourceTests, Passed, LT, Gate.holds, Program.eval, P4AOriginalSixthLaterSemantics.Source]

/-- Every comparison reads the same prior-stage program. In particular a
parallel maximum's fold accumulator is NOT a different current parent. -/
def laterTests (stage : ℕ) (current : Program 6) (c : LaterCell) : List (Gate 6) :=
  static (P4AOriginalSixthLaterLiteral.stage c = stage) ++ laterSourceTests c ++
  [LT (atom h5A) current, LE current (atom (laterComparisonA c)),
   LT (atom (laterComparisonA c)) (atom (laterEndpointA c))]

def laterStep (stage : ℕ) (current : Program 6) : Program 6 :=
  maxRows (laterTests stage current) (fun c => atom (laterEndpointA c)) current
    (Finset.univ : Finset LaterCell).toList

def afterProgram (d : OriginalData) (b : ℚ) : ℕ → Program 6
  | 0 => elevenProgram d b
  | j + 1 => laterStep j (afterProgram d b j)

def completeProgram (d : OriginalData) (b : ℚ) : Program 6 := afterProgram d b 8

@[simp] theorem laterTests_exact (stage : ℕ) (current : Program 6) (c : LaterCell) (t : SixPoint) :
    Passed t (laterTests stage current c) ↔
      P4AOriginalSixthLaterLiteral.stage c = stage ∧ P4AOriginalSixthLaterSemantics.Source c t ∧ Certificates.P2OriginalSixthElevenLogSemantics.H5 t < current.eval t ∧
      current.eval t ≤ P4AOriginalSixthLaterSemantics.comparison c t ∧ P4AOriginalSixthLaterSemantics.comparison c t < P4AOriginalSixthLaterSemantics.endpoint c t := by
  simp only [laterTests, passed_append, passed_static, laterSourceTests_exact, passed_cons,
    passed_nil, holds_LT, holds_LE, Program.eval, eval_h5A, laterComparisonA_exact,
    laterEndpointA_exact, and_true, and_assoc]

/-- Coordinate bridge from the own-sixth ancestor to its own fifth.
No later prime is consulted to determine the predecessor's value. -/
theorem fifthAtSix_at_history (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = (b : ℝ)) :
    (fifthAtSix d b).eval (primeHistoryLogCoordinates N 6 pre) = actualParent5 d N pre := by
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h5b : lambda3 d N (rosserAncestor 5 pre) = (b : ℝ) := by
    rw [lambda3_ancestor d N 5 (by decide), hb]
  have hc : (fun i : Fin 5 => primeHistoryLogCoordinates N 6 pre i.castSucc) =
      primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) := by
    funext i
    exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 6) i).symm
  rw [fifthAtSix, Program.eval_pull, hc, fifth_at_history d b N _ h5len h5b]
  rfl

theorem savedProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = (b : ℝ)) :
    (savedProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      savedExponent e q om N pre := by
  have hf := fifthAtSix_at_history (data e q om) b N pre hlen hb
  simp only [savedProgram, eval_maxRows, Finset.toList_toFinset,
    savedExponent, savedEligible, hlen, true_and, hb]
  congr 1
  · funext i
    apply propext
    simpa only [hf, fifth] using savedTests_exact (data e q om) b i
      (primeHistoryLogCoordinates N 6 pre)
  · funext i
    exact savedEndpoint_exact i _
  · exact hf

theorem elevenProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = (b : ℝ)) :
    (elevenProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      elevenExponent e q om N pre := by
  have hf := fifthAtSix_at_history (data e q om) b N pre hlen hb
  simp only [elevenProgram, eval_maxRows, elevenExponent, eligibleSixth,
    hlen, true_and]
  congr 1
  · funext c
    apply propext
    simpa only [hf] using elevenTests_exact (data e q om) b c
      (primeHistoryLogCoordinates N 6 pre)
  · funext c
    exact elevenNewA_exact c _
  · exact savedProgram_at_history e q om N b pre hlen hb

theorem afterProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (j : ℕ) :
    (afterProgram (data e q om) b j).eval (primeHistoryLogCoordinates N 6 pre) =
      afterLater e q om N pre j := by
  induction j with
  | zero => exact elevenProgram_at_history e q om N b pre hlen hb
  | succ j ih =>
      simp only [afterProgram, laterStep, eval_maxRows, Finset.toList_toFinset,
        afterLater, applyLater, laterEligible, hlen, true_and]
      congr 1
      · funext c
        apply propext
        simpa only [ih] using laterTests_exact j (afterProgram (data e q om) b j) c
          (primeHistoryLogCoordinates N 6 pre)
      · funext c
        exact laterEndpointA_exact c _
      · exact ih

/-- Exact endpoint, not an approximation, and not the held-eleven parent. -/
theorem completeProgram_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 (data e q om) N pre = (b : ℝ)) :
    (completeProgram (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      currentSixthExponent e q om N pre :=
  afterProgram_at_history e q om N b pre hlen hb 8

end
end ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
