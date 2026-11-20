import ImbalancedChen.P1FiniteAffineDecisionProgram
import ImbalancedChen.P4AOriginalFull87FiniteParentCaps

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The actual original fourth and fifth producers become finite affine
comparison programs. Static archive admission is evaluated before N;
point-dependent tests are the exact closed / half-open box inequalities.
The only scalar input is the already finite original third-table value.
No row geometry, saving or source bound is silently inferred by compiling.
-/
namespace ImbalancedChen.P4AOriginalFourthFifthAffinePrograms
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram
open P1OriginalVariableFourthContinuation
open P2OriginalFourthCapProducerInterface
open P5OriginalCommonRefinedConstructor

abbrev K {k : ℕ} := @Affine.const k
abbrev X {k : ℕ} := @Affine.coord k
abbrev atom {k : ℕ} := @Program.leaf k

def LT {k : ℕ} (a b : Program k) : Gate k := ⟨true, a, b⟩
def LE {k : ℕ} (a b : Program k) : Gate k := ⟨false, a, b⟩
def Passed {k : ℕ} (t : Fin k → ℝ) (gs : List (Gate k)) : Prop :=
  ∀ g ∈ gs, g.holds t

def indexed {k : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Gate k) : List (Gate k) :=
  s.toList.map g

def static {k : ℕ} (P : Prop) : List (Gate k) :=
  if P then [] else [LT (atom (K 0)) (atom (K 0))]

@[simp] theorem passed_nil {k : ℕ} (t : Fin k → ℝ) : Passed t [] := by simp [Passed]
@[simp] theorem passed_cons {k : ℕ} (t : Fin k → ℝ) (g : Gate k) (gs : List (Gate k)) :
    Passed t (g :: gs) ↔ g.holds t ∧ Passed t gs := by simp [Passed]

@[simp] theorem passed_append {k : ℕ} (t : Fin k → ℝ) (xs ys : List (Gate k)) :
    Passed t (xs ++ ys) ↔ Passed t xs ∧ Passed t ys := by
  simp [Passed]
@[simp] theorem passed_indexed {k : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Gate k) (t : Fin k → ℝ) :
    Passed t (indexed s g) ↔ ∀ i ∈ s, (g i).holds t := by
  simp [Passed, indexed]
@[simp] theorem passed_static {k : ℕ} (t : Fin k → ℝ) (P : Prop) :
    Passed t (static P) ↔ P := by
  by_cases hP : P <;> simp [static, hP, Passed, LT, Gate.holds, Program.eval]
@[simp] theorem holds_LT {k : ℕ} (t : Fin k → ℝ) (a b : Program k) :
    (LT a b).holds t ↔ a.eval t < b.eval t := Iff.rfl
@[simp] theorem holds_LE {k : ℕ} (t : Fin k → ℝ) (a b : Program k) :
    (LE a b).holds t ↔ a.eval t ≤ b.eval t := Iff.rfl

/-- Ordinary affine arithmetic, not an arbitrary function leaf. -/
def maskAffine {k : ℕ} (I : Finset (Fin k)) : Affine k :=
  Affine.sum I X

def ascending {k : ℕ} (a : Affine k) : Affine k :=
  (K (1 / 2)).add (a.scale (1 / 2))
def descending {k : ℕ} (a : Affine k) : Affine k :=
  (K (57 / 64)).sub (a.scale (3 / 2))

def tentProgram {k : ℕ} (I : Finset (Fin k)) (loss : ℝ) : Program k :=
  .inf (atom ((ascending (maskAffine I)).sub (K loss)))
    (atom ((descending (maskAffine I)).sub (K loss)))

@[simp] theorem eval_maskAffine {k : ℕ} (I : Finset (Fin k)) (t : Fin k → ℝ) :
    (maskAffine I).eval t = ∑ i ∈ I, t i := by simp [maskAffine]
@[simp] theorem eval_ascending {k : ℕ} (a : Affine k) (t : Fin k → ℝ) :
    (ascending a).eval t = VariableEnvelope.A (a.eval t) := by
  simp [ascending, VariableEnvelope.A]
  ring
@[simp] theorem eval_descending {k : ℕ} (a : Affine k) (t : Fin k → ℝ) :
    (descending a).eval t = VariableEnvelope.C (a.eval t) := by
  simp [descending, VariableEnvelope.C]
@[simp] theorem eval_tentProgram {k : ℕ} (I : Finset (Fin k))
    (loss : ℝ) (t : Fin k → ℝ) :
    (tentProgram I loss).eval t = VariableEnvelope.v (∑ i ∈ I, t i) - loss := by
  simp only [tentProgram, Program.eval, Affine.eval_sub, eval_ascending,
    eval_descending, eval_maskAffine, Affine.eval_const, VariableEnvelope.v_eq_min]
  rw [← min_sub]

@[simp] theorem three_halves_mul (x : ℝ) : (3 / 2 : ℝ) * x = 3 * x / 2 := by ring

/-- The lower/upper conventions are kept separate, including equality. -/
def closedBox {k : ℕ} (lo hi : Fin k → ℝ) : List (Gate k) :=
  indexed Finset.univ (fun i => LE (atom (K (lo i))) (atom (X i))) ++
  indexed Finset.univ (fun i => LE (atom (X i)) (atom (K (hi i))))

def halfOpenBox {k : ℕ} (lo hi : Fin k → ℝ) : List (Gate k) :=
  indexed Finset.univ (fun i => LE (atom (K (lo i))) (atom (X i))) ++
  indexed Finset.univ (fun i => LT (atom (X i)) (atom (K (hi i))))

@[simp] theorem passed_closedBox {k : ℕ} (t lo hi : Fin k → ℝ) :
    Passed t (closedBox lo hi) ↔ (∀ i, lo i ≤ t i) ∧ (∀ i, t i ≤ hi i) := by
  simp [closedBox, Program.eval]
@[simp] theorem passed_halfOpenBox {k : ℕ} (t lo hi : Fin k → ℝ) :
    Passed t (halfOpenBox lo hi) ↔ ∀ i, lo i ≤ t i ∧ t i < hi i := by
  simp [halfOpenBox, Program.eval, forall_and]

def fourthTests (d : OriginalData) (r : ProducerRow) : List (Gate 4) :=
  static (d.licensed4 r) ++
    closedBox (fun i => (r.lower i : ℝ)) (fun i => (r.upper i : ℝ))

def fourthCandidate (d : OriginalData) (r : ProducerRow) : Program 4 :=
  tentProgram r.selected (2 * (d.e : ℝ))

def fourthProgram (d : OriginalData) (b : ℚ) : Program 4 :=
  maxRows (fourthTests d) (fourthCandidate d) (atom (K (b : ℝ))) d.rows4.toList

@[simp] theorem fourthTests_exact (d : OriginalData) (r : ProducerRow) (t : Fin 4 → ℝ) :
    Passed t (fourthTests d r) ↔ producerEligible d.licensed4 r t := by
  simp only [fourthTests, passed_append, passed_static, passed_closedBox,
    producerEligible, ProducerRow.box, Set.mem_setOf_eq]
@[simp] theorem fourthCandidate_exact (d : OriginalData) (r : ProducerRow)
    (t : Fin 4 → ℝ) :
    (fourthCandidate d r).eval t = r.bufferedCandidate (d.e : ℝ) t := by
  rw [ProducerRow.bufferedCandidate_eq]
  exact eval_tentProgram _ _ _

theorem fourthProgram_exact (d : OriginalData) (b : ℚ) (t : Fin 4 → ℝ) :
    (fourthProgram d b).eval t =
      finiteMax d.rows4 (fun r => producerEligible d.licensed4 r t)
        (fun r => r.bufferedCandidate (d.e : ℝ) t) (b : ℝ) := by
  simp only [fourthProgram, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext r
    exact propext (fourthTests_exact d r t)
  · funext r
    exact fourthCandidate_exact d r t
  · exact Affine.eval_const _ _

def fifthTests (d : OriginalData) (r : P1OriginalVariableFifthContinuation.FifthRow d.m) :
    List (Gate 5) :=
  static (r.cell ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
    d.e d.chi d.m d.omega d.J5 ∧
    P1OriginalVariableFifthContinuation.gateCheck d.e d.m r = true) ++
  halfOpenBox (logPrimeMeshLo 0 (19 / 96) d.m r.cell)
    (logPrimeMeshHi 0 (19 / 96) d.m r.cell)

def fifthCandidate (d : OriginalData)
    (r : P1OriginalVariableFifthContinuation.FifthRow d.m) : Program 5 :=
  tentProgram r.selected (2 * (d.e : ℝ))

def fifthProgram (d : OriginalData) (b : ℚ) : Program 5 :=
  maxRows (fifthTests d) (fifthCandidate d)
    ((fourthProgram d b).pull Fin.castSucc) d.rows5.toList

@[simp] theorem fifthTests_exact (d : OriginalData)
    (r : P1OriginalVariableFifthContinuation.FifthRow d.m) (t : Fin 5 → ℝ) :
    Passed t (fifthTests d r) ↔
      P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega d.J5 r t := by
  simp only [fifthTests, passed_append, passed_static, passed_halfOpenBox,
    P1OriginalVariableFifthContinuation.eligible, mem_logPrimeMeshCell, and_assoc]

@[simp] theorem fifthCandidate_exact (d : OriginalData)
    (r : P1OriginalVariableFifthContinuation.FifthRow d.m) (t : Fin 5 → ℝ) :
    (fifthCandidate d r).eval t =
      P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t := by
  rw [P1OriginalVariableFifthContinuation.candidate,
    P1OriginalVariableFifthContinuation.envelope_eq_v]
  exact eval_tentProgram _ _ _

theorem fifthProgram_exact (d : OriginalData) (b : ℚ) (t : Fin 5 → ℝ) :
    (fifthProgram d b).eval t =
      finiteMax d.rows5
        (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega d.J5 r t)
        (fun r => P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected t)
        ((fourthProgram d b).eval (fun i => t i.castSucc)) := by
  simp only [fifthProgram, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext r
    exact propext (fifthTests_exact d r t)
  · funext r
    exact fifthCandidate_exact d r t
  · exact Program.eval_pull _ _ _

/-- These intermediate bridge hypotheses are values, not estimates.
The full87 terminal derives them from the existing actual third source. -/
theorem fourth_at_history (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 4) (hb : lambda3 d N pre = (b : ℝ)) :
    (fourthProgram d b).eval (primeHistoryLogCoordinates N 4 pre) = exponent4 d N pre := by
  rw [fourthProgram_exact, exponent4, if_pos hlen, hb]

theorem fifth_at_history (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 5) (hb : lambda3 d N pre = (b : ℝ)) :
    (fifthProgram d b).eval (primeHistoryLogCoordinates N 5 pre) = exponent5 d N pre := by
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h4b : lambda3 d N (rosserAncestor 4 pre) = (b : ℝ) := by
    rw [P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 4 (by decide), hb]
  have hc : (fun i : Fin 4 => primeHistoryLogCoordinates N 5 pre i.castSucc) =
      primeHistoryLogCoordinates N 4 (rosserAncestor 4 pre) := by
    funext i
    exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 4 ≤ 5) i).symm
  rw [fifthProgram_exact, hc, fourth_at_history d b N _ h4len h4b,
    exponent5, if_pos hlen]

end
end ImbalancedChen.P4AOriginalFourthFifthAffinePrograms
