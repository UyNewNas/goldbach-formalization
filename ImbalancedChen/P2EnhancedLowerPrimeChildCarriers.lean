import ImbalancedChen.P5OriginalFeedbackDomains

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual finite integer-prime children of ONE labelled parent history in
the original lower graph. Original BH, all70 W1 and all36 W2 domains are
used literally. Filters are the original prime/coprime, physical ceiling
and positive same-Q residual conditions; no analytic admission proof or
target BV support bound is a field. Pair children retain both labels and
append in physical decreasing order [larger,smaller].
-/

namespace ImbalancedChen.P2EnhancedLowerPrimeChildCarriers
noncomputable section
open Set Finset Classical
open P5OriginalActionMassBound

inductive SingleRule where
  | buchstab (upperParent : Bool) (s : ℝ)
  | w1 (target : Fin 7) (anchor : Fin 10)
  | w2 (bank : Fin 36) (piece : Fin 3)

def parentProduct (old : List ℕ) : ℕ := old.prod
def residualLevel (Q : ℝ) (old : List ℕ) : ℝ := Q/(parentProduct old : ℝ)
def relativePrime (Q : ℝ) (old : List ℕ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ)/Real.log (residualLevel Q old)
def physicalPrime (N p : ℕ) : ℝ := Real.log (p : ℝ)/Real.log (N : ℝ)
def buchstabArgument (Q : ℝ) (old : List ℕ) (p : ℕ) : ℝ :=
  (Real.log (residualLevel Q old)-Real.log (p : ℝ))/Real.log (p : ℝ)

def singleDomain (rule : SingleRule) (Q : ℝ) (old : List ℕ) (p : ℕ) : Prop :=
  match rule with
  | .buchstab up s =>
      (if up then 1≤s else 2≤s) ∧
        buchstabArgument Q old p ∈
          (if up then buchstabUpperDomain s else buchstabLowerDomain s)
  | .w1 i j => relativePrime Q old p ∈ W1Domain i j
  | .w2 bank piece => relativePrime Q old p ∈ W2SingletonDomain (originalW2At bank) piece

def singleEdgeScalar : SingleRule → ℝ
  | .buchstab _ _ => 1
  | .w1 _ _ => 1/2
  | .w2 _ _ => 1/5

/-- Physical level and ceiling are actual geometric constructor tests.
The complete marked product stays below this SAME total Q. -/
def parentWindow (N : ℕ) (Q : ℝ) (old : List ℕ) (chi : ℝ) : Prop :=
  1<N ∧ 0<parentProduct old ∧ (parentProduct old : ℝ)<Q ∧ Q≤(N : ℝ) ∧ 0<chi

def primeCandidates (N : ℕ) (old : List ℕ) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun p => p.val.Prime ∧ p.val.Coprime (N*parentProduct old))

def singleChildren (rule : SingleRule) (N : ℕ) (Q : ℝ) (old : List ℕ) (chi : ℝ) :
    Finset (Fin (N+1)) :=
  (primeCandidates N old).filter (fun p =>
    parentWindow N Q old chi ∧ singleDomain rule Q old p.val ∧
      physicalPrime N p.val<chi ∧ ((parentProduct old*p.val : ℕ) : ℝ)<Q)

/-- Coordinates0/1 are the SMALLER/LARGER prime, exactly as in D5+..D8. -/
def pairPoint (Q : ℝ) (old : List ℕ) (small large : ℕ) : Point :=
  ![relativePrime Q old small,relativePrime Q old large]

def pairChildren (bank : Fin 36) (piece : Fin 4) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (chi : ℝ) : Finset (Fin (N+1) × Fin (N+1)) :=
  ((primeCandidates N old) ×ˢ (primeCandidates N old)).filter (fun p =>
    parentWindow N Q old chi ∧ p.1.val<p.2.val ∧
      pairPoint Q old p.1.val p.2.val ∈ W2PairDomain (originalW2At bank) piece ∧
      physicalPrime N p.1.val<chi ∧ physicalPrime N p.2.val<chi ∧
      ((parentProduct old*p.2.val*p.1.val : ℕ) : ℝ)<Q)

def singleWord (old : List ℕ) (p : ℕ) : List ℕ := old++[p]
def pairWord (old : List ℕ) (small large : ℕ) : List ℕ := old++[large,small]

theorem mem_singleChildren {rule : SingleRule} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1)} :
    p ∈ singleChildren rule N Q old chi ↔
      (p.val.Prime ∧ p.val.Coprime (N*parentProduct old)) ∧
      parentWindow N Q old chi ∧ singleDomain rule Q old p.val ∧
      physicalPrime N p.val<chi ∧ ((parentProduct old*p.val : ℕ) : ℝ)<Q := by
  simp only [singleChildren,primeCandidates,Finset.mem_filter,Finset.mem_univ,true_and]

theorem mem_pairChildren {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)} :
    p ∈ pairChildren bank piece N Q old chi ↔
      ((p.1.val.Prime ∧ p.1.val.Coprime (N*parentProduct old)) ∧
       (p.2.val.Prime ∧ p.2.val.Coprime (N*parentProduct old))) ∧
      parentWindow N Q old chi ∧ p.1.val<p.2.val ∧
      pairPoint Q old p.1.val p.2.val ∈ W2PairDomain (originalW2At bank) piece ∧
      physicalPrime N p.1.val<chi ∧ physicalPrime N p.2.val<chi ∧
      ((parentProduct old*p.2.val*p.1.val : ℕ) : ℝ)<Q := by
  simp only [pairChildren,primeCandidates,Finset.mem_filter,Finset.mem_product,
    Finset.mem_univ,true_and]

theorem singleWord_history (old : List ℕ) (p : ℕ) :
    (singleWord old p).take old.length=old ∧ (singleWord old p).length=old.length+1 ∧
      (singleWord old p).prod=parentProduct old*p := by
  simp [singleWord,parentProduct]

theorem pairWord_history (old : List ℕ) (small large : ℕ) :
    (pairWord old small large).take old.length=old ∧
      (pairWord old small large).length=old.length+2 ∧
      (pairWord old small large).prod=parentProduct old*large*small := by
  simp [pairWord,parentProduct,mul_assoc]

theorem singleWord_primes {rule : SingleRule} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hold : ∀ p ∈ old,p.Prime) {p : Fin (N+1)}
    (hp : p ∈ singleChildren rule N Q old chi) : ∀ q ∈ singleWord old p.val,q.Prime := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hold q hq
  · simp only [List.mem_singleton] at hq
    subst q
    exact (mem_singleChildren.mp hp).1.1

theorem pairWord_primes {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hold : ∀ p ∈ old,p.Prime) {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) :
    ∀ q ∈ pairWord old p.1.val p.2.val,q.Prime := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hold q hq
  · simp only [List.mem_cons,List.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (mem_pairChildren.mp hp).1.2.1
    · exact (mem_pairChildren.mp hp).1.1.1

/-- The literal original edge scalars; no marked or total-rank factorial
is introduced by the arithmetic child constructor. -/
theorem singleEdgeScalar_nonneg (rule : SingleRule) : 0≤singleEdgeScalar rule := by
  cases rule <;> norm_num [singleEdgeScalar]

end
end ImbalancedChen.P2EnhancedLowerPrimeChildCarriers
