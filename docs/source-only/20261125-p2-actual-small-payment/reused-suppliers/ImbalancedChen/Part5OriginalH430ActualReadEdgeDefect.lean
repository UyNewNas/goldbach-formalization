import ImbalancedChen.Part5OriginalH430AllActionOccurrenceSource
import ImbalancedChen.Part5OriginalH430RequestedNonbankSupply

/-!
P5.6 / h34. Compare the genuine g+1 request read with the selected
old-table edge mass at the SAME actual generated level list positions.
Retention cancels after the exact parent Theta scaling. Buchstab has
its original integer suffix minus strict prime sum, not an assumed
identity. Selected bank reads have only their original candidate upper.
This remains source-only; it is NOT a count-source licence or a full
closed-cell induction. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/
namespace ImbalancedChen.Part5OriginalH430ActualReadEdgeDefect

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BankSlotTargets Part5OriginalH430FixedReadDictionary
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430RequestedNonbankSupply

def readTerm (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) *
    requestValue (iterate (g.val+1)) (levelOccurrence l).current

def childTerm (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  edgeValue (rootQ N n root tau p) (iterate g.val)
    (levelOccurrence l).current
    (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

def levelDefect (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  levelMark l * (readTerm N n root tau p g l -
    childTerm N n root tau p g l)

def levelReadMass (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l * readTerm N n root tau p g l

def levelChildMass (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l * childTerm N n root tau p g l

theorem level_mass_difference (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g =
      ∑ l : Index N n root tau p g, levelDefect N n root tau p g l := by
  unfold levelReadMass levelChildMass levelDefect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The true unresolved scalar request supplies neither a read nor
selected edges, so dropping it loses exactly zero mass. -/
theorem unresolved_request_gap_zero (N g : ℕ) (Q : ℝ)
    (r : Request) (hr : resolve (g+1) r = none) :
    thetaAtom N Q (parentProduct r.old) *
        requestValue (iterate (g+1)) r -
      edgeValue Q (iterate g) r (children N Q g r) = 0 := by
  obtain ⟨hc,hv⟩ := exterior_children_empty hr
  simp [hv,hc,edgeValue]

theorem unresolved_level_defect_zero (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hr : resolve (g.val+1) (levelOccurrence l).current = none) :
    levelDefect N n root tau p g l = 0 := by
  unfold levelDefect readTerm childTerm
  rw [unresolved_request_gap_zero N g.val (rootQ N n root tau p)
    (levelOccurrence l).current hr]
  ring

/-- On a retained winner the new rounded cell is EXACTLY the
specified old cell. The original retained edge has the same Theta. -/
theorem retained_request_gap_zero {N g : ℕ} {Q : ℝ}
    {r : Request} {i : Fin 200}
    (hs : Selected g r i .retained) :
    thetaAtom N Q (parentProduct r.old) *
        requestValue (iterate (g+1)) r -
      edgeValue Q (iterate g) r (children N Q g r) = 0 := by
  rw [requested_retained_value hs, requested_retained_children_value hs]
  ring

theorem retained_level_defect_zero (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hl : l ∈ retainedLevel N n root tau p g) :
    levelDefect N n root tau p g l = 0 := by
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  unfold levelDefect readTerm childTerm
  rw [retained_request_gap_zero (N := N)
    (Q := rootQ N n root tau p) (g := g.val) hi]
  ring

theorem retained_level_total_zero (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelDefect N n root tau p g l) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  exact retained_level_defect_zero N n root tau p g l hl

/-- Apply the actual resolver's action partition to the SIGNED
difference, at the real LevelIndex (which retains multiplicities). -/
theorem level_defect_partition (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l : Index N n root tau p g, levelDefect N n root tau p g l) =
    (∑ l ∈ retainedLevel N n root tau p g,
      levelDefect N n root tau p g l) +
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelDefect N n root tau p g l) +
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        levelDefect N n root tau p g l) := by
  classical
  calc
    (∑ l : Index N n root tau p g, levelDefect N n root tau p g l) =
        ∑ l : Index N n root tau p g,
          if ∃ i : Fin 200,
              resolve (g.val+1) (levelOccurrence l).current = some i
          then levelDefect N n root tau p g l else 0 := by
            apply Finset.sum_congr rfl
            intro l _
            by_cases hactive : ∃ i : Fin 200,
                resolve (g.val+1) (levelOccurrence l).current = some i
            · simp [hactive]
            · have hnone :
                  resolve (g.val+1) (levelOccurrence l).current = none := by
                cases he : resolve (g.val+1) (levelOccurrence l).current with
                | none => rfl
                | some i => exact (hactive ⟨i,he⟩).elim
              simp [hactive,unresolved_level_defect_zero N n root tau p g l hnone]
    _ = _ := (level_action_partition N n root tau p g
      (levelDefect N n root tau p g)).symm

/-- Retention cancels exactly, leaving only REAL Buchstab and bank
discrepancies. The equation is not an arithmetic count identity. -/
theorem level_defect_nonretained (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g =
      (∑ l ∈ buchstabLevel N n root tau p g,
        levelDefect N n root tau p g l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          levelDefect N n root tau p g l) := by
  rw [level_mass_difference,level_defect_partition,retained_level_total_zero]
  ring

/-- Explicit integer-suffix MINUS original strict prime carrier
with previous table, original parent Q, polarity and ceiling. -/
theorem selected_buchstab_gap_exact {N g : ℕ} {Q : ℝ}
    {r : Request} {i : Fin 200}
    (hc : Coherent N Q r) (hs : Selected g r i .buchstab) :
    thetaAtom N Q (parentProduct r.old) *
        requestValue (iterate (g+1)) r -
      edgeValue Q (iterate g) r (children N Q g r) =
      thetaAtom N Q (parentProduct r.old) *
        ((buchstabValue (iterate g) r.node.upper i : ℝ)/(2:ℝ)^80) -
      ∑ q ∈ singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling,
        thetaAtom N Q (parentProduct r.old*q.val) *
          tableFunction r.node.upper
            (if r.node.upper then iterate g false else iterate g true)
            (buchstabArgument Q r.old q.val) := by
  rw [requested_buchstab_value hs, requested_buchstab_children_value hc hs]

/-- On an ACTUAL Buchstab generation position, its own cell index,
Coherent instance and exact unpaid strict-prime gap are produced. -/
theorem buchstab_level_gap_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (l : Index N n root tau p g)
    (hl : l ∈ buchstabLevel N n root tau p g) :
    ∃ i : Fin 200,
      Selected g.val (levelOccurrence l).current i .buchstab ∧
      levelDefect N n root tau p g l =
        levelMark l *
          (thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
              ((buchstabValue (iterate g.val)
                (levelOccurrence l).current.node.upper i : ℝ)/(2:ℝ)^80) -
           ∑ q ∈ singleChildren
             (.buchstab (levelOccurrence l).current.node.upper
               (levelOccurrence l).current.node.physical.argument)
             N (rootQ N n root tau p) (levelOccurrence l).current.old
               (levelOccurrence l).current.node.physical.ceiling,
             thetaAtom N (rootQ N n root tau p)
               (parentProduct (levelOccurrence l).current.old*q.val) *
               tableFunction (levelOccurrence l).current.node.upper
                 (if (levelOccurrence l).current.node.upper then iterate g.val false
                  else iterate g.val true)
                 (buchstabArgument (rootQ N n root tau p)
                   (levelOccurrence l).current.old q.val)) := by
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  refine ⟨i,hi,?_⟩
  have hc := rootHistory_coherent hN ht ht' hn hp hband (levelOccurrence_source l).1
  unfold levelDefect readTerm childTerm
  rw [selected_buchstab_gap_exact hc hi]

/-- Bank envelope keeps original base/fixed/feedback (NOT a new
count estimate) and the actual physical child sum. -/
def bankCandidateGap (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) : ℝ :=
  levelMark l *
    (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
       (baseValue a + fixedValue (iterate g.val true) a +
         feedbackValue (iterate g.val) a) -
     childTerm N n root tau p g l)

theorem bank_level_defect_le_candidate (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (a : Original106Action)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    levelDefect N n root tau p g l ≤
      bankCandidateGap N n root tau p g a l := by
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  have hs := rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1
  have hw := hs.1
  have htheta : 0 ≤ thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hc := selected_bank_candidate_upper hi
  unfold levelDefect readTerm childTerm bankCandidateGap
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hc htheta) _)
    (mark_pos _).le

theorem bank_defect_sum_le (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        levelDefect N n root tau p g l) ≤
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        bankCandidateGap N n root tau p g a l) := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l hl
  exact bank_level_defect_le_candidate N n root tau p g a hN ht ht'
    hn hp hband l hl

/-- Actual one-step inequality with retention fully cancelled and a
literal UNPAID Buchstab integer-suffix/prime-sum difference. -/
theorem actual_one_generation_candidate_upper (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g ≤
      (∑ l ∈ buchstabLevel N n root tau p g,
        levelDefect N n root tau p g l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          bankCandidateGap N n root tau p g a l) := by
  rw [level_defect_nonretained]
  exact add_le_add le_rfl
    (bank_defect_sum_le N n root tau p g hN ht ht' hn hp hband)

end
end ImbalancedChen.Part5OriginalH430ActualReadEdgeDefect
