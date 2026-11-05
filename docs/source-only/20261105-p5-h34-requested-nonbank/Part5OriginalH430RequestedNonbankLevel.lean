import ImbalancedChen.Part5OriginalH430RequestedNonbankSupply

/-!
The actual (not arbitrarily labelled) selected nonbank generation slices.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is a pre-N uniform estimate for Buchstab feedback requests AND an
exact retained-cell identity. Each index is the original level-list
position and each mark is the original edge-weight product. It proves
neither source-count completeness nor the full CLOSED-CELL induction.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedNonbankLevel

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPrimeChildCarriers P2OriginalChildPhysicalNormalization
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankSupply
open Part5OriginalBuchstabActualRowLimits Part5OriginalBuchstabImmutable430Budget
open Part5OriginalH430FrozenRootRefinement

/-- Reuse the original level-list positions: identical integer products
at different positions retain their independent contributions. -/
def selectedBuchstabLevel (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ i : Fin 200, Selected g.val (levelOccurrence l).current i .buchstab)

def selectedRetainedLevel (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : Finset (Index N n root tau p g) :=
  Finset.univ.filter (fun l =>
    ∃ i : Fin 200, Selected g.val (levelOccurrence l).current i .retained)

def buchstabLevelTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l * thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old)

def buchstabLevelError (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l * (∑ b : RowAtom,
      |edgeRow (rootQ N n root tau p) (levelOccurrence l).current
          (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) b -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          integralRow (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical b| *
       |oldAtomValue (precedingH g) (precedingh g) b|)

def buchstabLevelRow (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (b : RowAtom) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l * edgeRow (rootQ N n root tau p) (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) b

def retainedLevelValue (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedRetainedLevel N n root tau p g,
    levelMark l * edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

/-- Choice and request-cell ownership are unique at the current generation,
regardless of scalar vs specified-cell read mode. -/
theorem selected_choice_unique {g : ℕ} {r : Request} {i j : Fin 200}
    {c d : Choice} (hc : Selected g r i c) (hd : Selected g r j d) : c = d := by
  have hij : i = j := Option.some.inj (hc.1.symm.trans hd.1)
  subst j
  exact hc.2.symm.trans hd.2

theorem buchstab_retained_disjoint (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    Disjoint (selectedBuchstabLevel N n root tau p g)
      (selectedRetainedLevel N n root tau p g) := by
  apply Finset.disjoint_left.mpr
  intro l hb hr
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hb).2
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hr).2
  have h : (Choice.buchstab : Choice) = .retained := selected_choice_unique hi hj
  cases h

/-- Each parent at a selected retention level reads its real OLD owned
cell; a scalar owner is not recalculated using the old table. -/
theorem retained_level_exact (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    retainedLevelValue N n root tau p g =
      ∑ l ∈ selectedRetainedLevel N n root tau p g,
        levelMark l * thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
        requestValue (iterate (g.val+1)) (levelOccurrence l).current := by
  unfold retainedLevelValue
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  rw [requested_retained_children_value hi, requested_retained_value hi]
  ring

/-- One pre-N threshold for all requested Buchstab generations, root
kinds and precision. A zero level Theta yields zero absolute error AND
zero coefficients; no positivity of the denominator is presumed. -/
theorem uniform_level_buchstab_supply {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
      physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
      buchstabLevelError N n root tau p g ≤
        epsilon*buchstabLevelTheta N n root tau p g ∧
      (∀ b, 0 ≤ buchstabLevelRow N n root tau p g b) ∧
      (∑ b : RowAtom, buchstabLevelRow N n root tau p g b) ≤
        5*buchstabLevelTheta N n root tau p g ∧
      (buchstabLevelTheta N n root tau p g = 0 →
        buchstabLevelError N n root tau p g = 0 ∧
        ∀ b, buchstabLevelRow N n root tau p g b = 0) := by
  obtain ⟨T,hTlo,hT⟩ := uniform_requested_buchstab_local he
  refine ⟨T,hTlo,?_⟩
  intro N hN n root tau ht ht' hn p hp hb g
  let Q := rootQ N n root tau p
  let S := selectedBuchstabLevel N n root tau p g
  have hlocal (l : Index N n root tau p g) (hl : l ∈ S) :
      (∑ b : RowAtom,
        |edgeRow Q (levelOccurrence l).current
           (children N Q g.val (levelOccurrence l).current) b -
           thetaAtom N Q (parentProduct (levelOccurrence l).current.old) *
             integralRow (levelOccurrence l).current.node.upper
               (levelOccurrence l).current.node.physical b| *
          |oldAtomValue (precedingH g) (precedingh g) b|) ≤
          epsilon*thetaAtom N Q (parentProduct (levelOccurrence l).current.old) ∧
      (∀ b, 0 ≤ edgeRow Q (levelOccurrence l).current
        (children N Q g.val (levelOccurrence l).current) b) ∧
      (∑ b : RowAtom, edgeRow Q (levelOccurrence l).current
        (children N Q g.val (levelOccurrence l).current) b) ≤
          5*thetaAtom N Q (parentProduct (levelOccurrence l).current.old) := by
    have ho := (levelOccurrence_source l).1
    have hc := rootHistory_coherent (by omega : 1 < N) ht ht' hn hp hb ho
    have hs := rootHistory_support (by omega : 1 < N) ht ht' hn hp hb ho
    obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
    exact hT N hN Q (levelOccurrence l).current g i hc hi hs.2.2.1
  have herr : buchstabLevelError N n root tau p g ≤
      epsilon*buchstabLevelTheta N n root tau p g := by
    calc
      _ ≤ ∑ l ∈ S, levelMark l *
          (epsilon*thetaAtom N Q (parentProduct (levelOccurrence l).current.old)) :=
        Finset.sum_le_sum (fun l hl =>
          mul_le_mul_of_nonneg_left (hlocal l hl).1 (mark_pos _).le)
      _ = _ := by
        unfold buchstabLevelTheta
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  have hrow (b : RowAtom) : 0 ≤ buchstabLevelRow N n root tau p g b :=
    Finset.sum_nonneg (fun l hl => mul_nonneg (mark_pos _).le ((hlocal l hl).2.1 b))
  have hmass : (∑ b : RowAtom, buchstabLevelRow N n root tau p g b) ≤
      5*buchstabLevelTheta N n root tau p g := by
    unfold buchstabLevelRow
    rw [Finset.sum_comm]
    calc
      _ = ∑ l ∈ S, levelMark l * ∑ b : RowAtom,
          edgeRow Q (levelOccurrence l).current
            (children N Q g.val (levelOccurrence l).current) b := by
        apply Finset.sum_congr rfl
        intro l _
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ l ∈ S, levelMark l *
          (5*thetaAtom N Q (parentProduct (levelOccurrence l).current.old)) :=
        Finset.sum_le_sum (fun l hl =>
          mul_le_mul_of_nonneg_left (hlocal l hl).2.2 (mark_pos _).le)
      _ = _ := by
        unfold buchstabLevelTheta
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  refine ⟨herr,hrow,hmass,?_⟩
  intro hz
  constructor
  · exact le_antisymm (by simpa only [hz,mul_zero] using herr)
      (Finset.sum_nonneg (fun l _ => mul_nonneg (mark_pos _).le
        (Finset.sum_nonneg (fun b _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))))
  · intro b
    have hb := Finset.single_le_sum (fun c _ => hrow c) (Finset.mem_univ b)
    exact le_antisymm (by simpa only [hz,mul_zero] using hb.trans hmass) (hrow b)

end
end ImbalancedChen.Part5OriginalH430RequestedNonbankLevel
