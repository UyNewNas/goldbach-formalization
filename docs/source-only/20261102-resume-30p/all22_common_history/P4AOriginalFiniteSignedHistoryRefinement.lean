import ImbalancedChen.P4AOriginalRankThreeRestorationSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An exact finite common refinement of the held constructor's SIGNED sources.
The finite list of native history tests is constructed from OriginalData
before N: all third mesh owners (also unselected owners), the original
fourth/fifth row tests and the actual re-tested eleven sixth sources.
Each test reads only its own ancestor; a not-yet-reached rank is `none`.
No child-wall projection is used to choose an earlier ancestor decision.

The same finite signature space partitions each actual occurrence list.
There is no conversion to a set of states, hence no loss of multiplicity.
The new restoration source, current third frontier, original fourth/fifth
gains, and sixth/eighth changes are then put into one exact same-rho ledger.

This is a finite source reindexing, not a buffered approximation theorem.
It supplies no whole-history margin or all22/87 source association.  The
eighth term remains the held constructor's literal sourceChange, and the
full ideal87 policy is deliberately not defined here.
-/

namespace ImbalancedChen.P4AOriginalFiniteSignedHistoryRefinement
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalCausalHistory P4AOriginalRankThreeRestorationSource
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P5OriginalCommonFourthSourceNavigation P5OriginalCommonFourthFallbackExcision
open P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

structure PrefixTest where
  rank : ℕ
  test : ℝ → List ℕ → Bool

/-- None retains the distinction between a false test and a rank that
has not been reached.  Neither case removes the source occurrence. -/
def PrefixTest.read (c : PrefixTest) (N : ℝ) (pre : List ℕ) : Option Bool :=
  if c.rank ≤ pre.length then some (c.test N (rosserAncestor c.rank pre)) else none

theorem read_later_history (c : PrefixTest) (N : ℝ) (later pre : List ℕ)
    (hc : c.rank ≤ pre.length) : c.read N (later ++ pre) = c.read N pre := by
  have hl : c.rank ≤ (later ++ pre).length := by simp only [List.length_append]; omega
  simp only [PrefixTest.read, if_pos hc, if_pos hl, rosserAncestor_append _ _ _ hc]

/-- The finite native tests, with their actual selected/fallback boundaries.
In particular the mesh bank is UNIV, not HistoricalThirdCoarse.cells. -/
def nativeTests (d : OriginalData) : List PrefixTest :=
  [⟨1, fun N pre => old3 d N false pre⟩,
   ⟨2, fun N pre => decide (secondGuard N pre)⟩,
   ⟨3, fun N pre => decide (selectedThird d N pre)⟩,
   ⟨3, fun N pre => decide (thirdGuard N pre)⟩,
   ⟨3, fun N pre => old3 d N false pre⟩,
   ⟨3, fun N pre => secondStage d N false pre⟩,
   ⟨3, fun N pre => decide ((pre.headD 0 : ℝ) < N ^ d.omega)⟩] ++
  ((Finset.univ : Finset (HistoricalThirdCoarse.Cell d.m)).toList.map (fun j =>
    ⟨3, fun N pre => decide (primeHistoryLogCoordinates N 3 pre ∈
      logPrimeMeshCell 0 (19 / 96) d.m j)⟩)) ++
  (d.rows4.toList.map (fun r =>
    ⟨4, fun N pre => decide (P1OriginalVariableFourthContinuation.producerEligible
      d.licensed4 r (primeHistoryLogCoordinates N 4 pre))⟩)) ++
  (d.rows5.toList.map (fun r =>
    ⟨5, fun N pre => decide (P1OriginalVariableFifthContinuation.eligible
      d.e d.chi d.m d.omega d.J5 r (primeHistoryLogCoordinates N 5 pre))⟩)) ++
  (Certificates.P2OriginalSixthElevenLogSemantics.allCells.map (fun c =>
    ⟨6, fun N pre => decide (eligibleSixth d N c pre)⟩))

abbrev Signature (bank : List PrefixTest) := Fin bank.length → Option Bool

def signature (bank : List PrefixTest) (N : ℝ) (pre : List ℕ) : Signature bank :=
  fun i => (bank.get i).read N pre

theorem signature_coordinate_causal (bank : List PrefixTest) (i : Fin bank.length)
    (N : ℝ) (later pre : List ℕ) (hi : (bank.get i).rank ≤ pre.length) :
    signature bank N (later ++ pre) i = signature bank N pre i :=
  read_later_history (bank.get i) N later pre hi

/-- Literal list fibers retain repeated occurrences, signs and masses. -/
def refinedSum {α : Type*} (bank : List PrefixTest) (N : ℝ)
    (xs : List α) (prefix : α → List ℕ) (value : α → ℝ) : ℝ :=
  ∑ q : Signature bank,
    ((xs.filter (fun x => decide (signature bank N (prefix x) = q))).map value).sum

/-- The common partition is proved exact; no cover or source equality is
an input.  False, equality, inherit and unselected fibers are retained. -/
theorem refinedSum_eq {α : Type*} (bank : List PrefixTest) (N : ℝ)
    (xs : List α) (prefix : α → List ℕ) (value : α → ℝ) :
    refinedSum bank N xs prefix value = (xs.map value).sum := by
  induction xs with
  | nil => simp [refinedSum]
  | cons x xs ih =>
      have hrow (q : Signature bank) :
          (((x :: xs).filter (fun a => decide (signature bank N (prefix a) = q))).map value).sum =
            (if signature bank N (prefix x) = q then value x else 0) +
              ((xs.filter (fun a => decide (signature bank N (prefix a) = q))).map value).sum := by
        by_cases hq : signature bank N (prefix x) = q <;> simp [hq]
      calc
        _ = ∑ q : Signature bank,
            ((if signature bank N (prefix x) = q then value x else 0) +
              ((xs.filter (fun a => decide (signature bank N (prefix a) = q))).map value).sum) := by
          exact Finset.sum_congr rfl (fun q _ => hrow q)
        _ = value x + refinedSum bank N xs prefix value := by
          rw [Finset.sum_add_distrib]
          simp only [refinedSum, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        _ = ((x :: xs).map value).sum := by rw [ih]; rfl

def refinedRoot (bank : List PrefixTest) (N : ℝ) (P : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  refinedSum bank N (firstExitRootLeaves P h carrier) (fun s => s.selected)
    (fun s => s.value * T s.positive s.selected)

theorem refinedRoot_eq (bank : List PrefixTest) (N : ℝ) (P : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    refinedRoot bank N P h T carrier = signedTest P h T [] true 1 carrier := by
  rw [refinedRoot, refinedSum_eq]
  exact (signedTest_eq_leaves P h T [] carrier true 1).symm

def refinedSecond (bank : List PrefixTest) (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  refinedSum bank N (candidates d N h carrier) (fun s => s.selectedPrefix)
    (fun s => retainedTerm d N h T s + restoredTerm d N h T s)

theorem refinedSecond_eq (bank : List PrefixTest) (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    refinedSecond bank d N h T carrier = secondChange d N h T carrier := by
  rw [refinedSecond, refinedSum_eq]
  exact (secondChange_eq_retained_and_restored d he N hN h T carrier).symm

def refinedThird (bank : List PrefixTest) (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  refinedSum bank N (firstExitDepthFrontier 3 (secondStage d N) h [] true 1 carrier)
    (fun s => s.selectedPrefix) (fun s =>
      signedTest (common3 d N) h T s.selectedPrefix s.positive s.mass s.remaining -
        signedTest (secondStage d N) h T s.selectedPrefix s.positive s.mass s.remaining)

theorem refinedThird_eq (bank : List PrefixTest) (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    refinedThird bank d N h T carrier = thirdChange d N h T carrier := by
  exact refinedSum_eq bank N _ _ _

def refinedAction (bank : List PrefixTest) (d : OriginalData) (a : Action)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  refinedSum bank (N : ℝ)
    (firstExitDepthFrontier (actionRank a) (stagePolicy d (N : ℝ) (parentStage a))
      (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z))
    (fun s => s.selectedPrefix) (fun s =>
      signedTest (replacement d (N : ℝ) a) (fun _ => 1)
        (terminal N cap w L G) s.selectedPrefix s.positive s.mass s.remaining -
      signedTest (stagePolicy d (N : ℝ) (parentStage a)) (fun _ => 1)
        (terminal N cap w L G) s.selectedPrefix s.positive s.mass s.remaining)

theorem refinedAction_eq (bank : List PrefixTest) (d : OriginalData) (a : Action)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    refinedAction bank d a N cap w z L G = sourceChange d a N cap w z L G := by
  exact refinedSum_eq bank (N : ℝ) _ _ _

/-- New minus CURRENT parent is unchanged by the one finite refinement. -/
theorem refinedAction_current_parent (bank : List PrefixTest) (d : OriginalData)
    (a : Action) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    refinedAction bank d a N cap w z L G =
      source d (nextStage a) N cap w z L G - source d (parentStage a) N cap w z L G := by
  rw [refinedAction_eq]
  exact (source_next_sub_current d a N cap w z L G).symm

/-- Every source uses this single bank fixed before N.  The equality is
pointwise for arbitrary terminal tests, not just density asymptotics. -/
theorem one_preN_native_refinement (d : OriginalData) :
    ∃ bank : List PrefixTest, bank = nativeTests d ∧
      ∀ N : ℝ, ∀ P : Bool → List ℕ → Bool, ∀ h : ℕ → ℝ,
        ∀ T : Bool → List ℕ → ℝ, ∀ carrier : List ℕ,
        refinedRoot bank N P h T carrier = signedTest P h T [] true 1 carrier := by
  exact ⟨nativeTests d, rfl, fun N P h T carrier => refinedRoot_eq _ N P h T carrier⟩

/-- The already proved historical gains survive common refinement with
their signs and occurrences intact.  No new gain is inferred from a bound. -/
theorem refined_archive_fifth_gain_preserved (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    let bank := nativeTests s.data
    refinedRoot bank N (policy4 s.data N) h T carrier -
        refinedRoot bank N (policy5 s.data N) h T carrier =
      refinedRoot bank N (original4 s.data N) h T carrier -
        refinedRoot bank N (original5 s.data N) h T carrier := by
  dsimp only
  simp only [refinedRoot_eq]
  exact archive_fifth_signed_gain_preserved s hg N hN h T carrier

/-- Actual same-rho ledger, including the newly explicit restoration
source.  Original fourth/fifth gains are charged once; the final two
sources retain their existing held-constructor identity and scope. -/
theorem common_refined_original_gain_telescope (s : ArchiveSchedule)
    (hg : FourthGeometry s.data) (he : 0 ≤ (s.e : ℝ)) (hemax : (s.e : ℝ) ≤ 11 / 64000)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (w z L : ℝ) (G : ℕ → ℝ) :
    let bank := nativeTests s.data
    let T := attachedLeafTest N cap 1 w L G
    let carrier := roughPrimeUniverse N cap w z
    (∑ q ∈ moduli s.data N cap w z,
      P5OriginalCommonRefinedConstructor.rho s.data N cap w z L q * G q) =
      refinedRoot bank (N : ℝ) (old3 s.data (N : ℝ)) (fun _ => 1) T carrier +
        refinedSecond bank s.data (N : ℝ) (fun _ => 1) T carrier +
        refinedThird bank s.data (N : ℝ) (fun _ => 1) T carrier -
        (refinedRoot bank (N : ℝ) (old3 s.data (N : ℝ)) (fun _ => 1) T carrier -
          refinedRoot bank (N : ℝ) (original4 s.data (N : ℝ)) (fun _ => 1) T carrier) -
        (refinedRoot bank (N : ℝ) (original4 s.data (N : ℝ)) (fun _ => 1) T carrier -
          refinedRoot bank (N : ℝ) (original5 s.data (N : ℝ)) (fun _ => 1) T carrier) +
        refinedAction bank s.data .sixth N cap w z L G +
        refinedAction bank s.data .eighth N cap w z L G := by
  dsimp only
  simp only [refinedRoot_eq, refinedSecond_eq _ s.data he (N : ℝ) hN,
    refinedThird_eq, refinedAction_eq]
  exact held_final_source_with_original_gains s hg he hemax N cap hN w z L G

end
end ImbalancedChen.P4AOriginalFiniteSignedHistoryRefinement
