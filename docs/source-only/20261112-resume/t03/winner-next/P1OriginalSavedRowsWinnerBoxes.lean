import ImbalancedChen.P1OriginalSavedRowsFinalRead

/-! A common fine mesh certifies the original row, historical third label,
sixth output and winning action. The third label is checked on the box too:
no arithmetic word in it is asked to supply an equal seed as a premise. -/
namespace ImbalancedChen.P1OriginalSavedRowsWinnerBoxes
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P1AffineCertifiedMesh P1AffineCertifiedLookup
open P4AOriginalFourthFifthAffinePrograms
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalFull87DataPolicy (Accepted cap5 licensedCap)
open P4AOriginalFull87FiniteParentCaps (thirdAlphabet originalSeed_mem)
open P4AOriginalLicensedSixthAffineProgram (program valueLookup value_closed_box)
open P4AOriginalLicensedSixthBoxedWitness (decision)
open P4AOriginalSixthActionBank (Action Entry selected endpoint)
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthPlanes (box lowerQ upperQ lift)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalNewFifthCoverage (Schedule)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P1FiniteAffineQuantizerTable (outputAlphabet)
open P4AOriginalFull87HistoryCore (width)
open P1OriginalSavedRowsActualAdmission (row_owner)

private def flag {k : ℕ} (gs : List (Gate k)) : Trace k Bool :=
  guarded gs (.leaf true) (.leaf false)

private theorem flag_true {k : ℕ} (gs : List (Gate k)) (t : Fin k → ℝ) :
    (flag gs).eval t = true ↔ Passed t gs := by
  by_cases h : Passed t gs <;> simp [flag,guarded_eval,Trace.eval,Passed] at h ⊢ <;> simp [h]

private def rowFlag (i : Row) : Trace 6 Bool :=
  flag (halfOpenBox (lift (lowerQ i)) (lift (upperQ i)))

private theorem rowFlag_true (i : Row) (t : Fin 6 → ℝ) :
    (rowFlag i).eval t = true ↔ t ∈ box i := by
  rw [rowFlag,flag_true,passed_halfOpenBox,box,mem_logPrimeBox]

private def thirdFlag (k : ℕ) (j : HistoricalThirdCoarse.Cell k) : Trace 6 Bool :=
  flag (indexed Finset.univ (fun z : Fin 3 =>
    LE (atom (K (logPrimeMeshLo 0 (19/96) k j z))) (atom (X (z.castLE (by decide))))) ++
    indexed Finset.univ (fun z : Fin 3 =>
    LT (atom (X (z.castLE (by decide)))) (atom (K (logPrimeMeshHi 0 (19/96) k j z)))))

private theorem thirdFlag_true (k : ℕ) (j : HistoricalThirdCoarse.Cell k) (t : Fin 6 → ℝ) :
    (thirdFlag k j).eval t = true ↔ firstThree t ∈ logPrimeMeshCell 0 (19/96) k j := by
  simp [thirdFlag,flag_true,firstThree,mem_logPrimeMeshCell,forall_and]

abbrev Seed (d : OriginalData) := {b : ℚ // b ∈ thirdAlphabet d.e d.chi d.m}
abbrev Index (d : OriginalData) := Row ⊕ (HistoricalThirdCoarse.Cell d.m ⊕ (Seed d × Bool))

private def full (p : Program 6) : Spec 6 := ⟨6,p,Function.Embedding.refl _⟩

/-- The extra tests are input labels of the existing archive and third
mesh. They do not alter an action, a level or a Boolean sieve decision. -/
def library (n : ℕ) (d : OriginalData) : Index d → Spec 6
  | .inl i => full (rowFlag i).code
  | .inr (.inl j) => full (thirdFlag d.m j).code
  | .inr (.inr (b,false)) => full (program n d b.val)
  | .inr (.inr (b,true)) => full (decision n d b.val).code

theorem fixed_tag {α : Type*} [Fintype α] (f : Trace 6 α) (m : ℕ)
    {t : Fin 6 → ℝ} (hc : t ∈ covered f.code m)
    (u : Fin 6 → ℝ) (hl : ∀ k,lo m (gridLabel m t) k ≤ u k)
    (hu : ∀ k,u k ≤ hi m (gridLabel m t) k) : f.eval u = f.eval t := by
  obtain ⟨hunit,happ⟩ := (mem_covered_iff _ _ _).mp hc
  have hcert := (mem_approved _ _ _).mp happ
  have hb := mem_logPrimeMeshCell.mp (gridLabel_mem m t hunit)
  exact (f.tag_on_closed_box _ _ _ hcert u hl hu).trans
    (f.tag_on_closed_box _ _ _ hcert t (fun k => (hb k).1) (fun k => (hb k).2.le)).symm

private theorem seed_on_label (d : OriginalData) (N : ℕ) (p : Fin 6 → ℕ) (hist : Owner d N p)
    {j : HistoricalThirdCoarse.Cell d.m} (hj : j ∈ HistoricalThirdCoarse.cells d.e d.chi d.m)
    (ht : firstThree (actualPrimeTupleLog N p) ∈ logPrimeMeshCell 0 (19/96) d.m j) :
    originalSeed d (N:ℝ) (pre p) = HistoricalThirdCoarse.levelExponent (d.e:ℝ)
      (HistoricalThirdCoarse.box d.m j) := by
  rw [← triple_log,← ancestor_three] at ht
  rw [originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hist.active.2,
    HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]

/-- The quantifiers on u precede the arithmetic tuple. A single tag and
one value work on the full closed rectangle, including its closed faces.
All integer histories there have the original physical row and third owner. -/
def FixedRead (n m : ℕ) (d : OriginalData) (i : Row) (t : Fin 6 → ℝ) : Prop :=
  ∃ b ∈ thirdAlphabet d.e d.chi d.m, ∃ v ∈ outputAlphabet n b, ∃ tag : Option Entry,
    t ∈ cell m (gridLabel m t) ∧
    ∀ u : Fin 6 → ℝ, (∀ k,lo m (gridLabel m t) k ≤ u k) →
      (∀ k,u k ≤ hi m (gridLabel m t) k) →
      u ∈ box i ∧ valueLookup n d b m u = (v:ℝ) ∧ (decision n d b).lookup m u = tag ∧
      ∀ N' : ℕ, 1 < N' → ∀ p' : Fin 6 → ℕ, (∀ k,0 < p' k) → actualPrimeTupleLog N' p' = u →
        originalSeed d (N':ℝ) (pre p') = (b:ℝ) ∧ licensedCap n d (N':ℝ) (pre p') = (v:ℝ) ∧
        (tag = none ↔ (v:ℝ) = cap5 n d (N':ℝ) (rosserAncestor 5 (pre p'))) ∧
        ∀ a : Entry, tag = some a →
          Accepted n d (N':ℝ) (pre p') a.val ∧ (v:ℝ) = (rounded n (endpoint a.val u):ℝ) ∧
          P1QuantizedActionLicense.LowerLicense (selected a.val) u (v:ℝ) ∧
          (v:ℝ)+width n ≤ VariableEnvelope.v (∑ j ∈ selected a.val,u j) ∧
          (∀ k : Row, a.val = .saved k → k = i)

private theorem fixed_of_owners (n m : ℕ) (d : OriginalData) (i : Row)
    (owners : ∀ N : ℕ, 1 < N → ∀ p : Fin 6 → ℕ, (∀ j,0 < p j) →
      actualPrimeTupleLog N p ∈ box i → Owner d N p)
    {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ) (hp : ∀ j,0 < p j)
    (ht : actualPrimeTupleLog N p ∈ box i)
    (hmesh : actualPrimeTupleLog N p ∈ accepted (library n d) m) :
    FixedRead n m d i (actualPrimeTupleLog N p) := by
  let t := actualPrimeTupleLog N p
  have ho := owners N hN p hp ht
  obtain ⟨j,hj,hj3⟩ := ho.active.2.2
  rw [ancestor_three,triple_log] at hj3
  obtain ⟨b,hb,hs⟩ := Finset.mem_image.mp (originalSeed_mem d (N:ℝ) (pre p))
  have hv : t ∈ covered (program n d b) m := mem_iInter.mp hmesh (.inr (.inr (⟨b,hb⟩,false)))
  have hw : t ∈ covered (decision n d b).code m := mem_iInter.mp hmesh (.inr (.inr (⟨b,hb⟩,true)))
  have hi' : t ∈ covered (rowFlag i).code m := mem_iInter.mp hmesh (.inl i)
  have hj' : t ∈ covered (thirdFlag d.m j).code m := mem_iInter.mp hmesh (.inr (.inl j))
  obtain ⟨hc,ha⟩ := (mem_covered_iff _ _ _).mp hv
  obtain ⟨v,hv',hval⟩ := value_closed_box n d b m (gridLabel m t) ha
  refine ⟨b,hb,v,hv',(decision n d b).eval t,gridLabel_mem m t hc,?_⟩
  intro u hl hu
  have hrow := (rowFlag_true i u).mp ((fixed_tag _ m hi' u hl hu).trans ((rowFlag_true i t).mpr ht))
  have hcoarse := (thirdFlag_true d.m j u).mp ((fixed_tag _ m hj' u hl hu).trans
    ((thirdFlag_true d.m j t).mpr hj3))
  have htag := (Trace.lookup_exact (decision n d b) m u).trans (fixed_tag _ m hw u hl hu)
  refine ⟨hrow,hval u hl hu,htag,?_⟩
  intro N' hN' p' hp' hu'
  subst u
  have ho' := owners N' hN' p' hp' hrow
  have hseed := (seed_on_label d N' p' ho' hj hcoarse).trans
    ((seed_on_label d N p ho hj hj3).symm.trans hs.symm)
  have hλ : lambda3 d (N':ℝ) (pre p') = (b:ℝ) :=
    (lambda3_ancestor d (N':ℝ) 4 (by decide) (pre p')).symm.trans (ho'.seed.trans hseed)
  have H := P1OriginalSixthWinnerBankRead.read_at_history n m d b (N':ℝ) (pre p') (pre_len p') hλ hseed
  dsimp only at H
  rw [pre_log] at H
  have hvact := H.1.symm.trans (hval _ hl hu)
  rw [htag,hvact] at H
  refine ⟨hseed,hvact,H.2.1,?_⟩
  intro win hwin
  obtain ⟨_,hacc,hvwin,hgate,hdebit⟩ := H.2.2 win hwin
  refine ⟨hacc,hvwin,hgate,hdebit,?_⟩
  intro k hk
  rw [hk] at hacc
  have hsrc := hacc.1.2.1
  rw [pre_log] at hsrc
  by_contra hne
  exact Set.disjoint_left.mp (P4AOriginalSavedSixthIntegral.box_disjoint hne)
    ((P4AOriginalSavedSixthSourceGates.source_iff k _).mp hsrc).1 hrow

theorem original_fixed_box (n m : ℕ) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a : ℝ} (ha : a ≤ 1/100) (i : Row) {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ)
    (hp : ∀ j,0 < p j) (ht : actualPrimeTupleLog N p ∈ box i)
    (hm : actualPrimeTupleLog N p ∈ accepted (library n (P4AOriginalCompleteSixthChronology.data e q a)) m) :
    FixedRead n m (P4AOriginalCompleteSixthChronology.data e q a) i (actualPrimeTupleLog N p) :=
  fixed_of_owners n m _ i (fun _ hN' p' hp' ht' => (row_owner i hs ha hN' p' hp' ht').1) hN p hp ht hm

theorem union_fixed_box (n m : ℕ) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a : ℝ} (ha : a ≤ 1/100) (i : Row) {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ)
    (hp : ∀ j,0 < p j) (ht : actualPrimeTupleLog N p ∈ box i)
    (hm : actualPrimeTupleLog N p ∈ accepted (library n (bank e q a)) m) :
    FixedRead n m (bank e q a) i (actualPrimeTupleLog N p) :=
  fixed_of_owners n m _ i (fun _ hN' p' hp' ht' => (row_owner i hs ha hN' p' hp' ht').2) hN p hp ht hm

end
end ImbalancedChen.P1OriginalSavedRowsWinnerBoxes
