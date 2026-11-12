import ImbalancedChen.P1OriginalSavedRowsWinnerBoxes
import ImbalancedChen.P1OriginalSavedRowsRawWinner

/-! The original raw winner and the two actual licensed reads are certified
on one pre-target mesh. The raw winner has its own chronology and code.
Arithmetic fallback uses the exact original predicates on every face. -/
namespace ImbalancedChen.P1OriginalSavedRowsWinnerSchedule
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory
open P1AffineCertifiedMesh P1AffineCertifiedLookup P1AffineTaggedDecision
open P4AOriginalSavedSixthPlanes (box)
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalFull87HistoryCore (width width_tendsto)
open P4AOriginalSixthActionBank (Entry selected endpoint)
open P4AOriginalNewFifthCoverage (Schedule)
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalFull87FiniteParentCaps (thirdAlphabet originalSeed_mem)
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalSavedRowsWinnerBoxes (Index Seed FixedRead fixed_tag)
open P1OriginalSavedRowsActualAdmission (row_owner)
open P1GuardFrozenFiniteCapAlgebra (rounded)

abbrev old := P4AOriginalCompleteSixthChronology.data
abbrev Key (e : ℚ) (q : ℕ) (a : ℝ) :=
  Index (old e q a) ⊕ (Index (bank e q a) ⊕ Seed (old e q a))

def joint (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) : Key e q a → Spec 6
  | .inl i => P1OriginalSavedRowsWinnerBoxes.library n (old e q a) i
  | .inr (.inl i) => P1OriginalSavedRowsWinnerBoxes.library n (bank e q a) i
  | .inr (.inr b) => ⟨6,(P1OriginalSavedRowsRawWinner.trace (old e q a) b.val).code,
      Function.Embedding.refl _⟩

def archived : Set (Fin 6 → ℝ) := ⋃ i : Row, box i

theorem archived_subset : archived ⊆ Icc (fun _ => (0:ℝ)) (fun _ => 1) := by
  intro t ht
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  constructor
  · intro j
    exact (by norm_num : (0:ℝ) ≤ 1/50).trans (P4AOriginalSavedSixthPrimeMean.bounds i hi j).1
  · intro j
    exact (P4AOriginalSavedSixthPrimeMean.bounds i hi j).2.le.trans (by norm_num)

/-- Raw tag on the actual P1 parent. Some tags name a maximizing archived
action, none is genuine inheritance. These are separate from rounded
licensed winners on the same fine rectangle. -/
def RawRead (m : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (t : Fin 6 → ℝ) : Prop :=
  ∃ b ∈ thirdAlphabet (old e q a).e (old e q a).chi (old e q a).m, ∃ tag : Option Entry,
    ∀ u : Fin 6 → ℝ, (∀ k,lo m (gridLabel m t) k ≤ u k) →
      (∀ k,u k ≤ hi m (gridLabel m t) k) →
      (P1OriginalSavedRowsRawWinner.trace (old e q a) b).lookup m u = tag ∧
      ∀ N : ℕ, 1 < N → ∀ p : Fin 6 → ℕ, (∀ k,0 < p k) → actualPrimeTupleLog N p = u →
        (tag = none ↔ P4AOriginalCompleteSixthChronology.currentSixthExponent e q a (N:ℝ) (pre p) =
          P4AOriginalCompleteSixthChronology.fifth e q a (N:ℝ) (pre p)) ∧
        ∀ win : Entry, tag = some win →
          P4AOriginalCompleteSixthChronology.fifth e q a (N:ℝ) (pre p) <
            P4AOriginalCompleteSixthChronology.currentSixthExponent e q a (N:ℝ) (pre p) ∧
          P4AOriginalSixthActionBank.ActualEligible e q a (N:ℝ) (pre p) win.val ∧
          P4AOriginalCompleteSixthChronology.currentSixthExponent e q a (N:ℝ) (pre p) = endpoint win.val u

theorem three_actual_reads (n m : ℕ) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a : ℝ} (ha : a ≤ 1/100) (i : Row) {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ)
    (hp : ∀ j,0 < p j) (ht : actualPrimeTupleLog N p ∈ box i)
    (hm : actualPrimeTupleLog N p ∈ accepted (joint n e q a) m) :
    FixedRead n m (old e q a) i (actualPrimeTupleLog N p) ∧
    FixedRead n m (bank e q a) i (actualPrimeTupleLog N p) ∧
    RawRead m e q a (actualPrimeTupleLog N p) := by
  let t := actualPrimeTupleLog N p
  have hold := P1OriginalSavedRowsWinnerBoxes.original_fixed_box n m hs ha i hN p hp ht
    (mem_iInter.mpr fun k => mem_iInter.mp hm (.inl k))
  have hnew := P1OriginalSavedRowsWinnerBoxes.union_fixed_box n m hs ha i hN p hp ht
    (mem_iInter.mpr fun k => mem_iInter.mp hm (.inr (.inl k)))
  refine ⟨hold,hnew,?_⟩
  obtain ⟨b,hb,v,hv,tag,hcell,H⟩ := hold
  let raw := P1OriginalSavedRowsRawWinner.trace (old e q a) b
  have hc : t ∈ covered raw.code m := mem_iInter.mp hm (.inr (.inr ⟨b,hb⟩))
  refine ⟨b,hb,raw.eval t,?_⟩
  intro u hl hu
  have htag := fixed_tag raw m hc u hl hu
  refine ⟨(Trace.lookup_exact raw m u).trans htag,?_⟩
  intro N' hN' p' hp' htu
  subst u
  have hread := H _ hl hu
  have hist := (row_owner i hs ha hN' p' hp' hread.1).1
  have hseed := (hread.2.2.2 N' hN' p' hp' rfl).1
  have hroot : lambda3 (old e q a) (N':ℝ) (pre p') = (b:ℝ) :=
    (lambda3_ancestor _ (N':ℝ) 4 (by decide) (pre p')).symm.trans (hist.seed.trans hseed)
  have he := P1OriginalSavedRowsRawWinner.actual_read e q a (N':ℝ) b (pre p') (pre_len p') hroot
  dsimp only at he
  rw [pre_log,htag] at he
  exact he

/-- On a wall or rejected fine box the final tree can still be read. The
seed comes from its own third label, and the equality case is inherited. -/
theorem exact_final_lookup (n m : ℕ) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a ω : ℝ} (ha : a ≤ 1/100) (hw : ω ≤ a) (i : Row) {N : ℕ} (hN : 1 < N)
    (p : Fin 6 → ℕ) (hp : ∀ j,0 < p j) (ht : actualPrimeTupleLog N p ∈ box i) :
    let d := bank e q a
    let h := pre p
    let t := actualPrimeTupleLog N p
    let R := P4AOriginalOrderedThirdFullPolicy.current d ω (N:ℝ) h
    let value := P4AOriginalOrderedThirdFullPolicy.cap6 R d (N:ℝ) n h
    ∃ b ∈ thirdAlphabet d.e d.chi d.m, originalSeed d (N:ℝ) h = (b:ℝ) ∧
      P4AOriginalLicensedSixthAffineProgram.valueLookup n d b m t = value ∧
      ((P4AOriginalLicensedSixthBoxedWitness.decision n d b).lookup m t = none ↔
        value = P4AOriginalFull87DataPolicy.cap5 n d (N:ℝ) (rosserAncestor 5 h)) ∧
      ∀ win : Entry, (P4AOriginalLicensedSixthBoxedWitness.decision n d b).lookup m t = some win →
        P4AOriginalOrderedThirdFullPolicy.accepted R d (N:ℝ) n h win.val ∧
        value = (rounded n (endpoint win.val t):ℝ) ∧
        P1QuantizedActionLicense.LowerLicense (selected win.val) t value ∧
        value+width n ≤ VariableEnvelope.v (∑ j ∈ selected win.val,t j) := by
  let d := bank e q a
  have hist := (row_owner i hs ha hN p hp ht).2
  obtain ⟨b,hb,hseed⟩ := Finset.mem_image.mp (originalSeed_mem d (N:ℝ) (pre p))
  have hl : lambda3 d (N:ℝ) (pre p) = (b:ℝ) :=
    (lambda3_ancestor d (N:ℝ) 4 (by decide) (pre p)).symm.trans (hist.seed.trans hseed.symm)
  have H := P1OriginalSixthWinnerBankRead.read_at_history n m d b (N:ℝ) (pre p) (pre_len p) hl hseed.symm
  dsimp only at H ⊢
  rw [pre_log] at H
  rw [P4AOriginalOrderedThirdFullPolicy.root_on_old_owner (d:=d)
      (by exact_mod_cast hs.1 : 0 ≤ (d.e:ℝ)) (by exact_mod_cast hN.le) hw hist.active.2,
    P4AOriginalOrderedThirdFullPolicy.cap6_prior]
  refine ⟨b,hb,hseed.symm,H.1,H.2.1,?_⟩
  intro win hwin
  obtain ⟨_,hacc,hv,hg,hd⟩ := H.2.2 win hwin
  refine ⟨?_,hv,hg,hd⟩
  unfold P4AOriginalOrderedThirdFullPolicy.accepted
  dsimp only
  rw [P4AOriginalOrderedThirdFullPolicy.eligible_prior]
  exact hacc

/-- The value/tag, archive input and true coarse owner are refined at the
same m. The omitted quantity is ordinary volume of rejected boxes on the
actual archive union. The pointwise fallback is available independently. -/
theorem common_schedule (ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, ∀ n ≥ n0, 4*width n < 1/1600 ∧
      ∀ e : ℚ, 0 < e → e ≤ 1/64000 → ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0,
      Schedule e q 0 ∧ ∀ a : ℝ, a ≤ 1/100 → ∃ m0 : ℕ, ∀ m ≥ m0,
        omitted (joint n e q a) archived (fun _ => (1:ℝ)) m < ε ∧
        ∀ i : Row, ∀ N : ℕ, 1 < N → ∀ p : Fin 6 → ℕ, (∀ j,0 < p j) →
          actualPrimeTupleLog N p ∈ box i → actualPrimeTupleLog N p ∈ accepted (joint n e q a) m →
          FixedRead n m (old e q a) i (actualPrimeTupleLog N p) ∧
          FixedRead n m (bank e q a) i (actualPrimeTupleLog N p) ∧ RawRead m e q a (actualPrimeTupleLog N p) := by
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp
    (width_tendsto.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/6400)))
  refine ⟨n0,?_⟩
  intro n hn
  refine ⟨by linarith only [hn0 n hn],?_⟩
  intro e he hemax
  obtain ⟨q0,hq0,hstep⟩ := exists_refinement_step_le_half ((e:ℝ)/10) (by positivity)
  refine ⟨q0,hq0,?_⟩
  intro q hq
  have hqpos := hq0.trans_le hq
  have hmono : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ logPrimeMeshStep 0 (19/96) (refinedMesh q0) := by
    rw [refined_step q hqpos,refined_step q0 hq0]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by norm_num))
  have hs : Schedule e q 0 := ⟨he.le,hemax,hqpos,hmono.trans (by linarith only [hstep]),by norm_num⟩
  refine ⟨hs,?_⟩
  intro a ha
  have hf : IntegrableOn (fun _ : Fin 6 → ℝ => (1:ℝ)) archived :=
    continuous_const.integrableOn_Icc.mono_set archived_subset
  obtain ⟨m0,H⟩ := eventually_atTop.mp
    ((tendsto_omitted (joint n e q a) archived _ hf).eventually (gt_mem_nhds hε))
  exact ⟨m0,fun m hm => ⟨H m hm,fun i _ hN p hp ht hc =>
    three_actual_reads n m hs ha i hN p hp ht hc⟩⟩

end
end ImbalancedChen.P1OriginalSavedRowsWinnerSchedule
