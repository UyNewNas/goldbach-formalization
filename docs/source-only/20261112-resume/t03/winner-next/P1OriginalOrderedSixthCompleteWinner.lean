import ImbalancedChen.P4AOrderedThirdRankReads
import ImbalancedChen.P4AOriginalSixthTaggedWinner

/-! Provenance for both branches of the final ordered sixth read. The
chronology when the lower mode is off uses its raw predecessor at each stage.
No original saved rectangle or old third owner is assumed. -/
namespace ImbalancedChen.P1OriginalOrderedSixthCompleteWinner
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P4AOriginalFourthFifthAffinePrograms P4AFull87VariableSeedHistory
open P4AOriginalSixthActionBank (Action Entry allActions endpoint selected mem_allActions)
open P4AOriginalSixthTaggedWinner (entries mem_entries)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1OriginalVariableFourthContinuation (finiteMax finiteMax_seed_le)
open P4AOriginalOrderedThirdFullPolicy
open P4AOrderedThirdStaticRootPrograms (mode native seed)
open P4AOrderedThirdStaticSixthPrograms
open P1FiniteAffineQuantizerTable (roundedProgram roundedProgram_exact)
open P1GuardFrozenFiniteCapAlgebra (rounded finiteMax_attained)
open P4AOriginalCompleteSixthChronology (applyLater laterEligible)

private def pick (old new : Program 6) (cost : Action → Program 6)
    (tests : Action → List (Gate 6)) : Trace 6 (Option Entry) :=
  .branch (LT old new) (firstWitness (fun a : Entry =>
    tests a.val ++ [LE (cost a.val) new, LE new (cost a.val)]) entries) (.leaf none)

private theorem pick_read (old new : Program 6) (cost : Action → Program 6)
    (tests : Action → List (Gate 6)) (t : Fin 6 → ℝ)
    (hle : old.eval t ≤ new.eval t)
    (hatt : old.eval t < new.eval t →
      ∃ w : Entry, Passed t (tests w.val) ∧ new.eval t = (cost w.val).eval t) :
    ((pick old new cost tests).eval t = none ↔ new.eval t = old.eval t) ∧
    (∀ w : Entry, (pick old new cost tests).eval t = some w →
      old.eval t < new.eval t ∧ Passed t (tests w.val) ∧ new.eval t = (cost w.val).eval t) := by
  let gs (w : Entry) := tests w.val ++ [LE (cost w.val) new,LE new (cost w.val)]
  have eqv (w : Entry) : Passed t (gs w) ↔ Passed t (tests w.val) ∧ new.eval t = (cost w.val).eval t := by
    simp only [gs,passed_append,passed_cons,passed_nil,holds_LE,and_true]
    exact and_congr_right fun _ => ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
  rw [pick,Trace.eval,holds_LT]
  by_cases hu : old.eval t < new.eval t
  · rw [if_pos hu]
    obtain ⟨w,hw⟩ := hatt hu
    obtain ⟨win,hwin⟩ := firstWitness_exists gs entries t ⟨w,mem_entries w,(eqv w).mpr hw⟩
    refine ⟨⟨?_,fun he => (ne_of_gt hu he).elim⟩,?_⟩
    · intro hz
      rw [hz] at hwin
      cases hwin
    · intro v hv
      exact ⟨hu,(eqv v).mp (firstWitness_sound gs entries t v hv).2⟩
  · rw [if_neg hu]
    exact ⟨⟨fun _ => le_antisymm (le_of_not_gt hu) hle,fun _ => rfl⟩,fun _ h => by cases h⟩

private theorem raw_attainment (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) (k : ℕ) :
    let A := fifth R d N (rosserAncestor 5 h)
    A ≤ after R d N h k ∧ (after R d N h k = A ∨ ∃ act : Action,
      eligible R d N h act ∧ after R d N h k = endpoint act (primeHistoryLogCoordinates N 6 h)) := by
  let t := primeHistoryLogCoordinates N 6 h
  let A := fifth R d N (rosserAncestor 5 h)
  let S := finiteMax Finset.univ (fun i => saved R d N i h)
    (fun i => P4AOriginalSavedSixthArchive.endpoint i t) A
  induction k with
  | zero =>
    have hS : A ≤ S := finiteMax_seed_le _ _ _ _
    refine ⟨hS.trans (finiteMax_seed_le _ _ _ _),?_⟩
    rcases finiteMax_attained Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
        (fun c => eleven R d N c h) (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) S
        with hE | ⟨c,_,hc,hE⟩
    · rcases finiteMax_attained Finset.univ (fun i => saved R d N i h)
          (fun i => P4AOriginalSavedSixthArchive.endpoint i t) A with h0 | ⟨i,_,hi,h0⟩
      · exact Or.inl (hE.trans h0)
      · exact Or.inr ⟨.saved i,hi,hE.trans h0⟩
    · exact Or.inr ⟨.eleven c,hc,hE⟩
  | succ k ih =>
    refine ⟨ih.1.trans (finiteMax_seed_le _ _ _ _),?_⟩
    rcases finiteMax_attained Finset.univ (fun c => laterEligible k (after R d N h k) N c h)
        (fun c => P4AOriginalSixthLaterSemantics.endpoint c t) (after R d N h k)
        with hE | ⟨c,_,hc,hE⟩
    · rcases ih.2 with h0 | ⟨act,ha,h0⟩
      · exact Or.inl (hE.trans h0)
      · exact Or.inr ⟨act,ha,hE.trans h0⟩
    · have hj : P4AOriginalSixthLaterLiteral.stage c = k := hc.2.1
      exact Or.inr ⟨.later c,by simpa only [eligible,hj] using hc,hE⟩

def tag (n : ℕ) (d : OriginalData) : Trace 6 (Option Entry) :=
  let s := seed d
  let b := native d
  .branch (LE (atom (K 1)) (liftSeed 6 (by decide) (mode d)))
    (pick ((p5 n d s b).pull Fin.castSucc) (p6 n d s b)
      (fun a => roundedProgram n (endpointProgram a)) (licensedTests n d b))
    (pick (variableFifthAtSix d b) (variableAfterProgram d b 8) endpointProgram (actionTests d b))

private theorem raw_tests (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ)
    (hl : h.length = 6) (hb : baseValue (native d) N h = third R N h) (a : Action) :
    Passed (primeHistoryLogCoordinates N 6 h) (actionTests d (native d) a) ↔ eligible R d N h a := by
  cases a with
  | saved i => exact saved_iff R d _ N h hl hb i
  | eleven c => exact eleven_iff R d _ N h hl hb c
  | later c =>
    simpa only [actionTests,eligible,laterEligible,hl,true_and,after_exact R d _ N h hl hb]
      using P4AOriginalCompleteSixthAffinePrograms.laterTests_exact (P4AOriginalSixthLaterLiteral.stage c)
        (variableAfterProgram d (native d) (P4AOriginalSixthLaterLiteral.stage c)) c (primeHistoryLogCoordinates N 6 h)

theorem rough_root (d : OriginalData) {N : ℕ} (hN : 1 < N) (ω : ℝ) (h : List ℕ)
    (hl : h.length = 6) (hp : ∀ p∈h,0 < p) (hrough : ω ≤ primeHistoryLogCoordinates (N:ℝ) 6 h 2) :
    current d ω (N:ℝ) h = current d 0 (N:ℝ) h := by
  let h3 := rosserAncestor 3 h
  have hz : h3.length = 3 := by simp [h3,hl]
  have hpos (p : ℕ) (hm : p∈h3) : 0 < p := hp p ((List.drop_sublist _ _).subset hm)
  have hp3 := hpos _ (primeHistoryTuple_mem hz (2:Fin 3))
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have ha : HistoricalThirdCoarse.active ω (N:ℝ) h3 := by
    refine ⟨hz,?_⟩
    rw [← rpow_primeHistoryLogCoordinates (N:ℝ) hNr hz hpos (2:Fin 3),
      primeHistoryLogCoordinates_ancestor (N:ℝ) hl (by decide : 3≤6)]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hrough
  have ha0 : HistoricalThirdCoarse.active 0 (N:ℝ) h3 := by
    refine ⟨hz,?_⟩
    rw [Real.rpow_zero]
    exact_mod_cast hp3
  simp only [current,P4AOriginalOrderedThirdTable.rawExponent,ha,ha0,if_true]

/-- All three scalar outputs are the real current policy's values at
their own ancestors. Lower mode requires all square/selected-tent checks.
The other mode reuses the original raw action and unrounded endpoint. -/
theorem actual_read (n m : ℕ) (d : OriginalData) {N : ℕ} (hN : 1 < N)
    (ω : ℝ) (h : List ℕ) (hl : h.length = 6) (hp : ∀ p∈h,0 < p)
    (hrough : ω ≤ primeHistoryLogCoordinates (N:ℝ) 6 h 2) :
    let R := current d ω (N:ℝ) h
    let t := primeHistoryLogCoordinates (N:ℝ) 6 h
    let A := if R.lower then cap5 R d (N:ℝ) n (rosserAncestor 5 h) else fifth R d (N:ℝ) (rosserAncestor 5 h)
    let C := if R.lower then cap6 R d (N:ℝ) n h else after R d (N:ℝ) h 8
    (atSix n d).eval t = C ∧ ((tag n d).lookup m t = none ↔ C=A) ∧
    ∀ win : Entry, (tag n d).lookup m t = some win → A<C ∧
      (if R.lower then accepted R d (N:ℝ) n h win.val else eligible R d (N:ℝ) h win.val) ∧
      C = (if R.lower then (rounded n (endpoint win.val t):ℝ) else endpoint win.val t) := by
  let N' : ℝ := N
  let h3 := rosserAncestor 3 h
  let t := primeHistoryLogCoordinates N' 6 h
  have hz : h3.length = 3 := by simp [h3,hl]
  have hpos (p : ℕ) (hm : p∈h3) : 0 < p := hp p ((List.drop_sublist _ _).subset hm)
  have hp3 := hpos _ (primeHistoryTuple_mem hz (2:Fin 3))
  have hcut := rough_root d hN ω h hl hp hrough
  let R := current d 0 N' h
  obtain ⟨hs,hm,hb⟩ := P4AOrderedThirdRankReads.native_modes d N' h hz hp3
  have scalar := P4AOrderedThirdRankReads.six_exact n d N' h hl hp3
  dsimp only
  rw [hcut,Trace.lookup_exact]
  refine ⟨scalar,?_⟩
  have hmode : (LE (atom (K 1)) (liftSeed 6 (by decide) (mode d))).holds t ↔ R.lower := by
    simpa only [holds_LE,Program.eval,Affine.eval_const,t,liftSeed_exact _ _ _ N' h hl] using hm
  rw [tag,Trace.eval,show (LE (atom (K 1)) (liftSeed 6 (by decide) (mode d))).holds t ↔ R.lower from hmode]
  by_cases H : R.lower
  · simp only [if_pos H]
    have h5 : (rosserAncestor 5 h).length = 5 := by simp [hl]
    have hs5 : baseValue (seed d) N' (rosserAncestor 5 h)=R.scalar := by
      simpa only [baseValue,rosserAncestor_nested 3 5 (by decide)] using hs
    have hb5 : baseValue (native d) N' (rosserAncestor 5 h)=third R N' (rosserAncestor 5 h) := by
      simpa only [baseValue,rosserAncestor_nested 3 5 (by decide),third_ancestor R N' h 5 (by decide)] using hb
    have hproj : (fun i : Fin 5 => t i.castSucc)=primeHistoryLogCoordinates N' 5 (rosserAncestor 5 h) := by
      funext i; exact (primeHistoryLogCoordinates_ancestor N' hl (by decide : 5≤6) i).symm
    have hf : ((p5 n d (seed d) (native d)).pull Fin.castSucc).eval t = cap5 R d N' n (rosserAncestor 5 h) := by
      rw [Program.eval_pull,hproj,p5_exact R n d _ _ N' _ h5 hs5 hb5]
    have hc := p6_exact R n d _ _ N' h hl hs hb
    have H' := pick_read ((p5 n d (seed d) (native d)).pull Fin.castSucc) (p6 n d (seed d) (native d))
      (fun a => roundedProgram n (endpointProgram a)) (licensedTests n d (native d)) t
      (by rw [hf,hc]; exact finiteMax_seed_le _ _ _ _) (by
        intro hlt
        rw [hf,hc] at hlt
        rcases finiteMax_attained allActions (accepted R d N' n h)
          (fun a => (rounded n (endpoint a t):ℝ)) (cap5 R d N' n (rosserAncestor 5 h))
          with heq | ⟨act,ha',hacc,hval⟩
        · exact (ne_of_gt hlt heq).elim
        · exact ⟨⟨act,ha'⟩,(licensed_iff R n d _ N' h hl hb act).mpr hacc,by
            rw [hc,roundedProgram_exact,endpoint_exact]; exact hval⟩)
    simpa only [hf,hc,licensed_iff R n d _ N' h hl hb,roundedProgram_exact,endpoint_exact] using H'
  · simp only [if_neg H]
    have hf := five_at_six R d (native d) N' h hl hb
    have hc := after_exact R d (native d) N' h hl hb 8
    have hr := raw_attainment R d N' h 8
    have H' := pick_read (variableFifthAtSix d (native d)) (variableAfterProgram d (native d) 8)
      endpointProgram (actionTests d (native d)) t (by rw [hf,hc]; exact hr.1) (by
        intro hlt
        rw [hf,hc] at hlt
        rcases hr.2 with heq | ⟨act,ha',hval⟩
        · exact (ne_of_gt hlt heq).elim
        · exact ⟨⟨act,mem_allActions act⟩,(raw_tests R d N' h hl hb act).mpr ha',by
            rw [hc,endpoint_exact]; exact hval⟩)
    simpa only [hf,hc,raw_tests R d N' h hl hb,endpoint_exact] using H'

end
end ImbalancedChen.P1OriginalOrderedSixthCompleteWinner
