import ImbalancedChen.P1OriginalOrderedSixthCompleteWinner
import ImbalancedChen.P1OriginalSavedRowsWinnerSchedule
import ImbalancedChen.P4AOriginalFull87SourcePrimeTests

/-! Same-m read of the final ordered tree on every original eighth source,
including sources with no saved rectangle. The retained and fallback
branches use their own actual fifth and sixth parents at the same N. -/
namespace ImbalancedChen.P1OriginalFull87FinalWinnerBoxes
noncomputable section
open scoped Classical Topology BigOperators
open Set Filter MeasureTheory
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision
open P1AffineCertifiedMesh P1AffineCertifiedLookup
open P4AOriginalFourthFifthAffinePrograms
open P4AFull87VariableSeedHistory (liftSeed liftSeed_exact)
open P4AOriginalSavedSixthHistoricalOwner (bank)
open P4AOriginalFull87SourceDictionary (Cell Point Source source_basic)
open P4AOriginalFull87StrictActionTrim (sourceSet)
open P4AOriginalSixthActionBank (Entry endpoint)
open P4AOrderedThirdStaticSixthPrograms (atSix)
open P4AOrderedThirdStaticRootPrograms (mode)
open P4AOriginalOrderedThirdFullPolicy (current cap5 cap6 fifth after eligible)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P1OriginalSavedRowsWinnerSchedule (joint archived Key)
open P1OriginalOrderedSixthCompleteWinner (tag)
open P4AOriginalFull87TrimOmission (source_volume_lt_top)
open P1GuardFrozenFiniteCapAlgebra (rounded)

private def cutFlag : Trace 6 Bool := guarded
  [LE (atom (X 0)) (atom (K VariableEnvelope.mu)),LE (atom (K (1/100))) (atom (X 2))]
  (.leaf true) (.leaf false)

private theorem cutFlag_true (u : Fin 6 → ℝ) :
    cutFlag.eval u = true ↔ u 0 ≤ VariableEnvelope.mu ∧ 1/100 ≤ u 2 := by
  simp [cutFlag,guarded_eval,Trace.eval,holds_LE,Program.eval]

private def modeFlag (d : OriginalData) : Trace 6 Bool :=
  .branch (LE (atom (K 1)) (liftSeed 6 (by decide) (mode d))) (.leaf true) (.leaf false)

private theorem mode_read (d : OriginalData) {N : ℕ} (hN : 1 < N) (ω : ℝ) (h : List ℕ)
    (hl : h.length=6) (hp : ∀ p∈h,0 < p) (hc : ω ≤ primeHistoryLogCoordinates (N:ℝ) 6 h 2) :
    (modeFlag d).eval (primeHistoryLogCoordinates (N:ℝ) 6 h) = true ↔ (current d ω (N:ℝ) h).lower := by
  have h3 : (rosserAncestor 3 h).length = 3 := by simp [hl]
  have hpos := hp _ ((List.drop_sublist _ _).subset (primeHistoryTuple_mem h3 (2:Fin 3)))
  have H := (P4AOrderedThirdRankReads.native_modes d (N:ℝ) h h3 hpos).2.1
  rw [P1OriginalOrderedSixthCompleteWinner.rough_root d hN ω h hl hp hc]
  simpa [modeFlag,Trace.eval,holds_LE,Program.eval,liftSeed_exact _ _ _ (N:ℝ) h hl] using H

abbrev Keys (e : ℚ) (q : ℕ) (a : ℝ) := Key e q a ⊕ (Bool × Bool)

def programs (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) : Keys e q a → Spec 6
  | .inl k => joint n e q a k
  | .inr (false,false) => ⟨6,cutFlag.code,Function.Embedding.refl _⟩
  | .inr (false,true) => ⟨6,(modeFlag (bank e q a)).code,Function.Embedding.refl _⟩
  | .inr (true,false) => ⟨6,atSix n (bank e q a),Function.Embedding.refl _⟩
  | .inr (true,true) => ⟨6,(tag n (bank e q a)).code,Function.Embedding.refl _⟩

abbrev firstSix (t : Point) : Fin 6 → ℝ := fun i => t (i.castLE (by decide))

def onEight (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : Keys e q a) : Spec 8 :=
  let s := programs n e q a k
  ⟨s.rank,s.program,s.embed.trans ⟨fun i => i.castLE (by decide),by intro i j he; exact Fin.ext (congrArg Fin.val he)⟩⟩

theorem refines_saved {n m : ℕ} {e : ℚ} {q : ℕ} {a : ℝ} :
    accepted (programs n e q a) m ⊆ accepted (joint n e q a) m :=
  fun _ h => mem_iInter.mpr fun k => mem_iInter.mp h (.inl k)

private theorem source_region {c : Cell} {t : Point} (ht : Source c t) :
    firstSix t 0 ≤ VariableEnvelope.mu ∧ 1/100 ≤ firstSix t 2 :=
  ⟨(source_basic ht).1.le,(source_basic ht).2.1.le⟩

/-- A single affine output formula, actual mode and provenance tag on
the entire approved closed box. In raw mode the formula can vary there. -/
theorem fixed_on_full87 (n m : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (c : Cell) (t : Point)
    (hs : Source c t) (hc : t ∈ accepted (onEight n e q a) m) :
    let d := bank e q a
    let j := gridLabel m (firstSix t)
    ∃ value : Affine 6, ∃ lower : Bool, ∃ winner : Option Entry,
      firstSix t ∈ cell m j ∧ ∀ u : Fin 6 → ℝ, (∀ k,lo m j k ≤ u k) → (∀ k,u k ≤ hi m j k) →
      (u 0 ≤ VariableEnvelope.mu ∧ 1/100 ≤ u 2) ∧ (atSix n d).eval u = value.eval u ∧
      (tag n d).lookup m u = winner ∧ ∀ N : ℕ, 1 < N → ∀ h : List ℕ, h.length=6 →
      (∀ p∈h,0 < p) → primeHistoryLogCoordinates (N:ℝ) 6 h = u → ∀ ω : ℝ, ω ≤ 1/100 →
        let R := current d ω (N:ℝ) h
        let parent := if R.lower then cap5 R d (N:ℝ) n (rosserAncestor 5 h) else fifth R d (N:ℝ) (rosserAncestor 5 h)
        (R.lower ↔ lower=true) ∧ (if R.lower then cap6 R d (N:ℝ) n h else after R d (N:ℝ) h 8)=value.eval u ∧
        (winner=none ↔ value.eval u=parent) ∧ ∀ w : Entry, winner=some w → parent < value.eval u ∧
          (if R.lower then P4AOriginalOrderedThirdFullPolicy.accepted R d (N:ℝ) n h w.val else eligible R d (N:ℝ) h w.val) ∧
          value.eval u = (if R.lower then (rounded n (endpoint w.val u):ℝ) else endpoint w.val u) := by
  let d := bank e q a
  let x := firstSix t
  let j := gridLabel m x
  have cf : x ∈ covered cutFlag.code m := mem_iInter.mp hc (.inr (false,false))
  have cm : x ∈ covered (modeFlag d).code m := mem_iInter.mp hc (.inr (false,true))
  have cv : x ∈ covered (atSix n d) m := mem_iInter.mp hc (.inr (true,false))
  have cw : x ∈ covered (tag n d).code m := mem_iInter.mp hc (.inr (true,true))
  obtain ⟨hunit,hcert⟩ := (mem_covered_iff _ _ _).mp cv
  refine ⟨(atSix n d).table ((atSix n d).signature (center m j)),(modeFlag d).eval x,
    (tag n d).eval x,gridLabel_mem m x hunit,?_⟩
  intro u hlo hhi
  have hcut := (cutFlag_true u).mp ((P1OriginalSavedRowsWinnerBoxes.fixed_tag _ m cf u hlo hhi).trans
    ((cutFlag_true x).mpr (source_region hs)))
  have hmode := P1OriginalSavedRowsWinnerBoxes.fixed_tag _ m cm u hlo hhi
  have hval := (certificate_on_approved (atSix n d) m j hcert u hlo hhi).2.symm
  have hwin := (Trace.lookup_exact (tag n d) m u).trans
    (P1OriginalSavedRowsWinnerBoxes.fixed_tag _ m cw u hlo hhi)
  refine ⟨hcut,hval,hwin,?_⟩
  intro N hN h hl hp he ω hω
  subst u
  have hr := hω.trans hcut.2
  have hm := mode_read d hN ω h hl hp hr
  rw [hmode] at hm
  have H := P1OriginalOrderedSixthCompleteWinner.actual_read n m d hN ω h hl hp hr
  dsimp only at H ⊢
  rw [hwin] at H
  have heq := H.1.symm.trans hval
  exact ⟨hm.symm,heq,heq ▸ H.2⟩

/-- The true low-sector physical Boolean read. It includes an actual eighth
override and uses the exact sixth formula for the unchanged continuation. -/
theorem final_descendant (B : Bank) (δ : ℝ) (n : ℕ) (d : OriginalData) {N : ℕ} (hN : 1 < N)
    (ω : ℝ) (h : List ℕ) (hl : h.length=6) (hp : ∀ p∈h,0 < p)
    (hlo : primeHistoryLogCoordinates (N:ℝ) 6 h 0 ≤ VariableEnvelope.mu)
    (hr : ω ≤ primeHistoryLogCoordinates (N:ℝ) 6 h 2) (later : List ℕ) (pos : Bool)
    (hmore : 6 < (later ++ h).length) :
    let word := later ++ h
    let C := (atSix n d).eval (primeHistoryLogCoordinates (N:ℝ) 6 h)
    let keep := ordinaryParityRosserPolicy false ((N:ℝ)^C) pos word
    P4AOriginalFiniteFallbackPolicy.policy B δ n d ω (N:ℝ) pos word =
      (if word.length≤8 then keep else match selectedCap δ n (N:ℝ) word with
        | none => keep | some v => ordinaryParityRosserPolicy false ((N:ℝ)^(v:ℝ)) pos word) := by
  let word := later ++ h
  let R := current d ω (N:ℝ) h
  have h3 := rosserAncestor_append 3 later h (by omega)
  have h1 := rosserAncestor_append 1 later h (by omega)
  have h6 : rosserAncestor 6 word = h := by
    rw [show word = later ++ h from rfl,rosserAncestor_append 6 later h hl.ge]
    simp [rosserAncestor,hl]
  have hroot : current d ω (N:ℝ) word = R := by simp only [current,word,h3,R]
  have hpoint : P4AOriginalFiniteFallbackPolicy.point (N:ℝ) 1 word 0≤VariableEnvelope.mu := by
    rw [P4AOriginalFiniteFallbackPolicy.point,h1,
      primeHistoryLogCoordinates_ancestor (N:ℝ) hl (by decide : 1≤6)]
    exact hlo
  have H := (P1OriginalOrderedSixthCompleteWinner.actual_read n 0 d hN ω h hl hp hr).1
  have hkeep : P4AOriginalOrderedThirdFullPolicy.six R d (N:ℝ) n pos word =
      ordinaryParityRosserPolicy false ((N:ℝ)^(atSix n d).eval (primeHistoryLogCoordinates (N:ℝ) 6 h)) pos word := by
    simp only [P4AOriginalOrderedThirdFullPolicy.six,firstExitDepthSplicePolicy,if_neg (not_le.mpr hmore),
      frozenParityRosserPolicy,ancestorFrozenPolicy,h6,H]
  dsimp only
  rw [P4AOriginalFiniteFallbackPolicy.lower_history B δ n d ω (N:ℝ) pos word hpoint,
    P4AOriginalOrderedThirdFullPolicy.policy,hroot,P4AOriginalOrderedThirdFullPolicy.eight]
  by_cases h8 : word.length≤8
  · simp only [firstExitDepthSplicePolicy,if_pos h8,hkeep]
  · simp only [firstExitDepthSplicePolicy,if_neg h8]
    cases ht : selectedCap δ n (N:ℝ) word <;> simp only [ht,hkeep]

/-- Exact, also on an unapproved box or a tie wall. No membership in a
saved rectangle, third historical owner, or trimmed source is required. -/
theorem all_sources_exact (B : Bank) (δ : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (hω : ω ≤ 1/100) {N : ℕ} (hN : 1 < N) (pre : List ℕ) (hl : pre.length=8)
    (hp : ∀ p∈pre,0 < p) (c : Cell) (hs : Source c (primeHistoryLogCoordinates (N:ℝ) 8 pre))
    (later : List ℕ) (pos : Bool) (hmore : 6 < (later ++ rosserAncestor 6 pre).length) :
    let d := bank e q a
    let x := firstSix (primeHistoryLogCoordinates (N:ℝ) 8 pre)
    let word := later ++ rosserAncestor 6 pre
    let keep := ordinaryParityRosserPolicy false ((N:ℝ)^(atSix n d).eval x) pos word
    P4AOriginalFiniteFallbackPolicy.policy B δ n d ω (N:ℝ) pos word =
      (if word.length≤8 then keep else match selectedCap δ n (N:ℝ) word with
        | none => keep | some v => ordinaryParityRosserPolicy false ((N:ℝ)^(v:ℝ)) pos word) := by
  have h6 : (rosserAncestor 6 pre).length=6 := by simp [hl]
  have hx : primeHistoryLogCoordinates (N:ℝ) 6 (rosserAncestor 6 pre) =
      firstSix (primeHistoryLogCoordinates (N:ℝ) 8 pre) := by
    funext i; exact primeHistoryLogCoordinates_ancestor (N:ℝ) hl (by decide : 6≤8) i
  have hc := source_region hs
  rw [← hx] at hc
  dsimp only
  rw [← hx]
  exact final_descendant B δ n _ hN ω _ h6 (fun p hm => hp p ((List.drop_sublist _ _).subset hm))
    hc.1 (hω.trans hc.2) later pos hmore

/-- A single pre-N mesh controls the union of all saved boxes and the
sum of the 87 original source omissions. The cutoff ω is still free. -/
theorem whole_mesh (n : ℕ) (e : ℚ) (q : ℕ) (a ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, ∀ m≥m0, omitted (programs n e q a) archived (fun _ => (1:ℝ)) m +
      (∑ c : Cell,omitted (onEight n e q a) (sourceSet c) (fun _ => (1:ℝ)) m) < ε := by
  have harch : IntegrableOn (fun _ : Fin 6 → ℝ => (1:ℝ)) archived :=
    continuous_const.integrableOn_Icc.mono_set P1OriginalSavedRowsWinnerSchedule.archived_subset
  have hs := tendsto_finset_sum (Finset.univ : Finset Cell) (fun c _ =>
    tendsto_omitted (onEight n e q a) (sourceSet c) (fun _ => (1:ℝ))
      (integrableOn_const (source_volume_lt_top c).ne))
  have H := (tendsto_omitted (programs n e q a) archived _ harch).add hs
  simp only [Finset.sum_const_zero,add_zero] at H
  exact eventually_atTop.mp (H.eventually (gt_mem_nhds hε))

end
end ImbalancedChen.P1OriginalFull87FinalWinnerBoxes
