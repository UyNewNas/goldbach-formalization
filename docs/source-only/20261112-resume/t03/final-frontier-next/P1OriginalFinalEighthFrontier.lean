import ImbalancedChen.P1OriginalFull87FinalWinnerBoxes
import ImbalancedChen.P4AOriginalOrderedSixthSigned
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-! Canonical rank-eight occurrences of the published finite policy. The
state has the original selected word, positive sign, actual product of the
local weights and exactly the strict remaining rough prime universe. -/
namespace ImbalancedChen.P1OriginalFinalEighthFrontier
noncomputable section
open scoped Classical BigOperators List
open P4AOriginalFiniteFallbackBank (Bank)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length pre_ofFn tuple_pre source_strictAnti)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87SourceDictionary (Cell Source)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87UnionHistory (bank)
open P4AOriginalOrderedThirdFullPolicy (six eight current)

abbrev rule (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N : ℕ) :=
  P4AOriginalFiniteFallbackPolicy.policy B (width r) n (bank e q a) ω (N:ℝ)

/-- The compiler attaches to the odd projection of precisely this rule. -/
theorem rule_even (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N : ℕ) (h : List ℕ) :
    rule B r n e q a ω N true h=true := by
  let d := bank e q a
  have h6 : six (current d ω (N:ℝ) h) d (N:ℝ) n true h=true :=
    (P4AOriginalOrderedSixthStages.policy_ten n d ω (N:ℝ) true h).symm.trans
      (P4AOriginalOrderedSixthSigned.even 10 n d ω (N:ℝ) h)
  unfold rule P4AOriginalFiniteFallbackPolicy.policy P4AOriginalFiniteFallbackPolicy.dispatch
  split_ifs
  · simp [P4AOriginalFiniteFallbackPolicy.upper,HistoricalThirdCoarse.initialPolicy,
      ordinaryParityRosserPolicy,oddFirstExitPolicy]
  · change eight (current d ω (N:ℝ) h) d (N:ℝ) (width r) n true h=true
    by_cases hlen : h.length≤8
    · simpa only [eight,firstExitDepthSplicePolicy,if_pos hlen] using h6
    · simp only [eight,firstExitDepthSplicePolicy,if_neg hlen]
      cases P4AOriginalFull87FiniteEighthPolicy.selectedCap (width r) n (N:ℝ) h <;> simp [h6]

theorem rule_is_physical (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N : ℕ) :
    rule B r n e q a ω N=oddFirstExitPolicy
      (P4AOriginalFiniteFallbackPolicy.F B (width r) n (bank e q a) ω N) := by
  funext b h
  cases b with
  | false => rfl
  | true => exact rule_even B r n e q a ω N h

abbrev frontier (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (N cap : ℕ) (w z : ℝ) (g : ℕ → ℝ) :=
  firstExitDepthFrontier 8 (rule B r n e q a ω N) g [] true 1 (roughPrimeUniverse N cap w z)

theorem canonical_fields (N cap : ℕ) (w : ℝ) (g : ℕ → ℝ) (p : Fin 8 → ℕ) :
    let s := canonicalState N cap w g p
    s.selectedPrefix=pre p ∧ s.positive=true ∧ s.mass=(∏ i,g (p i)) ∧
      s.remaining=roughPrimeUniverse N cap w (p 7:ℝ) := by
  refine ⟨rfl,rfl,?_,rfl⟩
  change ((pre p).map g).prod=_
  simp only [pre_ofFn,List.map_reverse,List.prod_reverse,List.map_ofFn,List.prod_ofFn,Function.comp_def]

/-- Reuse the actual occurrence permutation before passing to any sum.
In the reverse direction all four fields of the returned state are forced. -/
theorem canonical_iff_admitted (P : Bool → List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (g : ℕ → ℝ) (p : Fin 8 → ℕ) :
    canonicalState N cap w g p ∈ firstExitDepthFrontier 8 P g [] true 1 (roughPrimeUniverse N cap w z) ↔
      p ∈ firstExitAdmittedTuples 8 P (roughPrimeUniverse N cap w z) := by
  let u := roughPrimeUniverse N cap w z
  let F := firstExitDepthFrontier 8 P g [] true 1 u
  have H : p∈F.map (fun s => primeHistoryTuple 8 s.selectedPrefix) ↔
      p∈firstExitAdmittedTuples 8 P u := by
    rw [firstExitAdmittedTuples,List.mem_toFinset]
    exact (firstExitRootFrontier_admitted_tuple_perm 8 P g u).mem_iff
  constructor
  · intro hs
    exact H.mp (List.mem_map.mpr ⟨canonicalState N cap w g p,hs,tuple_pre p⟩)
  · intro hp
    obtain ⟨s,hs,ht⟩ := List.mem_map.mp (H.mpr hp)
    have hl := firstExitDepthFrontier_selected_length 8 P g [] u true 1 (by simp) s hs
    have hpre : s.selectedPrefix=pre p := by
      rw [pre_ofFn,←ht]
      exact (primeHistoryTuple_reverse_ofFn hl).symm
    have hsign : s.positive=true := by
      simpa [hpre,pre,evenListLength] using
        mem_firstExitDepthFrontier_positive_eq_evenListLength 8 P g u s hs
    have hmass := mem_firstExitDepthFrontier_mass_eq_selected_prod 8 P g u s hs
    rw [hpre] at hmass
    obtain ⟨l,tail,hsel,_,hrest⟩ :=
      mem_firstExitDepthFrontier_roughPrime_remaining 8 (by decide) P g N cap w z s hs
    have hlast : l=p 7 := by
      simpa [pre] using (congrArg (fun xs : List ℕ => xs.headD 0) (hpre.symm.trans hsel)).symm
    rw [hlast] at hrest
    have heq : s=canonicalState N cap w g p := by
      cases s with
      | mk sp b mass rest =>
        dsimp only at hpre hsign hmass hrest
        subst sp; subst b; subst mass; subst rest; rfl
    rwa [heq] at hs

/-- The four actual odd prefix tests determine membership at every
source point, including ties, absent third owners, and unselected eighth
actions. Every even prefix is retained. -/
theorem actual_source_iff (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (N cap : ℕ) (hN : 1<(N:ℝ)) (w z : ℝ)
    (hw : w≤(N:ℝ)^(53/13824:ℝ)) (hz : (N:ℝ)^VariableEnvelope.mu≤z) (hcap : z≤cap)
    (g : ℕ → ℝ) (p : Fin 8 → ℕ) (hp : ∀ i,(p i).Prime) (hd : ∀ i,¬p i∣N)
    (c : Cell) (hs : Source c (point (N:ℝ) p)) :
    let P := rule B r n e q a ω N
    canonicalState N cap w g p ∈ frontier B r n e q a ω N cap w z g ↔
      P false [p 0]=true ∧ P false [p 2,p 1,p 0]=true ∧
      P false [p 4,p 3,p 2,p 1,p 0]=true ∧ P false [p 6,p 5,p 4,p 3,p 2,p 1,p 0]=true := by
  dsimp only
  rw [canonical_iff_admitted,mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap _ _ _ _ _ _ hcap]
  have hpos (i) := (hp i).pos
  have ho := source_strictAnti _ hN p hpos c hs
  have hb := P4AOriginalFull87PolicyReverseAdmission.source_carrier_bounds _ hN p hpos c hs w z hw hz
  have hcar (i) : (p i).Prime ∧ ¬p i∣N ∧ w≤(p i:ℝ) ∧ (p i:ℝ)<z := ⟨hp i,hd i,hb i⟩
  rw [show List.ofFn p=[p 0,p 1,p 2,p 3,p 4,p 5,p 6,p 7] by simp [List.ofFn_succ]]
  simp only [ho,hcar,forall_const,true_and,FirstExitValidSelection,Bool.not_true,Bool.not_false,
    rule_even,and_true]

end
end ImbalancedChen.P1OriginalFinalEighthFrontier
