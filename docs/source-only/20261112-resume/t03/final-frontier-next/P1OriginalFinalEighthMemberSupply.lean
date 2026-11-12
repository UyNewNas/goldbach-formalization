import ImbalancedChen.P1OriginalFinalEighthFrontier
import ImbalancedChen.P4AOriginalR17EighthParent

/-! The actual final word is admitted on each original history core.
The original eighth upgrade is selected on the smaller action trim.
Both ownership tests are attached to the same arithmetic occurrence. -/
namespace ImbalancedChen.P1OriginalFinalEighthMemberSupply
noncomputable section
open scoped Classical BigOperators
open P1OriginalFinalEighthFrontier
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87SourceDictionary (Cell Source comparison source_basic)
open P4AOriginalFull87StrictActionTrim (trim trim_subset_source trim_subset_core)
open P4AOriginalFull87HistoryCore (width width_pos core)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory exists_original_common_history)
open P4AOriginalFull87SevenCubeAdmission (pre point pre_length pre_ofFn)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87UnionHistory (bank oldBank)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_append point8_at_eight)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix ownerAtPrefix_rank_eight)
open P4AOriginalOrderedThirdFullPolicy (current prior six eight five common base six_prior root_on_old_owner)
open P4AOriginalR17EighthParent (parent)

private theorem prefix_read (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (N : ℕ) (hN : 1≤(N:ℝ)) (p : Fin 8 → ℕ)
    (c : Cell) (hs : Source c (point (N:ℝ) p)) (hh : RealizedHistory e q a (N:ℝ) (pre p) c)
    (k : ℕ) (hk : 1≤k) (hk8 : k≤8) (b : Bool) :
    rule B r n e q a ω N b (rosserAncestor k (pre p)) =
      P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N:ℝ) b (rosserAncestor k (pre p)) := by
  let d := bank e q a
  let u := rosserAncestor k (pre p)
  have hl : u.length=k := by simp [u,pre_length,min_eq_left hk8]
  have hlo : P4AOriginalFiniteFallbackPolicy.point (N:ℝ) 1 u 0≤VariableEnvelope.mu := by
    rw [P4AOriginalFiniteFallbackPolicy.point,show rosserAncestor 1 u=rosserAncestor 1 (pre p) from
      rosserAncestor_nested 1 k hk (pre p),primeHistoryLogCoordinates_ancestor (N:ℝ) (pre_length p) (by decide : 1≤8)]
    exact (source_basic hs).1.le
  change P4AOriginalFiniteFallbackPolicy.policy B (width r) n d ω (N:ℝ) b u = _
  rw [P4AOriginalFiniteFallbackPolicy.lower_history B (width r) n d ω (N:ℝ) b u hlo]
  change eight (current d ω (N:ℝ) u) d (N:ℝ) (width r) n b u =
    P4AOriginalFull87DataPolicy.sixthPolicy n d (N:ℝ) b u
  rw [eight,firstExitDepthSplicePolicy,if_pos (hl.trans_le hk8),←six_prior]
  by_cases h3 : 3≤k
  · have ho : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) u := by
      change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor k (pre p)))
      rw [rosserAncestor_nested 3 k h3]
      exact hh.2.1
    rw [root_on_old_owner (by exact_mod_cast he : 0≤(d.e:ℝ)) hN hω ho]
  · have h2 : u.length≤2 := by omega
    have h3' : u.length≤3 := by omega
    have h4 : u.length≤4 := by omega
    have h6 : u.length≤6 := by omega
    simp only [six,five,common,base,firstExitDepthSplicePolicy,if_pos h6,if_pos h4,if_pos h3',if_pos h2]

theorem canonical_of_history (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (N cap : ℕ) (hN : 1<(N:ℝ)) (w z : ℝ)
    (hw : w≤(N:ℝ)^(53/13824:ℝ)) (hz : (N:ℝ)^VariableEnvelope.mu≤z) (hcap : z≤cap)
    (g : ℕ → ℝ) (p : Fin 8 → ℕ) (hp : ∀ i,(p i).Prime) (hd : ∀ i,¬p i∣N)
    (c : Cell) (hs : Source c (point (N:ℝ) p)) (hh : RealizedHistory e q a (N:ℝ) (pre p) c) :
    canonicalState N cap w g p ∈ frontier B r n e q a ω N cap w z g := by
  rw [actual_source_iff B r n e q a ω N cap hN w z hw hz hcap g p hp hd c hs]
  have H := P4AOriginalFull87UnionHistory.validSelection n e q a (N:ℝ) he hN p hp c hs hh
  simp only [pre,List.reverse_cons,List.reverse_nil,List.nil_append,List.append_assoc,List.singleton_append,
    FirstExitValidSelection,Bool.not_true,Bool.not_false,P4AOriginalFull87UnionHistory.sixthPolicy,
    P4AOriginalFull87DataPolicy.sixth_even,true_and,and_true] at H
  have E := prefix_read B r n e q a ω he hω N hN.le p c hs hh
  have E1 := E 1 (by decide) (by decide) false
  have E3 := E 3 (by decide) (by decide) false
  have E5 := E 5 (by decide) (by decide) false
  have E7 := E 7 (by decide) (by decide) false
  simp [pre,rosserAncestor] at E1 E3 E5 E7
  exact ⟨E1.trans H.1,E3.trans H.2.1,E5.trans H.2.2.1,E7.trans H.2.2.2⟩

/-- On any original source the true eighth decision depends on exactly
the action trim. Failing that test does not sever the sixth ancestor. -/
theorem eighth_owner (r n : ℕ) (N : ℕ) (p : Fin 8 → ℕ) (c : Cell)
    (hs : Source c (point (N:ℝ) p)) :
    ownerAtPrefix (N:ℝ) (pre p)=some c ∧ ∀ later : List ℕ,
      selectedCap (width r) n (N:ℝ) (later++pre p) =
        if point (N:ℝ) p∈trim c (width r) then some (finiteCap n c (point (N:ℝ) p)) else none := by
  have ho := (ownerAtPrefix_rank_eight (N:ℝ) (pre p) (pre_length p) c).mpr hs
  refine ⟨ho,fun later => ?_⟩
  rw [selectedCap_append _ _ _ later (pre p) (pre_length p).ge]
  simp only [selectedCap,ho,point8_at_eight _ _ (pre_length p),point]

/-- The integer word's historical cell and the level actually read by
its own sixth ancestor. The original levelExponent includes the buffer. -/
def ThirdOwner (e : ℚ) (q : ℕ) (a ω : ℝ) (N : ℕ) (h : List ℕ) : Prop :=
  let d := bank e q a
  let R := current d ω (N:ℝ) (rosserAncestor 6 h)
  ∃ j∈HistoricalThirdCoarse.cells (d.e:ℝ) d.chi d.m,
    primeHistoryLogCoordinates (N:ℝ) 3 (rosserAncestor 3 h)∈logPrimeMeshCell 0 (19/96) d.m j ∧
    R.scalar=HistoricalThirdCoarse.levelExponent (d.e:ℝ) (HistoricalThirdCoarse.box d.m j) ∧ R.lower

/-- This predicate describes one occurrence of the unchanged original
canonical state and its actual causal data. It is supplied below. -/
def Supply (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N cap : ℕ)
    (w z : ℝ) (g : ℕ → ℝ) (p : Fin 8 → ℕ) (c : Cell) : Prop :=
  let h := pre p
  let s := canonicalState N cap w g p
  let d := bank e q a
  RealizedHistory e q a (N:ℝ) h c ∧ ThirdOwner e q a ω N h ∧
  current d ω (N:ℝ) (rosserAncestor 6 h)=prior d (N:ℝ) (rosserAncestor 6 h) ∧
  parent n e q a ω (N:ℝ) h=P4AOriginalFull87UnionHistory.actualParent n e q a (N:ℝ) h ∧
  P5OriginalCommonRefinedConstructor.lambda3 (oldBank e q a) (N:ℝ) (rosserAncestor 4 h)≤
    parent n e q a ω (N:ℝ) h ∧ parent n e q a ω (N:ℝ) h≤comparison c (point (N:ℝ) p) ∧
  s ∈ frontier B r n e q a ω N cap w z g ∧ ownerAtPrefix (N:ℝ) s.selectedPrefix=some c ∧
  (∀ later : List ℕ, selectedCap (width r) n (N:ℝ) (later++s.selectedPrefix) =
    if point (N:ℝ) p∈trim c (width r) then some (finiteCap n c (point (N:ℝ) p)) else none)

theorem supply_of_history (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (N cap : ℕ) (hN : 1<(N:ℝ)) (w z : ℝ)
    (hw : w≤(N:ℝ)^(53/13824:ℝ)) (hz : (N:ℝ)^VariableEnvelope.mu≤z) (hcap : z≤cap)
    (g : ℕ → ℝ) (p : Fin 8 → ℕ) (hp : ∀ i,(p i).Prime) (hd : ∀ i,¬p i∣N)
    (c : Cell) (hs : Source c (point (N:ℝ) p)) (hh : RealizedHistory e q a (N:ℝ) (pre p) c) :
    Supply B r n e q a ω N cap w z g p c := by
  let d := bank e q a
  let h := pre p
  have ho : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) (rosserAncestor 6 h) := by
    change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor 6 h))
    rw [rosserAncestor_nested 3 6 (by decide)]
    exact hh.2.1
  have hb := P4AOriginalNonsingletonEighthParent.ordered_cap_bounds n e q a ω (N:ℝ) he hN.le hω
    h (pre_length p) c hs hh.1 hh.2.1 hh.2.2.1
  have hr := root_on_old_owner (by exact_mod_cast he : 0≤(d.e:ℝ)) hN.le hω ho
  have hown : ThirdOwner e q a ω N h := by
    obtain ⟨j,hj,ht⟩ := hh.2.1.2
    have ha6 := (P4AOriginalFull87DataPolicy.active_ancestor d (N:ℝ) 6 (by decide) h).mpr
      (P4AOriginalFull87UnionHistory.source_active (pre_length p) hs hh)
    dsimp only [ThirdOwner]
    rw [hr]
    refine ⟨j,hj,ht,?_,ha6⟩
    change P5OriginalCommonRefinedConstructor.originalSeed d (N:ℝ) (rosserAncestor 6 h)=_
    rw [P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 6 (by decide),
      P5OriginalCommonRefinedConstructor.originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent,if_pos hh.2.1,
      HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
  exact ⟨hh,hown,hr,
    P4AOriginalR17EighthParent.parent_on_owner n e q a ω (N:ℝ) he hN.le hω h hh.2.1,
    hb.1,hb.2,canonical_of_history B r n e q a ω he hω N cap hN w z hw hz hcap g p hp hd c hs hh,
    eighth_owner r n N p c hs⟩

def Histories (r : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) : Prop :=
  ∀ (N : ℕ), 1<(N:ℝ) → ∀ p : Fin 8 → ℕ, (∀ i,0<p i) → ∀ c : Cell,
    Source c (point (N:ℝ) p) → point (N:ℝ) p∈core (width r) →
      RealizedHistory e q a (N:ℝ) (pre p) c

theorem cofinal_history (r : ℕ) :
    ∃ e0 : ℝ, 0<e0 ∧ ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ, 0<q0 ∧
    ∀ q≥q0, ∀ a : ℝ,a≤1/100 → Histories r e q a := by
  obtain ⟨e0,he0,H⟩ := exists_original_common_history (width r) (width_pos r)
  refine ⟨e0,he0,?_⟩
  intro e he he'
  obtain ⟨q0,hq,Hq⟩ := H e he he'
  refine ⟨q0,hq,?_⟩
  intro q hq' a ha N hN p hp c hs hc
  apply Hq q hq' a ha (N:ℝ) hN (pre p) (pre_length p) _ c hs hc
  intro x hx
  rw [pre_ofFn] at hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
  exact hp i

end
end ImbalancedChen.P1OriginalFinalEighthMemberSupply
