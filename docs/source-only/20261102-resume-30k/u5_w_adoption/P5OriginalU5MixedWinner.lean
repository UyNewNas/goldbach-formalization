import ImbalancedChen.P5OriginalU5SameQSeedEntrance
import ImbalancedChen.P2OriginalThirdWReceiver

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The entire original L5 first-three-slot source, including the genuine
variable pair root. The root is selected before the new slot; all later
ties keep that exact source. The four remaining alternatives have the
original order (triple, W, first/third, second/third). Their reduction from
the literal eight gated branches is proved on the FULL L5 domain.

This is an ideal source/winner theorem. It does not define an adopted
finite CapPlan, identify any candidate rho with the adopted rho, or prove
the h248/AP/integral suppliers. The native source form and every selected
complement square below are conclusions, not admission hypotheses.
-/
namespace ImbalancedChen.P5OriginalU5MixedWinner

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerWholeBoxBranchSelect (SourceForm)
open P2OriginalLowerAffineTieSelector (AffineBranch)

abbrev a : ℝ := Part5OriginalUpsilon5CausalDictionary.a
abbrev h : ℝ := Part5OriginalUpsilon5CausalDictionary.h

/-- Closed geometric domain; the actual prime selector supplies its strict
pair inequalities and rough primes supply z<a. No rescue crop is imposed. -/
def Domain (t u z : ℝ) : Prop :=
  a ≤ u ∧ u ≤ t ∧ t ≤ h ∧ 0 ≤ z ∧ z ≤ a

theorem domain_ordered {t u z : ℝ} (hd : Domain t u z) : Ordered t u z := by
  rcases hd with ⟨hu,hut,ht,hz,hza⟩
  exact ⟨hz,hza.trans hu,hut,by dsimp [h,Part5OriginalUpsilon5CausalDictionary.h,mu] at *; linarith⟩

def rootValue (t u : ℝ) : ℝ := Part5OriginalUpsilon5CausalDictionary.level u t

/-- All gates are still present in `original`. The two omitted singleton
and swapped-W entries cannot improve the independently selected root. -/
theorem original_eq_root_and_four {t u z : ℝ} (hd : Domain t u z) :
    original t u z = max (rootValue t u)
      (max (v (t+u+z)) (max (B z) (max (v (t+z)) (v (u+z))))) := by
  have hBa : B a ≤ B z := by dsimp [B]; linarith [hd.2.2.2.2]
  have hrest : B a ≤ max (v (t+u+z))
      (max (B z) (max (v (t+z)) (v (u+z)))) :=
    hBa.trans (le_max_of_le_right (le_max_left _ _))
  rw [original_eq_six (domain_ordered hd)]
  unfold rootValue Part5OriginalUpsilon5CausalDictionary.level
  rw [max_assoc, max_assoc, max_eq_right hrest]
  rfl

/-- The four literal entries removed before the fresh scan are already
bounded by the independently selected root, including the swapped W gate. -/
theorem old_entries_le_root {t u z : ℝ} (hd : Domain t u z) :
    v t≤rootValue t u ∧ v u≤rootValue t u ∧
      v (t+u)≤rootValue t u ∧ w t z u≤rootValue t u := by
  have ho := domain_ordered hd
  have ht := ho.2.2.2
  have hu := ho.2.2.1.trans ht
  have hz := ho.2.1.trans hu
  have hu0 : 0≤u := ho.1.trans ho.2.1
  have ht0 : 0≤t := hu0.trans ho.2.2.1
  have hfirst : v t≤rootValue t u := le_max_left _ _
  have hpair : v (t+u)≤rootValue t u := le_max_of_le_right (le_max_left _ _)
  have hBa : B a≤rootValue t u := le_max_of_le_right (le_max_right _ _)
  have hsecond : v u≤v t := by
    rw [v_eq_A hu,v_eq_A ht]
    dsimp [A]; linarith [ho.2.2.1]
  have hBu : B u≤B a := by dsimp [B]; linarith [hd.1]
  have hroot0 : 0≤rootValue t u := by
    have hA : 0≤A t := by dsimp [A]; linarith
    rw [←v_eq_A ht] at hA
    exact hA.trans hfirst
  refine ⟨hfirst,hsecond.trans hfirst,hpair,?_⟩
  rw [w,wInner_eq_B t hz hu0]
  unfold psi
  split_ifs
  · exact hBu.trans hBa
  · exact hroot0

private theorem strict_psi_comparison {base current val gate : ℝ}
    (hb : 0≤base) (hc : base≤current) (hg : base≤val → gate≤val) :
    (current<psi val gate ↔ current<val) := by
  by_cases hgate : gate≤val
  · simp only [psi,if_pos hgate]
  · have hval : val≤current := (le_of_not_ge (fun hh => hgate (hg hh))).trans hc
    simp only [psi,if_neg hgate,not_lt.mpr (hb.trans hc),not_lt.mpr hval]

/-- At every accumulator above the actual root, the raw gated sources
and their native simplified values have the SAME strict-improvement test.
Thus their gate removal cannot change a fresh-source tie decision. -/
theorem original_fresh_comparisons {t u z current : ℝ} (hd : Domain t u z)
    (hcurrent : rootValue t u≤current) :
    (current<w t u z ↔ current<B z) ∧
    (current<psi (v (t+z)) (t+2*u+z) ↔ current<v (t+z)) ∧
    (current<psi (v (u+z)) (2*t+u+z) ↔ current<v (u+z)) := by
  have ho := domain_ordered hd
  have ht0 := (ho.1.trans ho.2.1).trans ho.2.2.1
  have hv : v t=A t := v_eq_A ho.2.2.2
  have hv0 : 0≤v t := by rw [hv]; dsimp [A]; linarith
  have hc : v t≤current := (old_entries_le_root hd).1.trans hcurrent
  refine ⟨?_,?_,?_⟩
  · rw [w,wInner_eq_B t (ho.2.2.1.trans ho.2.2.2) ho.1]
    exact strict_psi_comparison hv0 hc (fun hh => by simpa only [←hv] using hh)
  · exact strict_psi_comparison hv0 hc (fun hh => by
      have hm := xz_gate_margin ho hh
      linarith)
  · exact strict_psi_comparison hv0 hc (fun hh => by
      have hm := yz_gate_margin ho hh
      linarith)

inductive Source where
  | first | firstSecond | rootW | allThree | thirdW | firstThird | secondThird
  deriving DecidableEq

def sourceValue (t u z : ℝ) : Source → ℝ
  | .first => v t
  | .firstSecond => v (t+u)
  | .rootW => B a
  | .allThree => v (t+u+z)
  | .thirdW => B z
  | .firstThird => v (t+z)
  | .secondThird => v (u+z)

def keepOrRaise (t u z : ℝ) (old next : Source) : Source :=
  if sourceValue t u z old < sourceValue t u z next then next else old

def scan (t u z : ℝ) (old : Source) : List Source → Source
  | [] => old
  | next::rest => scan t u z (keepOrRaise t u z old next) rest

theorem keepOrRaise_value (t u z : ℝ) (old next : Source) :
    sourceValue t u z (keepOrRaise t u z old next) =
      max (sourceValue t u z old) (sourceValue t u z next) := by
  unfold keepOrRaise
  split_ifs with hh
  · exact (max_eq_right hh.le).symm
  · exact (max_eq_left (le_of_not_gt hh)).symm

theorem scan_inherits (t u z : ℝ) (old : Source) (rest : List Source)
    (hle : ∀ s∈rest, sourceValue t u z s ≤ sourceValue t u z old) :
    scan t u z old rest = old := by
  induction rest generalizing old with
  | nil => rfl
  | cons next rest ih =>
      have hn := hle next (List.mem_cons_self next rest)
      have hk : keepOrRaise t u z old next = old := by
        simp only [keepOrRaise,if_neg (not_lt.mpr hn)]
      rw [scan,hk]
      exact ih old (fun s hs => hle s (List.mem_cons_of_mem next hs))

theorem scan_origin (t u z : ℝ) (old : Source) (rest : List Source) :
    scan t u z old rest = old ∨ scan t u z old rest ∈ rest := by
  induction rest generalizing old with
  | nil => exact Or.inl rfl
  | cons next rest ih =>
      change scan t u z (keepOrRaise t u z old next) rest=old ∨
        scan t u z (keepOrRaise t u z old next) rest∈next::rest
      rcases ih (keepOrRaise t u z old next) with he | hm
      · simp only [he]
        by_cases hc : sourceValue t u z old<sourceValue t u z next
        · exact Or.inr (by simp only [keepOrRaise,if_pos hc,List.mem_cons_self])
        · exact Or.inl (by simp only [keepOrRaise,if_neg hc])
      · exact Or.inr (List.mem_cons_of_mem next hm)

/-- Original root order: v(t), v(t+u), W(a). The third rough prime does
not occur in this function, so refinement cannot reselect the old root. -/
def rootSource (t u : ℝ) : Source := scan t u a .first [.firstSecond,.rootW]

def newSources : List Source := [.allThree,.thirdW,.firstThird,.secondThird]

def winner (t u z : ℝ) : Source := scan t u z (rootSource t u) newSources

theorem rootSource_value (t u z : ℝ) :
    sourceValue t u z (rootSource t u) = rootValue t u := by
  have hz (s : Source) (hs : s=.first ∨ s∈[Source.firstSecond,Source.rootW]) :
      sourceValue t u z s = sourceValue t u a s := by
    rcases hs with rfl | hs
    · rfl
    · simp only [List.mem_cons,List.mem_singleton] at hs
      rcases hs with rfl | rfl <;> rfl
  unfold rootSource
  rw [hz _ (scan_origin t u a .first [.firstSecond,.rootW])]
  simp only [scan,keepOrRaise_value,sourceValue]
  exact max_assoc _ _ _

theorem winner_value (t u z : ℝ) :
    sourceValue t u z (winner t u z) = max (rootValue t u)
      (max (v (t+u+z)) (max (B z) (max (v (t+z)) (v (u+z))))) := by
  unfold winner newSources
  simp only [scan,keepOrRaise_value,rootSource_value,sourceValue,max_assoc]

/-- Actual full maximum, derived from the original gated formula. -/
theorem winner_eq_original {t u z : ℝ} (hd : Domain t u z) :
    sourceValue t u z (winner t u z) = original t u z := by
  rw [winner_value,original_eq_root_and_four hd]

theorem source_le_original {t u z : ℝ} (hd : Domain t u z) (s : Source) :
    sourceValue t u z s ≤ original t u z := by
  rw [original_eq_root_and_four hd]
  have hroot : rootValue t u ≤ max (rootValue t u)
      (max (v (t+u+z)) (max (B z) (max (v (t+z)) (v (u+z))))) := le_max_left _ _
  cases s
  · exact (le_max_left _ _).trans hroot
  · exact (le_max_of_le_right (le_max_left _ _)).trans hroot
  · exact (le_max_of_le_right (le_max_right _ _)).trans hroot
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

/-- Equality is an inherited region, including ties with a genuinely
different new source. No proper-wall deletion is needed for this identity. -/
theorem winner_inherits_iff {t u z : ℝ} (hd : Domain t u z) :
    winner t u z = rootSource t u ↔ original t u z = rootValue t u := by
  constructor
  · intro he
    rw [←winner_eq_original hd,he,rootSource_value]
  · intro he
    apply scan_inherits
    intro s _
    rw [rootSource_value]
    exact (source_le_original hd s).trans he.le

def sourceMask : Source → Finset (Fin 5)
  | .first => {0}
  | .firstSecond => {0,1}
  | .rootW => ∅
  | .allThree => {0,1,2}
  | .thirdW => ∅
  | .firstThird => {0,2}
  | .secondThird => {1,2}

def selectedExponent (t u z : ℝ) : Source → ℝ
  | .first => t
  | .firstSecond => t+u
  | .rootW => 0
  | .allThree => t+u+z
  | .thirdW => 0
  | .firstThird => t+z
  | .secondThird => u+z

def isW : Source → Prop
  | .rootW => True
  | .thirdW => True
  | _ => False

/-- Root W retains the cutoff a; new W retains the actual first rough
prime. Neither is substituted for the other in the source form. -/
def sourceCeiling (z : ℝ) : Source → ℝ
  | .rootW => a
  | _ => z

def sourcePoint (t u z : ℝ) (s : Source) : Fin 5 → ℝ :=
  ![t,u,sourceCeiling z s,0,0]

def nativeForm (t u z : ℝ) (s : Source) : SourceForm :=
  if isW s then .wSlot 2 else
    if selectedExponent t u z s ≤ mu then .tentLeft (sourceMask s)
    else .tentRight (sourceMask s)

theorem native_mask (t u z : ℝ) (s : Source) :
    (nativeForm t u z s).supportMask = sourceMask s := by
  cases s <;> simp only [nativeForm,isW,if_true,if_false]
  all_goals first | rfl | split_ifs <;> rfl

theorem native_value (t u z : ℝ) (s : Source) :
    (nativeForm t u z s).affine.eval (sourcePoint t u z s) = sourceValue t u z s := by
  cases s <;> simp only [nativeForm,isW,selectedExponent,if_true,if_false,sourceValue]
  all_goals first
  | (simp [SourceForm.affine,AffineBranch.eval,sourcePoint,sourceCeiling,
      sourceValue,B,cap,Fin.sum_univ_succ] <;> ring)
  | (split_ifs with hs
     · rw [v_eq_A hs]
       norm_num [SourceForm.affine,AffineBranch.eval,sourceMask,sourcePoint,sourceCeiling,
         selectedExponent,A,Fin.sum_univ_succ] <;> ring
     · rw [v_eq_C (le_of_not_ge hs)]
       norm_num [SourceForm.affine,AffineBranch.eval,sourceMask,sourcePoint,sourceCeiling,
         selectedExponent,C,Fin.sum_univ_succ] <;> ring)

theorem winner_native_source {t u z : ℝ} (hd : Domain t u z) :
    (nativeForm t u z (winner t u z)).affine.eval
        (sourcePoint t u z (winner t u z)) = original t u z ∧
      (nativeForm t u z (winner t u z)).supportMask = sourceMask (winner t u z) := by
  exact ⟨(native_value t u z _).trans (winner_eq_original hd),native_mask t u z _⟩

theorem tent_source_value {t u z : ℝ} {s : Source} (hs : ¬isW s) :
    sourceValue t u z s = v (selectedExponent t u z s) := by
  cases s <;> simp_all [isW,sourceValue,selectedExponent]

/-- A W winner has its genuine psi gate, both inner minima, and retained
ceiling proved from maximality. No `WBoxCheck` or W-winner hypothesis is
used to establish the full winner itself. -/
theorem W_winner_original_gate {t u z : ℝ} (hd : Domain t u z)
    (hw : isW (winner t u z)) :
    let c := sourceCeiling z (winner t u z)
    0 ≤ c ∧ c ≤ a ∧ z ≤ c ∧
      sourceValue t u z (winner t u z) = B c ∧
      w t u c = B c := by
  have hOrd := domain_ordered hd
  have hv : v t = A t := v_eq_A hOrd.2.2.2
  have hgate : A t ≤ sourceValue t u z (winner t u z) := by
    rw [winner_eq_original hd,←hv]
    exact v_le_original hOrd
  have hu : u ≤ mu := hOrd.2.2.1.trans hOrd.2.2.2
  have ha : 0 ≤ a := by norm_num [a,Part5OriginalUpsilon5CausalDictionary.a]
  cases he : winner t u z <;> simp only [he,isW] at hw
  all_goals try contradiction
  · simp only [he,sourceCeiling,sourceValue] at hgate ⊢
    refine ⟨ha,le_refl _,hd.2.2.2.2,rfl,?_⟩
    rw [w,wInner_eq_B t hu ha,psi,if_pos hgate]
  · simp only [he,sourceCeiling,sourceValue] at hgate ⊢
    refine ⟨hd.2.2.2.1,hd.2.2.2.2,le_refl _,rfl,?_⟩
    rw [w,wInner_eq_B t hu hd.2.2.2.1,psi,if_pos hgate]

/-- The simplified selected pairs also retain their ORIGINAL psi gates.
Their gate is a conclusion of actual maximality, not an eligibility crop. -/
theorem pair_winner_original_gates {t u z : ℝ} (hd : Domain t u z) :
    (winner t u z=.firstThird →
      psi (v (t+z)) (t+2*u+z)=sourceValue t u z (winner t u z)) ∧
    (winner t u z=.secondThird →
      psi (v (u+z)) (2*t+u+z)=sourceValue t u z (winner t u z)) := by
  have ho := domain_ordered hd
  constructor
  · intro hs
    have hv : v t≤v (t+z) := by
      have hh := v_le_original ho
      rw [←winner_eq_original hd,hs] at hh
      exact hh
    have hm := xz_gate_margin ho hv
    have hg : t+2*u+z≤v (t+z) := by linarith
    rw [hs,sourceValue,psi,if_pos hg]
  · intro hs
    have hv : v t≤v (u+z) := by
      have hh := v_le_original ho
      rw [←winner_eq_original hd,hs] at hh
      exact hh
    have hm := yz_gate_margin ho hv
    have hg : 2*t+u+z≤v (u+z) := by linarith
    rw [hs,sourceValue,psi,if_pos hg]

def prefixSlots (mask : Finset (Fin 5)) (t u z : ℝ) : List Slot :=
  [⟨t,decide (0∈mask)⟩,⟨u,decide (1∈mask)⟩,⟨z,decide (2∈mask)⟩]

/-- A uniform reserve for EVERY mask of the actual first three slots,
not just its selected sum. This uses the full original L5 pair range. -/
theorem all_masks_full_and_complement {t u z b M : ℝ} (hd : Domain t u z)
    (hb : b ≤ 1/1000) (hM : A t ≤ M) (mask : Finset (Fin 5)) :
    SquareGates (M-2*b-1/32) 0 [t,u,z] ∧
      SquareGates (M-2*b-1/32) (selectedWord (prefixSlots mask t u z)).sum
        (remainingWord (prefixSlots mask t u z)) := by
  rcases hd with ⟨hu,hut,ht,hz,hza⟩
  have ha0 : (0:ℝ) ≤ a := by norm_num [a,Part5OriginalUpsilon5CausalDictionary.a]
  have hu0 := ha0.trans hu
  have ht0 := hu0.trans hut
  have hzu := hza.trans hu
  have hbound : 2*t+u+z ≤ M-2*b-1/32 := by
    have huh : u ≤ h := hut.trans ht
    dsimp [A,a,h,Part5OriginalUpsilon5CausalDictionary.a,
      Part5OriginalUpsilon5CausalDictionary.h] at *
    linarith
  constructor
  · simp only [SquareGates,zero_add]
    exact ⟨by linarith,by linarith,by linarith,True.intro⟩
  · by_cases h0 : (0:Fin 5)∈mask <;>
      by_cases h1 : (1:Fin 5)∈mask <;>
      by_cases h2 : (2:Fin 5)∈mask <;>
      simp only [prefixSlots,selectedWord,remainingWord,h0,h1,h2,
        decide_true,decide_false,Bool.true_eq_false,Bool.false_eq_true,
        if_true,if_false,List.sum_cons,List.sum_nil,add_zero,
        SquareGates,zero_add,and_true] <;>
      (repeat' constructor <;> linarith)

theorem winner_full_and_complement {t u z b : ℝ} (hd : Domain t u z)
    (hb : b ≤ 1/1000) :
    SquareGates (original t u z-2*b-1/32) 0 [t,u,z] ∧
      SquareGates (original t u z-2*b-1/32)
        (selectedWord (prefixSlots (nativeForm t u z (winner t u z)).supportMask t u z)).sum
        (remainingWord (prefixSlots (nativeForm t u z (winner t u z)).supportMask t u z)) := by
  have hOrd := domain_ordered hd
  have hv := v_le_original hOrd
  rw [v_eq_A hOrd.2.2.2] at hv
  exact all_masks_full_and_complement hd hb hv _

end
end ImbalancedChen.P5OriginalU5MixedWinner
