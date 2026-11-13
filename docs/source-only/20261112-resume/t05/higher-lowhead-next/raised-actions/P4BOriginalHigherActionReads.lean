import ImbalancedChen.P4BOriginalHigherActionMargins
import ImbalancedChen.P4AOriginalEarlyFiniteStages

/-! Read the last retained odd cap from the low arm of the actual compiled
program. All four ancestors below refer to the same least retained rough
modulus of the frozen labelled word. -/
namespace ImbalancedChen.P4BOriginalHigherActionReads
noncomputable section
open Classical
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowRepresentative (g d t level lastLevel primeWord cell owner_data length_word)
open P4BOriginalMediumLowTriple (representative_raw)
open P4AOriginalOrderedThirdFullPolicy (Root current current_ancestor cap5 cap6 third)
open P5OriginalCommonFourthSourceNavigation (firstCoordinate firstCoordinate_ancestor ancestor_first_coordinate guards_false_below_mu)
open P4AFull87ActualAffineDeletion (coords canonical_coords)
open P4AUpperTaggedFrozenAdmissionCatalogue (canonicalPrefix_pos)
open P4AOrderedThirdStaticSixthPrograms (atFive atSix)
open P4AOrderedThirdRectangleRate (position)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AFinitePPLastOddSupport (tested exponent)
open P1FiniteAffineDecisionProgram

abbrev raw (P : Params) (J : List ℕ) := (g P J).primeFactorsList
abbrev anc (P : Params) (J : List ℕ) (k : ℕ) := rosserAncestor k (raw P J)
abbrev point (P : Params) (J : List ℕ) (k : ℕ) := primeHistoryLogCoordinates (P.N:ℝ) k (anc P J k)
abbrev root (P : Params) (J : List ℕ) := current (d P) 0 (P.N:ℝ) (raw P J)
abbrev five (P : Params) (J : List ℕ) := cap5 (root P J) (d P) (P.N:ℝ) P.n (anc P J 5)
abbrev six (P : Params) (J : List ℕ) := cap6 (root P J) (d P) (P.N:ℝ) P.n (anc P J 6)
abbrev eight (P : Params) (J : List ℕ) := selectedCap (width P.r) P.n (P.N:ℝ) (raw P J)
abbrev stage (P : Params) (J : List ℕ) := position (tested (raw P J)).length
def reachedSix (P : Params) (J : List ℕ) := stage P J=.sixth ∨ stage P J=.eighth ∧ eight P J=none
def reachedFive (P : Params) (J : List ℕ) := stage P J=.fifth ∨ reachedSix P J ∧ six P J=five P J

theorem arity (P : Params) {J : List ℕ} {k : ℕ} (hN : 1<P.N) (hJ : J∈P.words) (hk : k≤J.length) :
    k≤(raw P J).length := by
  simpa only [primeWord,List.length_reverse] using hk.trans_eq (length_word P hN hJ).symm

theorem coord (P : Params) {J : List ℕ} {k : ℕ} (hk : k≤(raw P J).length) :
    coords P.N k (primeWord P J)=point P J k := by
  rw [canonical_coords P.N k (g P J) hk,P4AFull87SamePieceCapVariation.coord_ancestor hk P.N]

theorem triple (P : Params) {J : List ℕ} (hN : 1<P.N) (hJ : J∈P.words) : t P J=point P J 3 :=
  coord P (arity P hN hJ (Finset.mem_filter.mp hJ).2)

theorem positive (P : Params) {J : List ℕ} (hN : 1<P.N) (hJ : J∈P.words) :
    0<primeHistoryTuple 3 (anc P J 3) 2 := by
  have h3 := arity P hN hJ (Finset.mem_filter.mp hJ).2
  have hU := P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ (representative_raw P hN hJ).1
  rw [←P4AFull87OrdinaryAdmissionDeletion.reversed_prefix (g P J) 3 h3]
  simpa [primeHistoryTuple] using canonicalPrefix_pos hU h3 (2:Fin 3)

theorem root_at (P : Params) {J : List ℕ} (hN : 1<P.N) (he : 0≤P.e) (ho : 0≤P.omega)
    (hJ : J∈P.words) (hlo : t P J 0≤VariableEnvelope.mu) :
    (root P J).lower ∧ (root P J).scalar=level P J ∧ firstCoordinate (P.N:ℝ) (raw P J)≤VariableEnvelope.mu := by
  obtain ⟨hi,hm,_⟩ := owner_data P hN he ho hJ
  have h3 := arity P hN hJ (Finset.mem_filter.mp hJ).2
  have act : HistoricalThirdCoarse.active 0 (P.N:ℝ) (anc P J 3) := by
    refine ⟨by simp [anc,rosserAncestor_length,min_eq_left h3],?_⟩
    have hp : 1≤primeHistoryTuple 3 (anc P J 3) 2 := positive P hN hJ
    rw [Real.rpow_zero]; exact_mod_cast hp
  have H := triple P hN hJ
  have low : point P J 3 0≤VariableEnvelope.mu := H ▸ hlo
  have mem : point P J 3∈logPrimeMeshCell 0 (19/96) (d P).m (cell P J) := H ▸ hm
  refine ⟨⟨low,act,cell P J,hi,mem⟩,?_,?_⟩
  · change P4AOriginalOrderedThirdTable.rawExponent _ _ _ _ _=_
    rw [P4AOriginalOrderedThirdTable.rawExponent,if_pos act]
    exact P4AOriginalOrderedThirdTable.atPoint_on_cell hi mem
  · rw [←ancestor_first_coordinate (P.N:ℝ) 3 (by decide) (raw P J) h3]; exact low

theorem third_four (P : Params) {J : List ℕ} (h4 : 4≤(raw P J).length)
    (hl : firstCoordinate (P.N:ℝ) (raw P J)≤VariableEnvelope.mu) :
    third (root P J) (P.N:ℝ) (anc P J 4)=(root P J).scalar := by
  have len : (anc P J 4).length=4 := by simp [anc,rosserAncestor_length,min_eq_left h4]
  have h := guards_false_below_mu (P.N:ℝ) (anc P J 4) (by omega) (by
    rw [firstCoordinate_ancestor (P.N:ℝ) 4 (by decide)]; exact hl)
  rw [third,if_neg h.2,if_neg h.1,max_self]

/-- Numerically identify the actual selected read. Eighth `none` falls
back to six on the same word, also when the final rough rank exceeds nine. -/
theorem last (P : Params) {J : List ℕ} (hN : 1<P.N) (he : 0≤P.e) (ho : 0≤P.omega)
    (hJ : J∈P.words) (h5 : 5≤J.length) (hlo : t P J 0≤VariableEnvelope.mu) :
    (stage P J=.fifth ∧ lastLevel P J=five P J) ∨
      (6≤(raw P J).length ∧ reachedSix P J ∧ lastLevel P J=six P J) ∨
      ∃ a : ℚ,8≤(raw P J).length ∧ stage P J=.eighth ∧ eight P J=some a ∧ lastLevel P J=(a:ℝ) := by
  let p := raw P J
  let j := (tested p).length
  have hp5 : 5≤p.length := arity P hN hJ h5
  have hn : p≠[] := fun h => by simp [h] at hp5
  have cmp : j≤p.length ∧ p.length≤j+1 := by
    rcases (P4AFinitePPLastOddSupport.tested_spec hn).2.2 with eq|⟨a,eq⟩
    · have hh : p.length=j := congrArg List.length eq; omega
    · have hh : p.length=j+1 := by simpa only [List.length_cons] using congrArg List.length eq
      omega
  have j0 : ¬j≤1 := by omega
  have j3 : ¬j≤3 := by omega
  obtain ⟨hR,_,hl⟩ := root_at P hN he ho hJ hlo
  have hpos := positive P hN hJ
  have low (k : ℕ) (hk : 0<k) (hk' : k≤p.length) : ¬VariableEnvelope.mu<point P J k ⟨0,hk⟩ := by
    rw [ancestor_first_coordinate (P.N:ℝ) k hk p hk']; exact not_lt_of_ge hl
  have at5 : (atFive P.n (d P)).eval (point P J 5)=five P J := by
    have len : (anc P J 5).length=5 := by simp [anc,rosserAncestor_length,min_eq_left hp5]
    have hh := P4AOrderedThirdRankReads.five_exact P.n (d P) (P.N:ℝ) (anc P J 5) len (by
      rw [rosserAncestor_nested 3 5 (by decide)]; exact hpos)
    simpa only [current_ancestor (d P) 0 (P.N:ℝ) p 5 (by decide),if_pos hR] using hh
  have at6 (hs : 6≤p.length) : (atSix P.n (d P)).eval (point P J 6)=six P J := by
    have len : (anc P J 6).length=6 := by simp [anc,rosserAncestor_length,min_eq_left hs]
    have hh := P4AOrderedThirdRankReads.six_exact P.n (d P) (P.N:ℝ) (anc P J 6) len (by
      rw [rosserAncestor_nested 3 6 (by decide)]; exact hpos)
    simpa only [current_ancestor (d P) 0 (P.N:ℝ) p 6 (by decide),if_pos hR] using hh
  by_cases hj5 : j≤6
  · have st : position j=.fifth := by simp only [position,if_neg j0,if_neg j3,if_pos hj5]
    refine Or.inl ⟨st,?_⟩; unfold lastLevel exponent; rw [st]
    simpa only [P4AOriginalFiniteFallbackPrograms.code,P4AOriginalFiniteFallbackPrograms.switch_eval,
      P4AOrderedThirdRectangleRate.code,coord P hp5,if_neg (low 5 (by decide) hp5)] using at5
  · have hs : 6≤p.length := by omega
    by_cases hj6 : j≤8
    · have st : position j=.sixth := by simp only [position,if_neg j0,if_neg j3,if_neg hj5,if_pos hj6]
      refine Or.inr (Or.inl ⟨hs,Or.inl st,?_⟩); unfold lastLevel exponent; rw [st]
      simpa only [P4AOriginalFiniteFallbackPrograms.code,P4AOriginalFiniteFallbackPrograms.switch_eval,
        P4AOrderedThirdRectangleRate.code,coord P hs,if_neg (low 6 (by decide) hs)] using at6 hs
    · have h8 : 8≤p.length := by omega
      have st : position j=.eighth := by simp only [position,if_neg j0,if_neg j3,if_neg hj5,if_neg hj6]
      have len : (anc P J 8).length=8 := by simp [anc,rosserAncestor_length,min_eq_left h8]
      have sub : (fun i : Fin 6 => point P J 8 (i.castLE (by decide : 6≤8)))=point P J 6 := by
        funext i
        simpa only [point,anc,rosserAncestor_nested 6 8 (by decide)] using
          (primeHistoryLogCoordinates_ancestor (P.N:ℝ) len (by decide : 6≤8) i).symm
      have read : lastLevel P J=(match eight P J with | none => six P J | some a => (a:ℝ)) := by
        unfold lastLevel exponent; rw [st]
        simp only [P4AOriginalFiniteFallbackPrograms.code,P4AOriginalFiniteFallbackPrograms.switch_eval,
          P4AOrderedThirdRectangleRate.code,coord P h8,if_neg (low 8 (by decide) h8),P4AOrderedThirdRankReads.eighthP]
        rw [P4AOrderedThirdEighthSelectionProgram.finish_exact (width P.r) (width_pos P.r) P.n _ (P.N:ℝ) p h8]
        cases hh : eight P J with
        | none =>
          simp only [show selectedCap (width P.r) P.n (P.N:ℝ) p=none from hh,hh,Program.eval_pull]
          change (atSix P.n (d P)).eval (fun i : Fin 6 => point P J 8 (i.castLE (by decide : 6≤8)))=six P J
          rw [sub]; exact at6 hs
        | some a => simp only [show selectedCap (width P.r) P.n (P.N:ℝ) p=some a from hh,hh]
      cases hh : eight P J with
      | none => exact Or.inr (Or.inl ⟨hs,Or.inr ⟨st,hh⟩,by simpa only [hh] using read⟩)
      | some a => exact Or.inr (Or.inr ⟨a,h8,st,hh,by simpa only [hh] using read⟩)

end
end ImbalancedChen.P4BOriginalHigherActionReads
