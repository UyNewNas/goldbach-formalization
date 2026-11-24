import ImbalancedChen.P4AFull87CompilerChangedPartition
import ImbalancedChen.P4ACommonPolicyTaggedCompiler

/-! Use the already defined historical tag on the original data. Its
common-third and old-fifth bits rule out early inherited disagreement
on the actual licensed policy. A residual word is necessarily outside
the active third cone, as is its opposite word. -/
namespace ImbalancedChen.P4AFull87HistoricalChangedSupport
noncomputable section
open scoped Classical BigOperators
open P4AFull87CompilerCapRead P4AFull87CompilerChangedPartition
open P4AUpperTaggedParityCompiler P4AUpperTaggedFirstPrefixDisagreement
open P4AOriginalFull87FiniteParentPolicy (active active_ancestor fifthPolicy fifth_inactive)
open P4AOriginalFull87LicensedSixthPolicy (policy sixthPolicy through_eight)
open P4AOriginalCompleteSixthChronology (data)
open P4ACommonPolicyTaggedCompiler (historicalTag stageTag canonicalHistory)
open P5OriginalCommonRefinedConstructor (common3 policy5)

abbrev suffix (P : Parameters) (N : ℕ) := historicalTag (data P.e P.q P.om) N

private theorem read_blocks {F G : ℕ → List Bool} (n : ℕ)
    (hF : ∀ x, (F x).length = n) (hG : ∀ x, (G x).length = n) :
    ∀ xs : List ℕ, xs.flatMap F = xs.flatMap G → ∀ r ∈ xs, F r = G r := by
  intro xs
  induction xs with
  | nil => simp
  | cons a xs ih =>
    intro h r hr
    change F a ++ xs.flatMap F = G a ++ xs.flatMap G at h
    rcases List.mem_cons.mp hr with hhead | htail
    · subst r
      have h' := congrArg (List.take n) h
      simpa only [List.take_left' (hF a),List.take_left' (hG a)] using h'
    · refine ih ?_ r htail
      have h' := congrArg (List.drop n) h
      simpa only [List.drop_left' (hF a),List.drop_left' (hG a)] using h'

private theorem parity (p : Bool) (xs : List ℕ) :
    polarityAfter p xs.length = if evenListLength xs then p else !p := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons,polarityAfter,ih,evenListLength]
    cases evenListLength xs <;> cases p <;> rfl

private theorem parity_read (xs : List ℕ) (r : ℕ) (hl : xs.length = r)
    (ho : polarityAfter true r = false) : evenListLength xs = false := by
  rw [← hl,parity] at ho
  cases h : evenListLength xs <;> simp_all

private theorem stage_eq (P : Parameters) (N : ℕ) {d f r : ℕ} (hr : r < 9)
    (ht : P.tags N (suffix P N) f = P.tags N (suffix P N) d) :
    stageTag (data P.e P.q P.om) N (rosserAncestor r f.primeFactorsList) =
    stageTag (data P.e P.q P.om) N (rosserAncestor r d.primeFactorsList) := by
  let K := Stage × (levels P.n P.e P.q : Type)
  have len (x : ℕ) : (bits P.delta P.n P.e P.q P.om (N : ℝ) x).length = Fintype.card K := by
    simp only [bits,List.length_ofFn,K]
  have hh := congrArg (List.drop (Fintype.card K)) ht
  simp only [Parameters.tags,tag,List.drop_left' (len f),List.drop_left' (len d)] at hh
  let block (x j : ℕ) := stageTag (data P.e P.q P.om) N (rosserAncestor j x.primeFactorsList)
  have hflat : (List.range 9).flatMap (block f) = (List.range 9).flatMap (block d) := hh
  exact read_blocks 5 (F := block f) (G := block d) (fun _ => rfl) (fun _ => rfl)
    _ hflat r (List.mem_range.mpr hr)

private theorem early_keep (P : Parameters) (N r d : ℕ) (hr : r ≤ d.primeFactorsList.length)
    (h6 : r ≤ 6) (hn : P.read N r d = none) :
    let pre := rosserAncestor r d.primeFactorsList
    P.keep N pre =
      if r ≤ 4 then common3 (data P.e P.q P.om) N false pre
      else policy5 (data P.e P.q P.om) N false pre := by
  let pre := rosserAncestor r d.primeFactorsList
  have hl : pre.length = r := by simp [pre,Nat.min_eq_left hr]
  change policy P.delta P.n P.e P.q P.om (N : ℝ) false pre = _
  rw [through_eight _ _ _ _ _ _ _ _ (by omega),
    sixthPolicy,firstExitDepthSplicePolicy,if_pos (hl.trans_le h6)]
  by_cases h4 : r ≤ 4
  · simp only [if_pos h4,fifthPolicy,firstExitDepthSplicePolicy,if_pos (hl.trans_le h4)]
  · have hn5 : ¬active P.e P.q P.om (N : ℝ) (rosserAncestor 5 d.primeFactorsList) := by
      intro ha
      simp [Parameters.read,atRank,h4,h6,readStage,ha] at hn
    have hpre : ¬active P.e P.q P.om (N : ℝ) pre := by
      intro ha
      exact hn5 ((active_ancestor _ _ _ _ 5 (by omega) _).mpr
        ((active_ancestor _ _ _ _ r (by omega) _).mp ha))
    simpa only [if_neg h4] using fifth_inactive P.n P.e P.q P.om (N : ℝ) false pre hpre

private theorem inactive_of_late_read (P : Parameters) (N r d : ℕ) (hr : 6 < r)
    (hn : P.read N r d = none) : ¬active P.e P.q P.om (N : ℝ) d.primeFactorsList := by
  intro ha
  have ha6 := (active_ancestor P.e P.q P.om (N : ℝ) 6 (by omega) d.primeFactorsList).mpr ha
  have h4 : ¬r ≤ 4 := by omega
  have h6 : ¬r ≤ 6 := by omega
  by_cases h8 : r ≤ 8
  · simp [Parameters.read,atRank,h4,h6,h8,readStage,ha6] at hn
  · cases he : P4AOriginalFull87FiniteEighthPolicy.selectedCap P.delta P.n (N : ℝ)
      (rosserAncestor 8 d.primeFactorsList) <;>
      simp [Parameters.read,atRank,h4,h6,h8,readStage,he,ha6] at hn

/-- For the concrete preexisting suffix both words of an unrepresented
first disagreement are inactive, and its actual rank is at least seven.
This includes the common3 OR and the inactive fifth fallback literally. -/
theorem inherited_late_inactive (P : Parameters) (hdelta : 0 < P.delta)
    (N cap : ℕ) (w z tau : ℝ) {d : ℕ}
    (hc : inheritedFirst P N cap (suffix P N) w z tau d) :
    ∃ f ∈ cell (P.tags N (suffix P N)) N cap w z tau d,
      ∃ k < d.primeFactorsList.length, 6 < k+1 ∧
      ¬active P.e P.q P.om (N : ℝ) d.primeFactorsList ∧
      ¬active P.e P.q P.om (N : ℝ) f.primeFactorsList ∧
      P.keep N (rosserAncestor (k+1) d.primeFactorsList) ≠
        P.keep N (rosserAncestor (k+1) f.primeFactorsList) := by
  obtain ⟨f,hf,k,hk,ho,hn,hdiff,_⟩ := hc
  let r := k+1
  have ht := cell_frozen_tag _ _ _ _ _ _ hf
  have heq := reads_eq_of_tag_eq hdelta P.n P.e P.q P.om (N : ℝ) (suffix P N) ht
  have hnf : P.read N r f = none := (congrArg (atRank r) heq).trans hn
  have hrd : r ≤ d.primeFactorsList.length := hk
  have hrf : r ≤ f.primeFactorsList.length := by
    rw [cell_rank_preserved _ _ _ _ _ _ hf]
    exact hrd
  have hl (x : ℕ) (hx : r ≤ x.primeFactorsList.length) :
      (rosserAncestor r x.primeFactorsList).length = r := by simp [Nat.min_eq_left hx]
  have hlate : 6 < r := by
    by_contra! h6
    have hb := stage_eq P N (show r < 9 by omega) ht
    have hdpar := parity_read _ r (hl d hrd) ho
    have hfpar := parity_read _ r (hl f hrf) ho
    have hD := early_keep P N r d hrd h6 hn
    have hF := early_keep P N r f hrf h6 hnf
    apply hdiff
    refine hD.trans (Eq.trans ?_ hF.symm)
    by_cases h4 : r ≤ 4
    · have hbit := congrArg (fun xs : List Bool => xs[1]?) hb
      change some (common3 _ _ _ _) = some (common3 _ _ _ _) at hbit
      simpa only [if_pos h4,hdpar,hfpar] using (Option.some.inj hbit).symm
    · have hbit := congrArg (fun xs : List Bool => xs[3]?) hb
      change some (policy5 _ _ _ _) = some (policy5 _ _ _ _) at hbit
      simpa only [if_neg h4,hdpar,hfpar] using (Option.some.inj hbit).symm
  exact ⟨f,hf,k,hk,hlate,inactive_of_late_read P N r d hlate hn,
    inactive_of_late_read P N r f hlate hnf,hdiff⟩

/-- Complete changed-modulus enclosure on the active source cone,
retaining every rough tail and both orientations of change. -/
theorem active_changed_in_catalogue (P : Parameters) (hdelta : 0 < P.delta)
    (N cap : ℕ) (hN : 2 ≤ N) (omega v tau : ℝ) (hw : 0 < omega) {d : ℕ}
    (hd : d ∈ universe N cap ((N : ℝ)^omega) ((N : ℝ)^v))
    (hc : changed (P.keep N) (P.tags N (suffix P N)) N cap ((N : ℝ)^omega) ((N : ℝ)^v) tau d)
    (ha : active P.e P.q P.om (N : ℝ) d.primeFactorsList) :
    d ∈ catalogue P N cap (suffix P N) omega v tau := by
  apply (changed_in_catalogue_or_inherited P hdelta N cap hN (suffix P N) omega v tau hw hd hc).resolve_right
  intro h
  obtain ⟨_,_,_,_,_,hinactive,_,_⟩ := inherited_late_inactive P hdelta N cap _ _ tau h
  exact hinactive ha

end
end ImbalancedChen.P4AFull87HistoricalChangedSupport
