import ImbalancedChen.P2OriginalLaterSixthJointTests

/-! The full signed arithmetic quotient is compared on the actual
updated fifth frontier. Every changed word in each of the eight stages
has an upper bound from its own genuine winning action. -/
namespace ImbalancedChen.P4AOriginalLaterSixthPointwise
noncomputable section
open Set VariableEnvelope
open scoped Classical BigOperators
open P2OriginalSixthSimplexMoments (Point)
open P2OriginalLaterSixthKernel (Piece action eval lower)
open P4AOriginalSixthLaterLiteral (stage)
open P4AOriginalSixthLaterSemantics (endpoint)
open P2OriginalLaterSixthStageMass (epoch)
open P2OriginalLaterSixthInnerTests (trim trim_region)
open P2OriginalLaterSixthJointTests (sum value)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalOrderedSixthStages (orderedLevel)
open P4AOriginalOrderedSixthSigned (admitted tupleResidual admitted_floor)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalSavedSixthHistoricalOwner (bank pre_log)
open P4AOriginalLaterSixthOccurrence (primes)
open P4AOriginalOrderedLaterChanged (changed_owner)
open Certificates.P2OriginalSixthElevenLogSemantics (S6)
open P2OriginalSixthMomentRow (cutoff cutoff_pos)
open P1GuardFrozenFiniteCapAlgebra (rounded rounded_error)
open P4AOriginalElevenProfileQuantization (profile_eq_reciprocals profile_quantization_lower)

/-- An additional simultaneously eligible action may increase the actual
new cap beyond this bought endpoint. The same upper-cube argument and
reciprocal bound apply to that genuinely realized maximum. -/
theorem profile_lower (n : ℕ) (P R M V : ℝ) (t : Point) (hP : cutoff≤P-S6 t)
    (hPR : P≤R) (hPM : P≤M) (hRV : R<V) (hV0 : 0≤V) (hVcap : V≤cap)
    (hnew : (rounded n V:ℝ)≤M) :
    value R V t≤value P M t+8*width n/cutoff^2 := by
  have hpos := cutoff_pos.trans_le hP
  have hwpos := width_pos n
  have hR := hpos.trans_le (sub_le_sub_right hPR _)
  have hV := hR.trans (sub_lt_sub_right hRV _)
  have hM := hpos.trans_le (sub_le_sub_right hPM _)
  by_cases hMV : M≤V
  · have hq := rounded_error n V hV0 hVcap
    have h := profile_quantization_lower P R M V cutoff (width n) t cutoff_pos hpos hPR
      (hP.trans (sub_le_sub_right hPM _)) hMV (by linarith only [hnew,hq.1])
    rw [profile_eq_reciprocals hR.ne' hV.ne',profile_eq_reciprocals hpos.ne' hM.ne'] at h
    dsimp only [value];linarith
  · have hR' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hpos (sub_le_sub_right hPR _)
    have hM' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hV (sub_le_sub_right (le_of_not_ge hMV) _)
    have hw : 0≤8*width n/cutoff^2 := by positivity
    dsimp only [value];linarith

theorem exists_test_lower (r : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<e → (e:ℝ)<E →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a omega : ℝ,a≤1/100 → omega≤a →
    ∀ N≥N0,Even N → ∀ p∈primes N,∀ k : Fin 8,
      let d := bank e q a
      let t := actualPrimeTupleLog N p
      sum r k t≤(if p∈admitted n d omega N N (P4AOriginalFull87RawChronology.cutoff N)
        then tupleResidual (k.val+2) n d omega N N p else 0)+(8*width n/cutoff^2+eta) := by
  obtain ⟨N1,h1,hclose⟩ := P4AOriginalSixthClosedQuotients.difference_close eta heta
  obtain ⟨N2,h2,hneg⟩ := P4AOriginalOrderedLaterChanged.whole_admitted_negative eta heta
  obtain ⟨n0,hcaps⟩ := P4AOriginalLaterSixthOccurrence.exists_caps (width_pos r)
  refine ⟨max N1 N2,h1.trans (le_max_left _ _),n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hq'⟩ := hcaps n hn
  refine ⟨E,hE,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hh⟩ := hq' e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa N hN hev p hp k
  let d := bank e q a
  let t := actualPrimeTupleLog N p
  let R := P4AOriginalOrderedThirdFullPolicy.current d omega (N:ℝ) (pre p)
  let P := orderedLevel (k.val+2) n d omega (N:ℝ) (pre p)
  let M := orderedLevel (k.val+3) n d omega (N:ℝ) (pre p)
  have hwpos := width_pos n
  have hN1 : 1<N := by have h := (le_max_left N1 N2).trans hN;omega
  have hw : 0≤8*width n/cutoff^2 := by positivity
  change sum r k t≤(if p∈admitted n d omega N N _ then tupleResidual (k.val+2) n d omega N N p else 0)+_
  by_cases hlive : ∃ i : Piece,epoch i=k ∧ t∈trim i (width r)
  · obtain ⟨i,hi,ht,htest⟩ := P2OriginalLaterSixthJointTests.charge hlive
    have hs := (trim_region (width_pos r) ht).1.2.1
    have hepoch : stage (action i)=k.val := congrArg Fin.val hi
    have hc := hh q hq a omega ha hwa N hN1 p hp i ht
    let V := endpoint (action i) t
    let L := eval (lower i) t
    have hprev : P≤L := by simpa only [←hepoch,P,L,t] using hc.previous
    have hn' : (rounded n V:ℝ)≤M := by simpa only [←hepoch,M,V,t] using hc.endpoint_floor
    have hPM : P<M := (hprev.trans_lt hc.strict).trans_le hn'
    obtain ⟨c,_,hc',hM⟩ := changed_owner k.val n R d (N:ℝ) (pre p) hPM
    rw [pre_log] at hc' hM
    obtain ⟨hx,hr,hl,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic c t hc'
    obtain ⟨hpr,_,_,hwedge,_⟩ := admitted_floor (k.val+2) n d omega N N _ hN1 p hc.admitted
    have hres : t 5≤P-S6 t := by
      change 2*(t 4-t 5)<P-S6 t-t 5 at hwedge
      have h45 := ho (show (4:Fin 6)<5 by decide)
      linarith
    have hM3 : M-S6 t≤3*t 5 := (sub_le_sub_right hM _).trans
      (P4AOriginalLaterSixthHistoryRows.source_margins c t hc').2.2.2.2.le
    have hlist := ((mem_firstExitAdmittedTuples_iff 6 _ _ p).mp hc.admitted).1
    have hcap := (mem_roughPrimeUniverse.mp (hlist.subset (List.mem_ofFn.mpr ⟨5,rfl⟩))).1
    have hc' := hclose N ((le_max_left _ _).trans hN) hev p (fun j=>(hpr j).pos) P M hl.le
      (hr.le.trans (by norm_num [P4AOriginalSixthClosedQuotients.high])) hres hPM.le hM3 N hcap
    obtain ⟨vl,vc⟩ := P4AOriginalLaterSixthPredecessor.endpoint_range (action i) hs
    have hRV : L<V := (P4AOriginalLaterSixthPredecessor.low_le_comparison i (trim_region (width_pos r) ht).1).trans_lt
      (P4AOriginalLaterSixthHistoryRows.source_margins _ _ hs).2.2.2.1
    have hprof := profile_lower n P L M V t (hl.le.trans hres) hprev hPM.le hRV vl vc hn'
    rw [if_pos hc.admitted]
    change sum r k t≤actualPrimeTupleInitialSaving N N P M p+_
    have ha' := (abs_lt.mp hc').1
    dsimp only [value,L,V] at hprof
    dsimp only [value] at htest
    linarith only [htest,hprof,ha']
  · rw [P2OriginalLaterSixthJointTests.zero_of_no_live hlive]
    split_ifs with hadm
    · have h := hneg N ((le_max_right _ _).trans hN) hev k.val n d omega N _ p hadm
      linarith only [h,hw]
    · linarith

end
end ImbalancedChen.P4AOriginalLaterSixthPointwise
