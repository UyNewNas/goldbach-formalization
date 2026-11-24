import ImbalancedChen.P4AOrderedThirdPhysicalAtoms

namespace ImbalancedChen.P4AOrderedThirdActualRoughGeometry
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AUpperTaggedFirstPrefixDisagreement (decisionAt decisionAt_eq_prefix polarityAfter)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)
open P4AOriginalOrderedThirdFullPolicy (current policy base common five six eight)
open P4AOriginalOrderedThirdTable (capValue retained)
open HistoricalThirdCoarse (Cell firstStop)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (SecondRegion)

theorem every_decision {α : Type*} (P : Bool → List α → Bool) (xs pre : List α) (sgn : Bool)
    (h : FirstExitValidSelection P pre sgn xs) (k : ℕ) (hk : k<xs.length) :
    decisionAt P pre sgn xs k=true := by
  induction xs generalizing pre sgn k with
  | nil => simp at hk
  | cons a xs ih =>
    cases k with
    | zero => exact h.1
    | succ k => exact ih _ _ h.2 _ (by simpa using hk)

theorem high_raw_root (delta : ℝ) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    {N cap x : ℕ} (hN : 1<N) {omega : ℝ} (hw : 0≤omega)
    (hx : x∈rawSupport (policy delta n d omega N false) N cap ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ)))
    (hr : 3≤x.primeFactorsList.length) :
    ∃ j ∈ retained (d.e:ℝ) d.m,
      actualPrimeTupleLog N (canonicalPrefix 3 x) ∈ logPrimeMeshCell 0 (19/96) d.m j ∧
      (current d omega N x.primeFactorsList).scalar=capValue (d.e:ℝ) d.m j ∧
      capValue (d.e:ℝ) d.m j≤VariableEnvelope.cap-2*(d.e:ℝ) := by
  let f := policy delta n d omega N false
  let p := canonicalPrefix 3 x
  obtain ⟨hU,hv⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hx
  have ht := mem_actualPrimeBoxTuples_iff.mp (canonical_prefix_tail_data hU hr).1
  have hphys : p∈actualPrimeBoxTuples N (fun _ => (0:ℝ)) (fun _ => (19/96:ℝ)) := by
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    exact ⟨(ht i).1,(ht i).2.1,(Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) hw).trans
      (ht i).2.2.1,(ht i).2.2.2⟩
  have h0 : 0<x.primeFactorsList.reverse.length := by simpa using (show 0<x.primeFactorsList.length by omega)
  have hv0 := every_decision (oddFirstExitPolicy f) x.primeFactorsList.reverse [] true hv 0 h0
  rw [decisionAt_eq_prefix _ _ _ _ _ h0] at hv0
  have htake : x.primeFactorsList.reverse.take 1=[p 0] := by
    have H := congrArg (List.take 1) (canonicalPrefix_ofFn hr)
    simpa [p,List.ofFn_succ,List.take_take] using H.symm
  have hf : HistoricalThirdCoarse.firstStop (d.e:ℝ) d.m (N:ℝ) [p 0] := by
    have H : ordinaryRosserPrefixAdmissible false ((N:ℝ)^HistoricalThirdCoarse.initial (d.e:ℝ)) [p 0] ∧
        firstStop (d.e:ℝ) d.m (N:ℝ) [p 0] := by
      simpa [htake,f,policy,eight,six,five,common,base,firstExitDepthSplicePolicy,
        HistoricalThirdCoarse.initialPolicy,polarityAfter,oddFirstExitPolicy] using hv0
    exact H.2
  have ha := P4AOriginalOrderedThirdActualCoefficient.actual_triple (by exact_mod_cast he) hN p hphys
    (canonicalPrefix_strictAnti hU hr) (ht 2).2.2.1 hf
  obtain ⟨j,⟨ht',hj,hval,hcap⟩,_⟩ := ha
  have hhist : rosserAncestor 3 x.primeFactorsList=HistoricalThirdCoarse.P1ActualTuple.history p := by
    rw [← reversed_prefix x 3 hr]
    simp [p,HistoricalThirdCoarse.P1ActualTuple.history,List.ofFn_succ]
  exact ⟨j,hj,ht',by simpa only [current,hhist] using hval,hcap⟩

theorem active_high_witness (delta : ℝ) (n : ℕ) (d : OriginalData) (he : 0≤d.e)
    {N cap x : ℕ} (hN : 1<N) {omega tau : ℝ} (hw : 0≤omega)
    (hx : coefficient (policy delta n d omega N false) (fun _ => []) N cap ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ)) tau x≠0)
    (hr : 3≤x.primeFactorsList.length) :
    ∃ f∈rawSupport (policy delta n d omega N false) N cap ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ)),
      f∈cell (fun _ => []) N cap ((N:ℝ)^omega) ((N:ℝ)^(19/96:ℝ)) tau x ∧
      ∃ j∈retained (d.e:ℝ) d.m,
        actualPrimeTupleLog N (canonicalPrefix 3 f)∈logPrimeMeshCell 0 (19/96) d.m j ∧
        (current d omega N f.primeFactorsList).scalar=capValue (d.e:ℝ) d.m j ∧
        capValue (d.e:ℝ) d.m j≤VariableEnvelope.cap-2*(d.e:ℝ) := by
  obtain ⟨f,hf,hcell,_,_⟩ := active_has_raw_witness _ _ _ _ _ _ _ hx
  have hlen : 3≤f.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hcell]; exact hr
  exact ⟨f,hf,hcell,high_raw_root delta n d he hN hw hf hlen⟩

/-- Every odd decision on the true retained representative satisfies all of its
historical odd cubes at the named original-stage code, together with its actual
full product. The cutoff-zero evaluation here is only on this rough subword. -/
theorem retained_strict_cubes (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData)
    {N cap x : ℕ} (hN : 1<N) {omega v : ℝ} (hw : 0≤omega)
    (hx : x∈rawSupport (policy delta n d omega N false) N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (k : ℕ) (hk : k<x.primeFactorsList.length) (ho : polarityAfter true (k+1)=false) :
    let r := k+1
    let t := actualPrimeTupleLog N (canonicalPrefix r x)
    let s := P4AOrderedThirdRectangleRate.position r
    let A := (P4AOrderedThirdRectangleRate.code delta n d s).eval
      (P4AFull87ActualAffineDeletion.coords N _ x.primeFactorsList.reverse)
    (∑ i,t i)<A ∧ ∀ i : Fin r, Even i.val → P5Z.PresievedRoughSlotAffineGates.cube t i<A := by
  let f := P4AOrderedThirdRoughCutTransport.F delta n d 0 N
  have h0 := P4AOrderedThirdRoughCutTransport.support_cut delta n d (by omega : 1≤N) cap hw ((N:ℝ)^v)
  change x∈rawSupport (P4AOrderedThirdRoughCutTransport.F delta n d omega N) N cap _ _ at hx
  rw [h0] at hx
  obtain ⟨hU,hV⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hx
  have hlen : k<x.primeFactorsList.reverse.length := by simpa
  have H := every_decision (oddFirstExitPolicy f) _ [] true hV k hlen
  rw [decisionAt_eq_prefix _ _ _ _ _ hlen,ho,List.append_nil,← canonicalPrefix_ofFn (show k+1≤_ from hk),
    reversed_prefix x (k+1) hk] at H
  have hr := (P4AOrderedThirdRectangleRate.read delta hd n d N cap hN _ _ x hU (k+1) hk ho).2
  have hraw : f (rosserAncestor (k+1) x.primeFactorsList)=true := by simpa [oddFirstExitPolicy] using H
  rw [hr] at hraw
  apply (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN _ _
    (canonicalPrefix_pos hU hk) (canonicalPrefix_strictAnti hU hk)).mp
  rw [reversed_prefix x (k+1) hk]
  exact of_decide_eq_true hraw

/-- The native above-mu second replacement uses its exact ideal tent.
Its primitive exact unbuffered upper gap vanishes inside this region.
This asserts a fact about the primitive continuous comparison. -/
theorem above_mu_tent_touches {x : ℝ} (hlo : mu<x)
    (hhi : x<P5OriginalAboveMuThirdLowerPhysicalCoefficient.rho) :
    SecondRegion x mu ∧ v mu=VariableEnvelope.cap ∧
    ∀ eta : ℝ, 0<eta → ¬v mu+eta≤v mu := by
  have hv : v x=C x := v_eq_C hlo.le
  have hg : 2*v x-1<mu := by
    rw [hv]
    dsimp [C,mu] at *
    linarith
  refine ⟨⟨hlo,hhi,hg,hlo⟩,?_,fun _ hp => by linarith⟩
  rw [v_eq_A le_rfl]
  norm_num [A,mu,VariableEnvelope.cap]

end
end ImbalancedChen.P4AOrderedThirdActualRoughGeometry
