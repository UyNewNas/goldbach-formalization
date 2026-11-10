import ImbalancedChen.P4AOriginalOrderedSixthStages

/-! Exact signed quotient identity on the corrected whole-third fifth
frontier, including every admitted tuple outside all archived trims.
The strict fifth odd cube gives both the endpoint bound and a quantitative
ordering wedge for each of the eleven comparison levels. -/
namespace ImbalancedChen.P4AOriginalOrderedSixthSigned
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root base common)
open P4AOriginalOrderedSixthStages (orderedFifth orderedFifth_splice orderedLevel ownFifth ordered_zero policy level_mono)
open P4AOriginalSavedSixthFrontier (afterFour actual_frontier_admissible)
open P4AOriginalSavedSixthSigned (pre rank_six_density)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)
open Certificates.P2OriginalSixthElevenLogSemantics (H5 S6)

theorem common_even (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : common R d N true h=true := by
  have hb : base R d N true h=true := by
    by_cases hk : h.length≤2 <;>
      simp [base,hk,HistoricalThirdCoarse.initialPolicy,ordinaryParityRosserPolicy,oddFirstExitPolicy]
  simp only [common,hb,Bool.true_or]

theorem fifth_even (n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ) : orderedFifth n d omega N true h=true := by
  rw [orderedFifth_splice]
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 4 _ _
    (fun p => common_even _ d N p) (fun p => frozenParityRosserPolicy_upper_even 5 _ p) h

theorem even (m n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ) : policy m n d omega N true h=true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (fifth_even n d omega N) (fun p => frozenParityRosserPolicy_upper_even 6 _ p) h

def admitted (n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 6 (orderedFifth n d omega (N:ℝ)) (roughPrimeUniverse N cap 0 z)

def tupleResidual (m n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (p : Fin 6→ℕ) :=
  actualPrimeTupleInitialSaving N cap (orderedLevel m n d omega N (pre p))
    (orderedLevel (m+1) n d omega N (pre p)) p

theorem stage_admissible (m n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (weight' : ℕ→ℝ) (hN : 1≤(N:ℝ)) (s : FirstExitDepthState ℕ)
    (hs : s∈firstExitDepthFrontier 6 (orderedFifth n d omega (N:ℝ)) weight' [] true 1
      (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false ((N:ℝ)^orderedLevel m n d omega N s.selectedPrefix) s.selectedPrefix := by
  have hle := level_mono n (P4AOriginalOrderedThirdFullPolicy.current d omega N s.selectedPrefix) d N s.selectedPrefix
    (show 0≤m by omega)
  change orderedLevel 0 n d omega N s.selectedPrefix≤orderedLevel m n d omega N s.selectedPrefix at hle
  rw [ordered_zero] at hle
  apply ordinaryRosserPrefixAdmissible_mono false _ (Real.rpow_le_rpow_of_exponent_le hN hle)
  rw [orderedFifth_splice] at hs
  exact actual_frontier_admissible _ _ 6 (by omega) N cap w z weight' s hs

theorem frontier_floor (m n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (weight' : ℕ→ℝ) (hN : 1<N) (s : FirstExitDepthState ℕ)
    (hs : s∈firstExitDepthFrontier 6 (orderedFifth n d omega (N:ℝ)) weight' [] true 1
      (roughPrimeUniverse N cap w z))
    (p : Fin 6→ℕ) (hpre : pre p=s.selectedPrefix) (hprime : ∀ j,(p j).Prime) (ho : StrictAnti p) :
    let t := actualPrimeTupleLog N p
    let L := orderedLevel m n d omega N (pre p)
    H5 t<L ∧ 2*(t 4-t 5)<L-S6 t-t 5 ∧ (p 5:ℝ)<(N:ℝ)^L/((∏ j,p j:ℕ):ℝ) := by
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have ha := stage_admissible m n d omega N cap w z weight' hNr.le s hs
  rw [←hpre] at ha
  let L := orderedLevel m n d omega N (pre p)
  obtain ⟨hh,hw⟩ := P4AOriginalSixthResidualFloor.history_and_wedge N hN p L hprime ho ha
  exact ⟨hh,hw,P4AOriginalSixthResidualFloor.last_prime_lt_quotient p ((N:ℝ)^L) hprime ho ha⟩

theorem admitted_floor (m n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (z : ℝ)
    (hN : 1<N) (p : Fin 6→ℕ) (hp : p∈admitted n d omega N cap z) :
    let t := actualPrimeTupleLog N p
    let L := orderedLevel m n d omega N (pre p)
    (∀ j,(p j).Prime) ∧ StrictAnti p ∧ H5 t<L ∧ 2*(t 4-t 5)<L-S6 t-t 5 ∧
      (p 5:ℝ)<(N:ℝ)^L/((∏ j,p j:ℕ):ℝ) := by
  let S := orderedFifth n d omega (N:ℝ)
  let C := roughPrimeUniverse N cap 0 z
  have hlist := ((mem_firstExitAdmittedTuples_iff 6 S C p).mp hp).1
  have hprime (j : Fin 6) : (p j).Prime :=
    mem_roughPrimeUniverse_prime (hlist.subset (List.mem_ofFn.mpr ⟨j,rfl⟩))
  have ho : StrictAnti p := List.pairwise_ofFn.mp ((roughPrimeUniverse_pairwise_gt N cap 0 z).sublist hlist)
  have hm := (firstExitRootFrontier_admitted_tuple_perm 6 S weight C).mem_iff.mpr (List.mem_toFinset.mp hp)
  obtain ⟨s,hs,hval⟩ := List.mem_map.mp hm
  have hl := firstExitDepthFrontier_selected_length 6 S weight [] C true 1 (by simp) s hs
  have hpre : pre p=s.selectedPrefix := by rw [←hval]; exact primeHistoryTuple_reverse_ofFn hl
  exact ⟨hprime,ho,frontier_floor m n d omega N cap 0 z weight hN s hs p hpre hprime ho⟩

theorem signed_at_stage (k n : ℕ) (d : OriginalData) (omega : ℝ) (N cap : ℕ) (z : ℝ) (hN : 1≤(N:ℝ)) :
    normalize N (raw (policy k n d omega N) N cap 0 z-raw (policy (k+1) n d omega N) N cap 0 z) =
      ∑ p∈admitted n d omega N cap z,(∏ i,weight (p i))*tupleResidual k n d omega N cap p := by
  let S := orderedFifth n d omega (N:ℝ)
  let Q := fun h => (N:ℝ)^orderedLevel k n d omega N h
  let M := fun h => (N:ℝ)^orderedLevel (k+1) n d omega N h
  let carrier := roughPrimeUniverse N cap 0 z
  have hx := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 6 (by decide) S M Q N cap z (stage_admissible (k+1) n d omega N cap 0 z weight hN)
      (stage_admissible k n d omega N cap 0 z weight hN)
  change firstExitRetainedPolynomial (policy k n d omega N) _ _ _ _ _ -
    firstExitRetainedPolynomial (policy (k+1) n d omega N) _ _ _ _ _ = _ at hx
  rw [UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
       (even k n d omega N) N cap 0 z,
     UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _
       (even (k+1) n d omega N) N cap 0 z] at hx
  change raw _ N cap 0 z - raw _ N cap 0 z = _ at hx
  unfold normalize
  rw [hx]
  let states := firstExitDepthFrontier 6 S weight [] true 1 carrier
  let term := fun s : FirstExitDepthState ℕ =>
    actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix -
    actualFrozenFrontierDensityTerm false N cap M s.selectedPrefix
  have hscale (l : List (FirstExitDepthState ℕ)) :
      (l.map term).sum * Real.log (N:ℝ)/singularSeries N =
      (l.map (fun s => term s*Real.log (N:ℝ)/singularSeries N)).sum := by
    induction l with
    | nil => simp
    | cons s l ih => simp only [List.map_cons,List.sum_cons,add_mul,add_div,ih]
  change (states.map term).sum * _ / _ = _
  rw [hscale,←firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 6 S weight carrier
    (roughPrimeUniverse_nodup N cap 0 z) (tupleResidual k n d omega N cap)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  have hl := firstExitDepthFrontier_selected_length 6 S weight [] carrier true 1 (by simp) s hs
  have hp : pre (primeHistoryTuple 6 s.selectedPrefix)=s.selectedPrefix := primeHistoryTuple_reverse_ofFn hl
  dsimp only [term]
  rw [rank_six_density N cap Q _ hl,rank_six_density N cap M _ hl]
  simp only [tupleResidual,actualPrimeTupleInitialSaving,hp,primeHistoryTuple_last (k:=5) hl,
    primeHistoryTuple_prod hl,Q,M,weight]
  ring

end
end ImbalancedChen.P4AOriginalOrderedSixthSigned
