import ImbalancedChen.P1OriginalFinalEighthMemberSupply
import ImbalancedChen.P1OriginalFull87PrimeBoundary

/-! The reciprocal-prime tests are read on the actual occurrence list.
The absolute omission on the entire original arithmetic source is bounded
before the target, using its sharp prime limit and its retained lower ramp. -/
namespace ImbalancedChen.P1OriginalFinalEighthWeightedFrontier
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87SourceDictionary (Cell Point Source)
open P4AOriginalFull87StrictActionTrim (sourceSet trim trim_subset_source trim_subset_core)
open P4AOriginalFull87HistoryCore (width width_pos core)
open P4AOriginalFull87EighthKernelControl (cutoff)
open P4AOriginalFull87SourcePrimeTests (box test profile ramp testSum cellIntegral source_subset_box
  test_off_trim ramp_off_trim ramp_bounds)
open P4AOriginalFull87OrdinarySignedGain (weight point_eq_tuple_log)
open P4AOriginalFull87ActualGain (tuples)
open P4AOriginalFull87SevenCubeAdmission (pre pre_ofFn pre_length point)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87OwnedEighthSource (retainedOwner retainedOwner_some_iff)
open P1OriginalFinalEighthFrontier
open P1OriginalFinalEighthMemberSupply (Histories Supply canonical_of_history supply_of_history eighth_owner)
open P1OriginalFull87PrimeBoundary (charge sharp inner)

theorem owner_iff_trim (r N : ℕ) (p : Fin 8 → ℕ) (c : Cell) :
    retainedOwner (width r) (N:ℝ) (pre p)=some c ↔ actualPrimeTupleLog N p∈trim c (width r) := by
  rw [retainedOwner_some_iff,P4AOriginalFull87FiniteEighthPolicy.point8_at_eight _ _ (pre_length p)]
  change _ ∧ point (N:ℝ) p∈trim c (width r) ↔ _
  rw [point_eq_tuple_log]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  apply (P4AOriginalFull87SourceDispatch.ownerAtPrefix_rank_eight (N:ℝ) (pre p) (pre_length p) c).mpr
  change Source c (point (N:ℝ) p)
  rw [point_eq_tuple_log]
  exact trim_subset_source c (width_pos r) h

def received (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N cap : ℕ)
    (w z : ℝ) (p : Fin 8 → ℕ) (c : Cell) : Prop :=
  canonicalState N cap w weight p ∈ frontier B r n e q a ω N cap w z weight ∧
  retainedOwner (width r) (N:ℝ) (pre p)=some c

/-- Full-source arithmetic classification before the core is chosen. -/
theorem received_source_iff (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (N cap : ℕ) (hN : 1<(N:ℝ)) (w z : ℝ)
    (hw : w≤(N:ℝ)^cutoff) (hz : (N:ℝ)^mu≤z) (hcap : z≤cap)
    (p : Fin 8 → ℕ) (hp : ∀ i,(p i).Prime) (hd : ∀ i,¬p i∣N)
    (c : Cell) (hs : Source c (point (N:ℝ) p)) :
    let P := rule B r n e q a ω N
    received B r n e q a ω N cap w z p c ↔
      (P false [p 0]=true ∧ P false [p 2,p 1,p 0]=true ∧
       P false [p 4,p 3,p 2,p 1,p 0]=true ∧ P false [p 6,p 5,p 4,p 3,p 2,p 1,p 0]=true) ∧
      actualPrimeTupleLog N p∈trim c (width r) := by
  dsimp only
  rw [received,actual_source_iff B r n e q a ω N cap hN w z hw hz hcap weight p hp hd c hs,
    owner_iff_trim]

private theorem received_on_trim (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (H : Histories r e q a) (N cap : ℕ) (hN : 1<N) (w z : ℝ)
    (hw : w≤(N:ℝ)^cutoff) (hz : (N:ℝ)^mu≤z) (hcap : z≤cap)
    (p : Fin 8 → ℕ) (hp : p∈tuples N) (c : Cell) (ht : actualPrimeTupleLog N p∈trim c (width r)) :
    received B r n e q a ω N cap w z p c := by
  have hprime := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).1
  have hNr : 1<(N:ℝ) := by exact_mod_cast hN
  have ht' : point (N:ℝ) p∈trim c (width r) := by rwa [point_eq_tuple_log]
  have hs := trim_subset_source c (width_pos r) ht'
  have hh := H N hNr p (fun i => (hprime i).1.pos) c hs (trim_subset_core c (width r) ht')
  exact ⟨canonical_of_history B r n e q a ω he hω N cap hNr w z hw hz hcap weight p
    (fun i => (hprime i).1) (fun i => (hprime i).2) c hs hh,(owner_iff_trim r N p c).mpr ht⟩

/-- The sum retains occurrence multiplicity and the actual state mass,
including the target-deleted carrier and its original eighth owner. -/
def frontierTest (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N cap : ℕ)
    (w z : ℝ) (c : Cell) : ℝ :=
  ((frontier B r n e q a ω N cap w z weight).map fun s =>
    s.mass * (if retainedOwner (width r) (N:ℝ) s.selectedPrefix=some c then
      test r c (primeHistoryLogCoordinates (N:ℝ) 8 s.selectedPrefix) else 0)).sum

theorem frontier_test_eq (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (H : Histories r e q a) (N cap : ℕ) (hN : 1<N) (w z : ℝ)
    (hw : w≤(N:ℝ)^cutoff) (hz : (N:ℝ)^mu≤z) (hcap : z≤cap) (c : Cell) :
    frontierTest B r n e q a ω N cap w z c=testSum N r c := by
  let P := rule B r n e q a ω N
  let U := roughPrimeUniverse N cap w z
  let A := firstExitAdmittedTuples 8 P U
  let T := tuples N
  let K (p : Fin 8 → ℕ) := actualPrimeTupleLog N p∈trim c (width r)
  let f (h : List ℕ) := if retainedOwner (width r) (N:ℝ) h=some c then
    test r c (primeHistoryLogCoordinates (N:ℝ) 8 h) else 0
  have hset : A.filter K=T.filter K := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha,hk⟩
      have hprime := ((mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap
        8 P N cap w z hcap p).mp ha).2.1
      exact ⟨(mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
        ⟨fun i => ⟨(hprime i).1,(hprime i).2.1⟩,source_subset_box c (trim_subset_source c (width_pos r) hk)⟩,hk⟩
    · rintro ⟨ht,hk⟩
      exact ⟨(canonical_iff_admitted P N cap w z weight p).mp
        (received_on_trim B r n e q a ω he hω H N cap hN w z hw hz hcap p ht c hk).1,hk⟩
  have hf (p : Fin 8 → ℕ) : f (List.ofFn p).reverse =
      if K p then test r c (actualPrimeTupleLog N p) else 0 := by
    rw [←pre_ofFn p]
    simp only [f,owner_iff_trim,←point_eq_tuple_log,K,point]
  calc
    frontierTest B r n e q a ω N cap w z c =
        ((firstExitDepthFrontier 8 P weight [] true 1 U).map fun s =>
          (s.selectedPrefix.map weight).prod*f s.selectedPrefix).sum := by
            unfold frontierTest
            congr 1
            apply List.map_congr_left
            intro s hs
            rw [mem_firstExitDepthFrontier_mass_eq_selected_prod 8 P weight U s hs]
    _ = ∑ p∈A,(∏ i,weight (p i))*f (List.ofFn p).reverse :=
      firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 8 P weight U (roughPrimeUniverse_nodup N cap w z) f
    _ = ∑ p∈A.filter K,(∏ i,weight (p i))*test r c (actualPrimeTupleLog N p) := by
      rw [Finset.sum_filter]
      simp only [hf,mul_ite,mul_zero]
    _ = ∑ p∈T.filter K,(∏ i,weight (p i))*test r c (actualPrimeTupleLog N p) := by rw [hset]
    _ = testSum N r c := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hk : K p
      · rw [if_pos hk]
      · rw [if_neg hk,test_off_trim r c ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2 hk,mul_zero]

/-- Positive charge on every target-deleted source tuple not both present
and assigned its original upgrade. It includes true retained states where
the eighth override is inactive as well as words rejected at an odd gate. -/
def missed (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ) (N cap : ℕ)
    (w z : ℝ) (c : Cell) : ℝ :=
  ∑ p∈tuples N,(∏ i,weight (p i)) *
    (if received B r n e q a ω N cap w z p c then 0 else
      (sourceSet c).indicator (charge c) (actualPrimeTupleLog N p))

theorem missed_bound (B : Bank) (r n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
    (he : 0≤e) (hω : ω≤a) (H : Histories r e q a) (N cap : ℕ) (hN : 1<N) (w z : ℝ)
    (hw : w≤(N:ℝ)^cutoff) (hz : (N:ℝ)^mu≤z) (hcap : z≤cap) (c : Cell) :
    0≤missed B r n e q a ω N cap w z c ∧
    missed B r n e q a ω N cap w z c≤sharp N c-inner N r c := by
  have h0 (t : Point) : 0≤(sourceSet c).indicator (charge c) t := by
    by_cases hs : t∈sourceSet c
    · simpa only [indicator_of_mem hs] using P1OriginalFull87PrimeBoundary.charge_nonneg c t
    · simp only [indicator_of_notMem hs,le_refl]
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    apply mul_nonneg (actualPrimeBoxWeight_nonneg hp)
    split_ifs <;> first | exact le_rfl | exact h0 _
  · unfold missed sharp inner actualPrimeBoxTestSum
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    rw [←mul_sub]
    apply mul_le_mul_of_nonneg_left _ (actualPrimeBoxWeight_nonneg hp)
    let t := actualPrimeTupleLog N p
    have hb : t∈box := ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
    by_cases ht : t∈trim c (width r)
    · have hit := received_on_trim B r n e q a ω he hω H N cap hN w z hw hz hcap p hp c ht
      rw [if_pos hit,indicator_of_mem (trim_subset_source c (width_pos r) ht)]
      exact sub_nonneg.mpr (mul_le_of_le_one_right (P1OriginalFull87PrimeBoundary.charge_nonneg c t)
        (ramp_bounds r c t).2)
    · have miss : ¬received B r n e q a ω N cap w z p c :=
        fun h => ht ((owner_iff_trim r N p c).mp h.2)
      simp only [if_neg miss,ramp_off_trim r c hb ht,mul_zero,sub_zero,le_refl]

/-- The mesh, core, action trim, reciprocal-prime estimate and target
threshold are chosen once. The final upper bank, target, cut, positive
and ordinary presieve carriers, and occurrence weights can then vary. -/
theorem cofinal_final_membership (ε : ℝ) (hε : 0<ε) :
    ∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,4*width n<width r ∧
    ∃ e0 : ℝ,0<e0 ∧ ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧
    ∀ q≥q0,∀ a : ℝ,a≤1/100 → ∃ N0 : ℕ,2≤N0 ∧
    ∀ (B : Bank) (ω : ℝ),ω≤a → ∀ N≥N0,∀ (cap : ℕ) (w z : ℝ),
    w≤(N:ℝ)^cutoff → (N:ℝ)^mu≤z → z≤cap →
      (∀ (p : Fin 8 → ℕ), (∀ i,(p i).Prime) → (∀ i,¬p i∣N) → ∀ c : Cell,
        Source c (point (N:ℝ) p) → point (N:ℝ) p∈core (width r) →
        ∀ g : ℕ → ℝ,Supply B r n e q a ω N cap w z g p c) ∧
      (0≤∑ c : Cell,missed B r n e q a ω N cap w z c) ∧
      (∑ c : Cell,missed B r n e q a ω N cap w z c)<ε ∧
      (∑ c : Cell,cellIntegral c)-ε < ∑ c : Cell,frontierTest B r n e q a ω N cap w z c := by
  obtain ⟨r0,hr0⟩ := P1OriginalFull87PrimeBoundary.cofinal_boundary ε hε
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨N0,hN0,hprime⟩ := hr0 r hr
  obtain ⟨n0,hn⟩ := P4AOriginalFull87FiniteEighthCap.exists_uniform_cap_resolution (width r) (width_pos r)
  refine ⟨n0,?_⟩
  intro n hn'
  obtain ⟨e0,he0,hist⟩ := P1OriginalFinalEighthMemberSupply.cofinal_history r
  refine ⟨hn n hn',e0,he0,?_⟩
  intro e he he'
  obtain ⟨q0,hq0,Hq⟩ := hist e he he'
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha
  have H := Hq q hq a ha
  refine ⟨N0,hN0,?_⟩
  intro B ω hω N hN cap w z hw hz hcap
  have hN' : 1<N := hN0.trans hN
  have hNr : 1<(N:ℝ) := by exact_mod_cast hN'
  have hm := missed_bound B r n e q a ω he.le hω H N cap hN' w z hw hz hcap
  have hm' := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => (hm c).2)
  rw [Finset.sum_sub_distrib] at hm'
  refine ⟨?_,Finset.sum_nonneg (fun c _ => (hm c).1),hm'.trans_lt (hprime N hN).1,?_⟩
  · intro p hp hd c hs hc g
    exact supply_of_history B r n e q a ω he.le hω N cap hNr w z hw hz hcap g p hp hd c hs
      (H N hNr p (fun j => (hp j).pos) c hs hc)
  · simpa only [frontier_test_eq B r n e q a ω he.le hω H N cap hN' w z hw hz hcap] using (hprime N hN).2

/-- The single ordinary/positive arithmetic carrier of the published
finite fallback tree. The caller's late beta is used as given. -/
theorem cofinal_original_carriers (ε : ℝ) (hε : 0<ε) :
    ∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,4*width n<width r ∧
    ∃ e0 : ℝ,0<e0 ∧ ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧
    ∀ q≥q0,∀ a : ℝ,a≤1/100 → ∃ N0 : ℕ,2≤N0 ∧
    ∀ (B : Bank) (ν β : ℝ),0<ν → 0<β → β<1/8 → ν*β<1/1000 → ν*β^2≤a →
    ∀ N≥N0,∀ w : ℝ,w=0 ∨ w=(N:ℝ)^(ν*β^2) →
      let ω := ν*β^2
      let z := P4AOriginalFull87RawChronology.cutoff N
      (∀ (p : Fin 8 → ℕ), (∀ i,(p i).Prime) → (∀ i,¬p i∣N) → ∀ c : Cell,
        Source c (point (N:ℝ) p) → point (N:ℝ) p∈core (width r) →
        ∀ g : ℕ → ℝ,Supply B r n e q a ω N N w z g p c) ∧
      (0≤∑ c : Cell,missed B r n e q a ω N N w z c) ∧
      (∑ c : Cell,missed B r n e q a ω N N w z c)<ε ∧
      (∑ c : Cell,cellIntegral c)-ε < ∑ c : Cell,frontierTest B r n e q a ω N N w z c := by
  obtain ⟨r0,Hr⟩ := cofinal_final_membership ε hε
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,Hn⟩ := Hr r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨hwid,e0,he0,He⟩ := Hn n hn
  refine ⟨hwid,e0,he0,?_⟩
  intro e he he'
  obtain ⟨q0,hq,Hq⟩ := He e he he'
  refine ⟨q0,hq,?_⟩
  intro q hq' a ha
  obtain ⟨N0,h0,H⟩ := Hq q hq' a ha
  refine ⟨N0,h0,?_⟩
  intro B ν β hν hβ hβ8 hνβ hω N hN w hw
  have hNr : 1≤(N:ℝ) := by exact_mod_cast (show 1≤N by omega)
  have hsmall : ν*β^2≤cutoff := by
    calc
      ν*β^2=(ν*β)*β := by ring
      _ ≤ ν*β := mul_le_of_le_one_right (mul_pos hν hβ).le (hβ8.le.trans (by norm_num))
      _ ≤ cutoff := hνβ.le.trans (by norm_num [cutoff])
  have hlow : w≤(N:ℝ)^cutoff := by
    rcases hw with rfl|rfl
    · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
    · exact Real.rpow_le_rpow_of_exponent_le hNr hsmall
  have hz := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num [mu] : mu≤(19/96:ℝ))
  have hcap : (N:ℝ)^(19/96:ℝ)≤N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (19/96:ℝ)≤1)
  exact H B (ν*β^2) hω N hN N w _ hlow hz hcap

end
end ImbalancedChen.P1OriginalFinalEighthWeightedFrontier
