import ImbalancedChen.P4BOriginalHigherLowBins
import ImbalancedChen.P4AOriginalFiniteFallbackNaturalEndpoints
import ImbalancedChen.ActualDwellSelectedRemainder

namespace ImbalancedChen.P4BOriginalHigherLowKeySupport
noncomputable section
open Classical
open P4BOriginalCollisionWords (Params)
open P4BOriginalHigherLowBins (selected rest perm useRoot)
open P4BOriginalHigherLowRootRows (Row sum)
open P4BOriginalHigherLowRepresentative (g primeWord level row d cell t)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalMediumLowTriple (representative_raw)
open P4AOriginalFiniteFallbackSelectedMask (front)
open P4AOriginalFiniteFallbackPhysicalSelected (head)
open P4AOriginalFiniteFallbackNaturalEndpoints (tag upper)
open P4BUpperSelectedBoxCapacity (endpoint)
open P4AHeldTaggedCompilerSupport (J0)
open P4AOriginalFull87HistoryCore (width width_pos)

theorem natural (P : Params) (hN : 1<P.N) (he : 0<P.e) (hes : (P.e:ℝ)≤1/2048)
    (hstep : logPrimeMeshStep 0 (19/96) (d P).m≤(P.e:ℝ)/20) (ho : 0<P.omega)
    {J : List ℕ} (hJ : J∈P.words) (huse : useRoot P J) {z : ℝ}
    (hb : P.T*((J0 P.omega:ℝ)+1)≤z) :
    let H := actualPrimeFineLabelIntegerUpper P.N P.T
    let p := head J
    let b := row P J
    let M := level P J
    let S := selected b p
    let T := rest b p (J.drop 3)
    let s := sum b (t P J)
    1/2≤M ∧ M≤VariableEnvelope.cap-2*(P.e:ℝ) ∧
    (if b=.rescue then VariableEnvelope.A (t P J 0)≤M+11*(P.e:ℝ)/20 ∧
       M+2*(P.e:ℝ)≤VariableEnvelope.B (t P J 2)
     else M+(P.e:ℝ)/2≤VariableEnvelope.v s) ∧
    0≤s ∧ s≤1 ∧ (P.N:ℝ)^s≤endpoint H S ∧ endpoint H S≤(P.N:ℝ)^(s+z) ∧
    actualDwellSupport ((P.N:ℝ)^(M+z)) (J.map H) ∧
    actualDwellSupport (((P.N:ℝ)^(M+z))/endpoint H S) (T.map H) ∧
    (∀j∈J,0<H j) ∧
    (∀i : Fin 3,(H (p i):ℝ)≤(P.N:ℝ)^(t P J i+P.T)) ∧
    (∀j∈p 2::J.drop 3,(H j:ℝ)≤(P.N:ℝ)^(t P J 2+P.T)) := by
  let pr := ownerHead P J
  let xs := (primeWord P J).drop 3
  let b := row P J
  let M := level P J
  let t' := t P J
  let Q := (P.N:ℝ)^M
  let lab := tag P.N P.T
  have hr := (representative_raw P hN hJ).1
  have hw := (representative_raw P hN hJ).2
  change (primeWord P J).map lab=J at hw
  have hlen : 3≤(primeWord P J).length := by
    rw [P4BOriginalHigherLowRepresentative.length_word P hN hJ]
    exact (Finset.mem_filter.mp hJ).2
  have hv : primeWord P J=front pr xs := (P4BOriginalHigherLowRepresentative.front_eq _ hlen).symm
  have hlabel : J=front (lab ∘ pr) (xs.map lab) := by simpa only [hv,front,List.map_cons,Function.comp_apply] using hw.symm
  have head_eq : head J=lab ∘ pr := by rw [hlabel]; funext i; fin_cases i <;> rfl
  have drop_eq : J.drop 3=xs.map lab := by rw [hlabel]; rfl
  obtain ⟨_,_,ht⟩ := P4BOriginalHigherLowRepresentative.owner_data P hN he.le ho.le hJ
  have hl := huse.2.1
  have H := P4BOriginalHigherLowRootRows.gates (by exact_mod_cast he) hes hstep ht hl
    (P4BOriginalHigherLowRootRows.read_licensed (by exact_mod_cast he) ht)
  have lo := P4BOriginalHigherLowRootRows.half_le (by exact_mod_cast he) hes hstep ht hl
  have hi := P4AOriginalOrderedThirdTable.cap_on_ordered (by exact_mod_cast he.le) ht
  obtain ⟨pp,anti,_⟩ := P4AOriginalFiniteFallbackSelectedSupport.data_of_word hr pr xs hv
  have hn : (1:ℝ)<P.N := by exact_mod_cast hN
  have pos := zero_lt_one.trans hn
  have pw (i : Fin 3) : (P.N:ℝ)^(t' i)=(pr i:ℝ) := actualPrimeTupleLog_rpow hN _ pp i
  have full : actualDwellSupport Q (front pr xs) := by
    rw [←hv]
    exact huse.2.2
  have hrest : actualDwellSupport (Q/((selected b pr).prod:ℝ)) (rest b pr xs) := by
    cases h : b with
    | first => exact actualDwell_selected_prefix_budget [pr 0] _ (by simpa using pp 0) full
    | xy => exact actualDwell_selected_prefix_budget [pr 0,pr 1] _ (by simpa using Nat.mul_pos (pp 0) (pp 1)) full
    | xyz => exact actualDwell_selected_prefix_budget [pr 0,pr 1,pr 2] _ (by simp [pp]) full
    | rescue => simpa only [selected,rest,List.prod_nil,Nat.cast_one,div_one] using full
    | xz =>
      have s := Real.rpow_le_rpow_of_exponent_le hn.le (H.2.1 h)
      change (P.N:ℝ)^(t' 0+2*t' 1+t' 2)≤Q at s
      rw [two_mul,Real.rpow_add pos,Real.rpow_add pos,Real.rpow_add pos,pw,pw,pw] at s
      simpa [selected,rest] using actualDwell_selected_p1p3_budget _ _ _ xs (pp 0) (pp 2) full
        (by simpa only [pow_two] using s)
    | yz =>
      have s := Real.rpow_le_rpow_of_exponent_le hn.le (H.2.2 h)
      change (P.N:ℝ)^(2*t' 0+t' 1+t' 2)≤Q at s
      rw [two_mul,Real.rpow_add pos,Real.rpow_add pos,Real.rpow_add pos,pw,pw,pw] at s
      simpa [selected,rest] using actualDwell_selected_p2p3_budget _ _ _ xs (pp 1) (pp 2) full
        (by simpa only [pow_two] using s)
  have selpow : (P.N:ℝ)^sum b t'=((selected b pr).prod:ℝ) := by
    cases b <;> simp only [sum,selected,Real.rpow_add pos,pw,List.prod_cons,List.prod_nil,mul_one,
      Nat.cast_mul,Nat.cast_one,Real.rpow_zero,mul_assoc]
  have all := P4AOriginalFiniteFallbackNaturalEndpoints.general_endpoint_support P.m P.n P.N P.N (g P J)
    (width P.r) P.omega (P4AOriginalFull87RawChronology.cutoff P.N) P.T z (d P)
    (width_pos P.r) he.le hN ho P.T_pos hb hr _ _ _ hv (perm b pr xs) M _ selpow full hrest
  have hgeom := ht.2
  have nonneg : ∀i,0≤t' i := fun i => div_nonneg (Real.log_nonneg (by exact_mod_cast pp i))
    (Real.log_nonneg hn.le)
  have le1 : 0≤sum b t' ∧ sum b t'≤1 := by
    change t' 0≤25/128 at hl
    change 0≤t' 2 ∧ t' 2≤t' 1 ∧ t' 1≤t' 0 at hgeom
    cases b <;> dsimp only [sum] <;> constructor <;> linarith [nonneg 0,nonneg 1,nonneg 2,hgeom.2.1,hgeom.2.2]
  have maps : (selected b pr).map lab=selected b (lab ∘ pr) ∧
      (rest b pr xs).map lab=rest b (lab ∘ pr) (xs.map lab) := by cases b <;> exact ⟨rfl,rfl⟩
  let key := actualPrimeFineLabelIntegerUpper P.N P.T
  have einf (S : List ℕ) : endpoint (upper P.N P.T) S=endpoint key (S.map lab) := by
    simp [endpoint,upper,lab,key,List.map_map,Function.comp_def]
  have vall : (front pr xs).map (upper P.N P.T)=J.map key := by rw [←hw,hv,List.map_map]; rfl
  have tall : (rest b pr xs).map (upper P.N P.T)=(rest b (lab ∘ pr) (xs.map lab)).map key := by
    rw [←maps.2,List.map_map]; rfl
  obtain ⟨hs1,hs2,hfu,hre,hpos⟩ := all
  rw [einf,maps.1] at hs1 hs2 hre
  rw [vall] at hfu
  rw [tall] at hre
  have hsub := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe _ _ _ _
    (P4AUpperTaggedParityCompiler.rawSupport_subset_universe _ _ _ _ _ hr)).1
  rw [hv] at hsub
  have sort := (roughPrimeUniverse_pairwise_gt _ _ _ _).sublist hsub
  have key_le (q : ℕ) (hq : q∈front pr xs) : (key (lab q):ℝ)≤(P.N:ℝ)^P.T*q :=
    let h := mem_roughPrimeUniverse.mp (hsub.subset hq)
    (P4AOriginalFiniteFallbackNaturalEndpoints.endpoint_bounds hN P.T_pos h.2.1 h.2.2.1).2
  have hprime (i : Fin 3) : pr i∈front pr xs := by fin_cases i <;> simp [front]
  dsimp only
  rw [head_eq,drop_eq]
  refine ⟨lo,hi,H.1,le1.1,le1.2,hs1,hs2,hfu,hre,?_,?_,?_⟩
  · intro j hj
    rw [hlabel] at hj
    have : j∈(front pr xs).map lab := by simpa [front] using hj
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp this
    exact hpos q hq
  · intro i
    simpa only [Function.comp_apply,Real.rpow_add pos,pw,mul_comm] using key_le (pr i) (hprime i)
  · intro j hj
    simp only [Function.comp_apply,List.mem_cons,List.mem_map] at hj
    rcases hj with rfl|⟨q,hq,rfl⟩
    · simpa only [Real.rpow_add pos,pw,mul_comm] using key_le (pr 2) (hprime 2)
    · have hsort : (pr 2::xs).Pairwise (·>·) := (List.pairwise_cons.mp (List.pairwise_cons.mp sort).2).2
      have hh := (List.pairwise_cons.mp hsort).1 q hq
      have hq' : q∈front pr xs := by simp [front,hq]
      exact (key_le q hq').trans (by rw [Real.rpow_add pos,pw,mul_comm]; exact
        mul_le_mul_of_nonneg_left (by exact_mod_cast hh.le) (Real.rpow_nonneg pos.le _))

end
end ImbalancedChen.P4BOriginalHigherLowKeySupport
