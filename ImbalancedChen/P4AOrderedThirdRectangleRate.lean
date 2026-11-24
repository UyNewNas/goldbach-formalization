import ImbalancedChen.P4AOrderedThirdRankReads

namespace ImbalancedChen.P4AOrderedThirdRectangleRate
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P1FiniteAffineDecisionProgram (Program)
open P4AOrderedThirdRankReads (firstP thirdP eighthP admit)
open P4AOrderedThirdStaticSixthPrograms (atFive atSix)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport P4AUpperTaggedFirstPrefixDisagreement
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AFull87MarkedPrimePayment P4AFull87ActualAffineDeletion P4AFull87OrdinaryAdmissionDeletion
open P4AOrderedThirdRoughCutTransport (F)
open P4AFull87PhysicalReserveFromRate (WallRate)
open P4AOrderedThirdPrefixDeletion (Family bank native_seen)
open P2CanonicalWallFullResidualPayment

inductive Stage where | first | third | fifth | sixth | eighth
  deriving DecidableEq, Fintype

def index : Stage → ℕ | .first => 0 | .third => 2 | .fifth => 4 | .sixth => 5 | .eighth => 7

def code (delta : ℝ) (n : ℕ) (d : OriginalData) : (s : Stage) → Program (index s+1)
  | .first => firstP d
  | .third => thirdP d
  | .fifth => atFive n d
  | .sixth => atSix n d
  | .eighth => eighthP delta n d

def position (r : ℕ) : Stage :=
  if r≤1 then .first else if r≤3 then .third else if r≤6 then .fifth else if r≤8 then .sixth else .eighth

abbrev Charts (delta : ℝ) (n : ℕ) (d : OriginalData) :=
  Σ s : Stage, Family (code delta n d s) (∅ : Finset ℝ)

def centresFor (delta : ℝ) (n : ℕ) (d : OriginalData) (N J : ℕ) (k : Charts delta n d) :=
  bank (code delta n d k.1) (∅:Finset ℝ) N J k.2

theorem read (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData) (N cap : ℕ) (hN : 1<N)
    (w z : ℝ) (x : ℕ) (hx : x∈universe N cap w z) (r : ℕ) (hr : r≤x.primeFactorsList.length)
    (ho : polarityAfter true r=false) :
    index (position r)+1≤r ∧ F delta n d 0 N (rosserAncestor r x.primeFactorsList)=
      admit N ((code delta n d (position r)).eval (coords N _ x.primeFactorsList.reverse))
        (rosserAncestor r x.primeFactorsList) := by
  by_cases h8 : 8<r
  · simp only [position,if_neg (by omega : ¬r≤1),if_neg (by omega : ¬r≤3),if_neg (by omega : ¬r≤6),
      if_neg (by omega : ¬r≤8),index,code]
    exact ⟨by omega,P4AOrderedThirdRankReads.read_eight delta hd n d N cap hN w z x hx hr h8⟩
  by_cases h6 : 6<r
  · simp only [position,if_neg (by omega : ¬r≤1),if_neg (by omega : ¬r≤3),if_neg (by omega : ¬r≤6),
      if_pos (by omega : r≤8),index,code]
    exact ⟨by omega,P4AOrderedThirdRankReads.read_six delta n d N cap hN w z x hx hr h6 (by omega)⟩
  by_cases h4 : 4<r
  · simp only [position,if_neg (by omega : ¬r≤1),if_neg (by omega : ¬r≤3),if_pos (by omega : r≤6),
      index,code]
    exact ⟨by omega,P4AOrderedThirdRankReads.read_five delta n d N cap hN w z x hx hr h4 (by omega)⟩
  have hr' : r=1 ∨ r=3 := by
    have hr4 : r≤4 := by omega
    interval_cases r <;> simp [polarityAfter] at ho ⊢
  rcases hr' with rfl|rfl
  · exact ⟨by decide,P4AOrderedThirdRankReads.read_one delta n d N cap hN w z x hx hr⟩
  · exact ⟨by decide,P4AOrderedThirdRankReads.read_three delta n d N cap hN w z x hx hr⟩

theorem changed_seen (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    (N cap : ℕ) (hN : 2≤N) (omega v tau : ℝ) (hw : 0<omega) (hv : omega≤v) (ht : 0<tau)
    (tags : ℕ → List Bool) {x : ℕ} (hx : x∈universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hc : changed (F delta n D 0 N) tags N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau x) :
    ∃ i : Charts delta n D, x∈covered N cap (J0 omega) omega v ((J0 omega:ℝ)*tau)
      (centresFor delta n D N (J0 omega) i) := by
  let f := F delta n D 0 N
  have hJ : x.primeFactorsList.length<J0 omega := by
    obtain ⟨u,hu⟩ := (changed_implies_crossing f tags _ _ _ _ _ hx hc).1
    obtain ⟨huc,hur⟩ := Finset.mem_inter.mp hu
    rw [← cell_rank_preserved _ _ _ _ _ _ huc]
    exact (P4AOrderedThirdGlobalRange.raw_range delta hd n D he 0 N cap hN omega _ hw hur).1
  obtain ⟨y,hy,_,_,k,hk,ho,hneq,_⟩ := changed_first_actual_odd_prefix f tags _ _ _ _ _ hx hc
  let r := k+1
  let s := position r
  have hr : r≤x.primeFactorsList.length := hk
  have hry : r≤y.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hy]; exact hr
  have rev (z : ℕ) (hz : r≤z.primeFactorsList.length) :
      (z.primeFactorsList.reverse.take r).reverse=rosserAncestor r z.primeFactorsList := by
    rw [← canonicalPrefix_ofFn hz,reversed_prefix z r hz]
  rw [rev x hr,rev y hry] at hneq
  have hx' := read delta hd n D N cap (by omega) _ _ x hx r hr ho
  have hy' := read delta hd n D N cap (by omega) _ _ y (Finset.mem_filter.mp hy).1 r hry ho
  have hflip : ¬(ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^((code delta n D s).eval (coords N _ x.primeFactorsList.reverse))) (rosserAncestor r x.primeFactorsList) ↔
      ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^((code delta n D s).eval (coords N _ y.primeFactorsList.reverse))) (rosserAncestor r y.primeFactorsList)) := by
    intro hh
    exact hneq (hx'.2.trans ((congrArg (fun P : Prop => decide P) (propext hh)).trans hy'.2.symm))
  obtain ⟨i,hi⟩ := native_seen (code delta n D s) (∅:Finset ℝ) N cap _ (by omega) omega v tau hw hv ht
    tags hx hy hx'.1 hr (hr.trans hJ.le) hflip
  exact ⟨⟨s,i⟩,hi⟩

abbrev count (delta : ℝ) (n : ℕ) (d : OriginalData) := Fintype.card (Charts delta n d)

theorem rate (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    (tags : ℕ → ℕ → List Bool) :
    WallRate (count delta n D) (F delta n D 0) tags := by
  obtain ⟨K,E,hK,hE,hh⟩ := P4AFull87FiniteWallRate.exists_finite_rate (ι:=Charts delta n D)
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  apply hh B hB N cap (by omega) hEven omega v tau hw hv hv1 ht.le h3 hlog (centresFor delta n D N (J0 omega))
  intro x hx
  obtain ⟨hU,hc⟩ := Finset.mem_filter.mp hx
  exact changed_seen delta hd n D he N cap hN omega v tau hw hv ht (tags N) hU hc

end
end ImbalancedChen.P4AOrderedThirdRectangleRate
