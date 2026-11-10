import ImbalancedChen.P4AOriginalFiniteFallbackRankReads

namespace ImbalancedChen.P4AOriginalFiniteFallbackWallRate
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackRange (Bounded)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AOrderedThirdRectangleRate (Stage index position)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport P4AUpperTaggedFirstPrefixDisagreement
open P4AUpperTaggedFrozenAdmissionCatalogue
open P4AFull87MarkedPrimePayment P4AFull87ActualAffineDeletion P4AFull87OrdinaryAdmissionDeletion
open P4AFull87PhysicalReserveFromRate (WallRate)
open P4AOrderedThirdPrefixDeletion (Family bank native_seen)
open P2CanonicalWallFullResidualPayment

abbrev Charts (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) :=
  Σ s : Stage, Family (code T delta n d s) (∅ : Finset ℝ)

def centresFor (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) (N J : ℕ) (k : Charts T delta n d) :=
  bank (code T delta n d k.1) (∅:Finset ℝ) N J k.2

theorem changed_seen (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    (N cap : ℕ) (hN : 2≤N) (omega v tau : ℝ) (hw : 0<omega) (hv : omega≤v) (ht : 0<tau)
    (tags : ℕ → List Bool) {x : ℕ} (hx : x∈universe N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (hc : changed (F T delta n D 0 N) tags N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau x) :
    ∃ i : Charts T delta n D, x∈covered N cap (J0 omega) omega v ((J0 omega:ℝ)*tau)
      (centresFor T delta n D N (J0 omega) i) := by
  let f := F T delta n D 0 N
  have hJ : x.primeFactorsList.length<J0 omega := by
    obtain ⟨u,hu⟩ := (changed_implies_crossing f tags _ _ _ _ _ hx hc).1
    obtain ⟨huc,hur⟩ := Finset.mem_inter.mp hu
    rw [← cell_rank_preserved _ _ _ _ _ _ huc]
    exact (P4AOriginalFiniteFallbackRange.raw_range T hT delta hd n D he 0 N cap hN omega _ hw hur).1
  obtain ⟨y,hy,_,_,k,hk,ho,hneq,_⟩ := changed_first_actual_odd_prefix f tags _ _ _ _ _ hx hc
  let r := k+1
  let s := position r
  have hr : r≤x.primeFactorsList.length := hk
  have hry : r≤y.primeFactorsList.length := by rw [cell_rank_preserved _ _ _ _ _ _ hy]; exact hr
  have rev (z : ℕ) (hz : r≤z.primeFactorsList.length) :
      (z.primeFactorsList.reverse.take r).reverse=rosserAncestor r z.primeFactorsList := by
    rw [← canonicalPrefix_ofFn hz,reversed_prefix z r hz]
  rw [rev x hr,rev y hry] at hneq
  have hx' := P4AOriginalFiniteFallbackRankReads.read T delta hd n D N cap (by omega) _ _ x hx r hr ho
  have hy' := P4AOriginalFiniteFallbackRankReads.read T delta hd n D N cap (by omega) _ _ y (Finset.mem_filter.mp hy).1 r hry ho
  have hflip : ¬(ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^((code T delta n D s).eval (coords N _ x.primeFactorsList.reverse))) (rosserAncestor r x.primeFactorsList) ↔
      ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^((code T delta n D s).eval (coords N _ y.primeFactorsList.reverse))) (rosserAncestor r y.primeFactorsList)) := by
    intro hh
    exact hneq (hx'.2.trans ((congrArg (fun P : Prop => decide P) (propext hh)).trans hy'.2.symm))
  obtain ⟨i,hi⟩ := native_seen (code T delta n D s) (∅:Finset ℝ) N cap _ (by omega) omega v tau hw hv ht
    tags hx hy hx'.1 hr (hr.trans hJ.le) hflip
  exact ⟨⟨s,i⟩,hi⟩

abbrev count (T : Bank) (delta : ℝ) (n : ℕ) (d : OriginalData) := Fintype.card (Charts T delta n d)

theorem rate (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0<delta) (n : ℕ) (D : OriginalData) (he : 0≤D.e)
    (tags : ℕ → ℕ → List Bool) :
    WallRate (count T delta n D) (F T delta n D 0) tags := by
  obtain ⟨K,E,hK,hE,hh⟩ := P4AFull87FiniteWallRate.exists_finite_rate (ι:=Charts T delta n D)
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog
  apply hh B hB N cap (by omega) hEven omega v tau hw hv hv1 ht.le h3 hlog (centresFor T delta n D N (J0 omega))
  intro x hx
  obtain ⟨hU,hc⟩ := Finset.mem_filter.mp hx
  exact changed_seen T hT delta hd n D he N cap hN omega v tau hw hv ht (tags N) hU hc

end
end ImbalancedChen.P4AOriginalFiniteFallbackWallRate
