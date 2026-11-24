import ImbalancedChen.P4AOriginalFiniteFallbackOwnCubeRows

namespace ImbalancedChen.P4AOriginalFiniteFallbackSignedSource
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFiniteFallbackOccurrence
open P4AOriginalFiniteFallbackOwnCubeRows (secondRow thirdRow)
open P4AFallbackCanonicalBanks (bank)
open P5OriginalCommonRefinedConstructor (OriginalData old3)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples)
open P4AOriginalRankThreeRestorationSource (candidates beforeThirdPolicy)
open P5OriginalCommonPositivePresieve (normalize normalize_add)
open HistoricalThirdCoarse.P1ActualTuple (history)
open P4AOriginalThirdFallbackAdmission (pre_eq)

def sum (d : OriginalData) (N : ℕ) (g : (Fin 3 → ℕ) → ℝ) :=
  ∑ p∈candidateTuples d N,(∏ i,weight (p i))*g p

private theorem sum_identity (B C : Bank) (d : OriginalData) (w : ℝ) (N : ℕ) (g : (Fin 3 → ℕ) → ℝ)
    (hrow : ∀ s∈candidates d N weight (carrier N),∀ p : Fin 3 → ℕ,s.selectedPrefix=history p →
      p∈candidateTuples d N → normalize N (signedNode B d w N s-signedNode C d w N s)=s.mass*g p) :
    normalize N (rawRoot (upper B d w N) N-rawRoot (upper C d w N) N)=sum d N g := by
  rw [difference]
  let X := candidates d N weight (carrier N)
  have H (xs : List (FirstExitDepthState ℕ)) (u : FirstExitDepthState ℕ → ℝ) :
      normalize N (xs.map u).sum=(xs.map (fun s => normalize N (u s))).sum := by
    induction xs with
    | nil => simp [normalize]
    | cons a as ih => simp only [List.map_cons,List.sum_cons,normalize_add,ih]
  rw [H,sum,←firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 3 (beforeThirdPolicy (old3 d N))
    weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _) g]
  congr 1
  apply List.map_congr_left
  intro s hs
  obtain ⟨hl,_,_,_,_,_,hm⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d N)) N N (cutoff N) s hs
  let p := primeHistoryTuple 3 s.selectedPrefix
  have hp : s.selectedPrefix=history p := by rw [←pre_eq p,primeHistoryTuple_reverse_ofFn hl]
  have hmem : p∈candidateTuples d N := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨s.selectedPrefix.reverse,?_,?_⟩
    · exact (firstExitRootFrontier_admitted_history_perm 3 (beforeThirdPolicy (old3 d N)) weight (carrier N)).mem_iff.mp
        (List.mem_map.mpr ⟨s,hs,rfl⟩)
    · simp only [List.reverse_reverse]; rfl
  rw [hrow s hs p hp hmem,hm]

theorem two_and_three (m : ℕ) (d : OriginalData) (he : 0<(d.e:ℝ)) (hs : (d.e:ℝ)≤1/384)
    (hm : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) (w : ℝ) (hw : w≤5/96)
    (N : ℕ) (hN : 1<N) :
    let B := bank m
    normalize N (rawRoot (P4AOrderedThirdArithmeticOccurrence.fresh d w N) N-
        rawRoot (upper (onlySecond B) d w N) N)=sum d N (secondRow m d w N) ∧
    normalize N (rawRoot (upper (onlySecond B) d w N) N-rawRoot (upper B d w N) N)=sum d N (thirdRow m d w N) := by
  dsimp only
  rw [←empty_eq (bank m) d w N]
  exact ⟨sum_identity _ _ _ _ _ _ (fun s H p hp hc =>
      (P4AOriginalFiniteFallbackOwnCubeRows.rows m d he hs hm w hw N hN s H p hp hc).1),
    sum_identity _ _ _ _ _ _ (fun s H p hp hc =>
      (P4AOriginalFiniteFallbackOwnCubeRows.rows m d he hs hm w hw N hN s H p hp hc).2)⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackSignedSource
