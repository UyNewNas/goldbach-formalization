import ImbalancedChen.P4AOriginalHistoricalFirstStop

/-! Exact old3-minus-initial occurrence sum. The rank-three frontier is
enumerated before admission. An inactive row cancels at its actual cap,
and a failed own cube contributes the canonical zero. -/
namespace ImbalancedChen.P4AOriginalHistoricalThirdOccurrence
noncomputable section
open Filter
open scoped Classical BigOperators
open HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (history history_log)
open P1ThirdFallbackSupport
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open P4AOriginalHistoricalFirstStop (initial_nonempty_continuation)
open P4AOriginalRankThreeRestorationSource
open P4ACatalogFiveCoarseWeightedPayment
open P4ACatalogFiveCoarseResidualUniformity (rawGatedMinus)
open P4AOriginalThirdFallbackAdmission (pre_eq self raw_eq)
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonThirdScreenedSource (selectedThird)
open P5OriginalCommonFourthSourceLedger (signedTest_one_eq_polynomial)
open P1Pair12RetainedSignedSource

abbrev base (d : OriginalData) (N : ℕ) := initialPolicy (d.e:ℝ) d.m (N:ℝ)
abbrev lit (d : OriginalData) (N : ℕ) (pre : List ℕ) :=
  supported (d.e:ℝ) d.chi d.m d.omega (N:ℝ) pre
abbrev primes (a : ℝ) (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 3 => a) (fun _ => thirdPrefixRho)

def charge (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  if lit d N (history p) then actualPrimeTupleOwnCubeMinus N N (initial (d.e:ℝ)) p -
    actualPrimeTupleOwnCubeMinus N N (originalSeed d (N:ℝ) (history p)) p else 0

theorem base_admitted (d : OriginalData) (N : ℕ) (s : FirstExitDepthState ℕ)
    (hl : s.selectedPrefix.length=3) (hb : s.positive=false) :
    admittedTest (base d N) weight (fun _ _ => 1) s =
      admittedOrdinary ((N:ℝ)^initial (d.e:ℝ)) N s := by
  have hn : s.selectedPrefix ≠ [] := by intro ha; simp [ha] at hl
  simp only [admittedTest,base,hb,initialPolicy,oddFirstExitPolicy,Bool.false_eq_true,if_false,
    decide_eq_true_eq,hl,show ¬(3:ℕ)=1 by decide,false_implies,and_true,admittedOrdinary]
  split_ifs
  · rw [signedTest_one_eq_polynomial,signedTest_one_eq_polynomial]
    exact P4AOriginalHistoricalFirstStop.initial_nonempty_continuation _ _ _ _ _ _ _ _ hn
  · rfl

theorem row (d : OriginalData) (he : 0<(d.e:ℝ)) (hsml : (d.e:ℝ)<(3/256:ℝ)/100)
    (hchi : d.chi<(d.e:ℝ)/10) {N : ℕ} (hN : 1<N) (s : FirstExitDepthState ℕ)
    (hs : s∈candidates d (N:ℝ) weight (carrier N)) :
    normalize N (admittedTest (old3 d (N:ℝ)) weight (fun _ _ => 1) s -
      admittedTest (base d N) weight (fun _ _ => 1) s) =
      (s.selectedPrefix.map weight).prod*charge d N (primeHistoryTuple 3 s.selectedPrefix) := by
  obtain ⟨hl,_,hprod,_,_,hb,hm⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N:ℝ))) N N (cutoff N) s hs
  let p := primeHistoryTuple 3 s.selectedPrefix
  have hp : s.selectedPrefix=history p := by simpa only [← pre_eq] using (primeHistoryTuple_reverse_ofFn hl).symm
  have hpos : ∀ i,0<p i := by
    rw [hp] at hprod
    simp only [history,List.prod_cons,List.prod_nil,Nat.cast_mul,Nat.cast_one,mul_one] at hprod
    intro i; fin_cases i <;> by_contra! h <;>
      simp [Nat.eq_zero_of_le_zero h] at hprod
  have hfalse : s.positive=false := by simpa [hp,history,evenListLength] using hb
  rw [old_admitted_eq_ordinary d N s hs,base_admitted d N s hl hfalse,← hm]
  change _ = s.mass*charge d N p
  by_cases hhit : lit d N (history p)
  · obtain ⟨rough,j,hj,ht⟩ := (supported_triple _ _ _ _ _ _ _ _).mp hhit
    let Q := rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix
    have hNr : (1:ℝ)<N := by exact_mod_cast hN
    have hc : (p 0:ℝ)^3 < Q := by
      dsimp only [Q]; rw [hp]
      exact rawLevel_first_cube_on_cell _ _ he hsml hchi _ _ _ hNr _ _ _ (hpos 0) rough j hj ht
    have hQ := rawLevel_triple_on_cell (d.e:ℝ) d.chi d.m d.omega (N:ℝ) _ _ _ rough j hj ht
    have hgeom := (mem_cells (d.e:ℝ) d.chi d.m j).mp hj
    have hceil := gamma_le_cap _ _ he.le hgeom.1 hgeom.2.1
    have hsmall : levelExponent (d.e:ℝ) (box d.m j) ≤ initial (d.e:ℝ) := by
      dsimp [levelExponent,initial,VariableEnvelope.extendedDistributionCap,VariableEnvelope.cap] at *; linarith
    have hbase : (p 0:ℝ)^3 < (N:ℝ)^initial (d.e:ℝ) := by
      dsimp only [Q] at hc; rw [hp,hQ] at hc
      exact hc.trans_le (Real.rpow_le_rpow_of_exponent_le hNr.le hsmall)
    rw [normalize_sub]
    unfold normalize
    rw [admittedOrdinary_normalized d N s hs p hp (hpos 2) _ hc,
      admittedOrdinary_normalized d N s hs p hp (hpos 2) _ hbase,charge,if_pos hhit,hp,
      raw_eq d N p]
    change -s.mass*actualPrimeTupleOwnCubeMinus N N _ p - -s.mass*actualPrimeTupleOwnCubeMinus N N _ p = _
    ring
  · rw [hp,rawLevel_fallback _ _ _ _ _ _ hhit,sub_self,charge,if_neg hhit,mul_zero]
    simp [normalize]

theorem source (d : OriginalData) (he : 0<(d.e:ℝ)) (hsml : (d.e:ℝ)<(3/256:ℝ)/100)
    (hchi : d.chi<(d.e:ℝ)/10) {N : ℕ} (hN : 1<N) :
    normalize N (rawRoot (old3 d (N:ℝ)) N-rawRoot (base d N) N) =
      ∑ p∈candidateTuples d N,(∏ i,weight (p i))*charge d N p := by
  let P := old3 d (N:ℝ)
  have hr (R : Bool → List ℕ → Bool) (hr : ∀ pre,R true pre=true) :
      signedTest R weight (fun _ _ => 1) [] true 1 (carrier N)=rawRoot R N := by
    rw [signedTest_one_eq_polynomial]
    exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained R hr N N 0 _
  rw [← hr P (policy_even _ _ _ _ _),← hr (base d N) (fun _ => rfl),
    signed_difference_before_third P (base d N) P
      (fun b pre hl => (policy_through_two _ _ _ _ _ b pre hl).symm)
      (fun _ _ _ => rfl) weight (fun _ _ => 1) [] (by simp) true 1 (carrier N)]
  have hmap (L : List (FirstExitDepthState ℕ)) (f : FirstExitDepthState ℕ → ℝ) :
      normalize N (L.map f).sum=(L.map (fun s => normalize N (f s))).sum := by
    induction L with
    | nil => simp [normalize]
    | cons s ss ih => simp only [List.map_cons,List.sum_cons,P5OriginalCommonPositivePresieve.normalize_add,ih]
  rw [hmap,← firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 3
    (beforeThirdPolicy P) weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _) (charge d N)]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact row d he hsml hchi hN s hs

def applied (d : OriginalData) (N : ℕ) (p : Fin 3 → ℕ) : ℝ :=
  if p∈candidateTuples d N then charge d N p else 0

theorem on_box (d : OriginalData) (he : 0<(d.e:ℝ)) (hsml : (d.e:ℝ)<(3/256:ℝ)/100)
    (hchi : d.chi<(d.e:ℝ)/10) {N : ℕ} (hN : 1<N) :
    normalize N (rawRoot (old3 d (N:ℝ)) N-rawRoot (base d N) N) =
      ∑ p∈primes d.omega N,(∏ i,weight (p i))*applied d N p := by
  rw [source d he hsml hchi hN]
  let C := candidateTuples d N
  let S := C.filter (fun p => lit d N (history p))
  have hsub : S ⊆ primes d.omega N := by
    intro p hp
    obtain ⟨hc,hh⟩ := Finset.mem_filter.mp hp
    have hp' := (mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ)))
      (carrier N) (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hc
    have hl := (HistoricalThirdCoarse.P1ActualTuple.active_iff_log hN d.omega p
      (fun i => (mem_roughPrimeUniverse_prime (hp'.2.1 i)).pos)).mp hh.1
    exact P4ACatalogFiveOmittedOrderPayment.candidate_cutoff_mem_box d d.omega N hN p hc hl
  symm
  calc
    _ = ∑ p∈S,(∏ i,weight (p i))*applied d N p := (Finset.sum_subset hsub (by
      intro p _ hn
      by_cases hp : p∈C
      · have hh : ¬lit d N (history p) := fun h => hn (Finset.mem_filter.mpr ⟨hp,h⟩)
        rw [applied,if_pos hp,charge,if_neg hh,mul_zero]
      · simp only [applied,if_neg hp,mul_zero])).symm
    _ = ∑ p∈S,(∏ i,weight (p i))*charge d N p := Finset.sum_congr rfl
      (fun p hp => by rw [applied,if_pos (Finset.mem_filter.mp hp).1])
    _ = _ := Finset.sum_subset (Finset.filter_subset _ _) (by
      intro p hp hn
      have hh : ¬lit d N (history p) := fun h => hn (Finset.mem_filter.mpr ⟨hp,h⟩)
      simp [charge,hh])

end
end ImbalancedChen.P4AOriginalHistoricalThirdOccurrence
