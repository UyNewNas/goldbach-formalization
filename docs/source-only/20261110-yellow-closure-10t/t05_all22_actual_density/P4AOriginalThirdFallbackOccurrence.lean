import ImbalancedChen.P4AOriginalNewFifthPaidDensity
import ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment

/-! The original G6 action changes the continuation after the third
prime. Record its genuine lower residual at the already corrected
second-stage frontier. Old and new admissions at rank three are
identical. The two fallback guards exclude each other on every hit. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackOccurrence
noncomputable section
open scoped Classical BigOperators
open P4AOriginalCausalHistory
open P4AOriginalRankThreeRestorationSource
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonThirdScreenedSource P5OriginalCommonThirdActualLowerSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P1Pair12RetainedSignedSource
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples)
open P5OriginalCommonFourthSourceLedger (signedTest_one_eq_polynomial)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalFull87RawChronology (thirdIncrement cutoff)
open P4AOriginalNewFifthUnion (data)

def active (d : OriginalData) (N : ℝ) (pre : List ℕ) : Prop :=
  selectedThird d N pre ∧ thirdGuard N pre

theorem unchanged_node (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (hsmall : (d.e : ℝ) ≤ 11/64000) (N : ℝ) (hN : 1 ≤ N)
    (b : Bool) (pre : List ℕ) (hl : pre.length = 3) :
    common3 d N b pre = secondStage d N b pre := by
  rw [common3_eq_screened3 d he hsmall N hN]
  simp [screened3,secondStage,hl]

theorem inactive_continuation (d : OriginalData) (he : 0 ≤ (d.e : ℝ))
    (hsmall : (d.e : ℝ) ≤ 11/64000) (N : ℝ) (hN : 1 ≤ N)
    (pre : List ℕ) (hl : 3 ≤ pre.length) (ha : ¬active d N pre)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (b : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (common3 d N) h T pre b mass remaining =
      signedTest (secondStage d N) h T pre b mass remaining := by
  induction remaining generalizing pre b mass with
  | nil => rfl
  | cons p ps ih =>
    have hl' : 3 < (p::pre).length := by simp; omega
    have ha' : ¬active d N (p::pre) := by
      simpa only [active,List.singleton_append] using
        (not_congr (and_congr (selectedThird_append d N [p] pre hl)
          (thirdGuard_later_history N [p] pre hl))).mpr ha
    have hp : common3 d N (!b) (p::pre) = secondStage d N (!b) (p::pre) := by
      rw [common3_eq_screened3 d he hsmall N hN]
      simp only [screened3, secondStage, if_neg (by omega : ¬(p::pre).length ≤ 2),
        if_neg (not_le_of_gt hl'),if_neg ha']
    simp only [signedTest,hp]
    rw [ih (pre := pre) (hl := hl) (ha := ha) (b := b) (mass := mass),
      ih (pre := p::pre) (hl := hl'.le) (ha := ha') (b := !b) (mass := mass*h p)]

def lower (Q : List ℕ → ℝ) (N : ℕ) (pre : List ℕ) : ℝ :=
  actualSmallRosserMinusDensity N N (pre.headD 0 : ℝ) (Q pre/(pre.prod : ℝ))

def saving (d : OriginalData) (N : ℕ) (pre : List ℕ) : ℝ :=
  if active d (N : ℝ) pre ∧ old3 d (N : ℝ) false pre = true then
    lower (thirdQ (N : ℝ)) N pre - lower (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ)) N pre
  else 0

theorem row (d : OriginalData) (he : 0 ≤ (d.e : ℝ)) (hsmall : (d.e : ℝ) ≤ 11/64000)
    (N : ℕ) (hN : 1 ≤ (N : ℝ)) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) weight (carrier N)) :
    admittedTest (secondStage d (N : ℝ)) weight (fun _ _ => 1) s -
      admittedTest (common3 d (N : ℝ)) weight (fun _ _ => 1) s =
    (s.selectedPrefix.map weight).prod * saving d N s.selectedPrefix := by
  obtain ⟨hlen,_,_,_,_,hsign,hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N N (cutoff N) s hs
  have hfalse : s.positive = false := by
    have hh := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1 : ℝ)
    cases h : evenListLength s.selectedPrefix
    · exact hsign.trans h
    · rw [h,hlen] at hh
      norm_num [signedTreeCoefficient] at hh
  have hnode := unchanged_node d he hsmall (N : ℝ) hN s.positive _ hlen
  by_cases ha : active d (N : ℝ) s.selectedPrefix
  · have hn2 : ¬activeSecond d (N : ℝ) s.selectedPrefix :=
      fun hh => second_third_disjoint (N : ℝ) _ (by omega) hh.2 ha.2
    have hOld : secondStage d (N : ℝ) s.positive s.selectedPrefix = old3 d (N : ℝ) false s.selectedPrefix := by
      simp only [secondStage, if_neg (by omega : ¬s.selectedPrefix.length ≤ 2), if_neg hn2, hfalse]
    by_cases ho : old3 d (N : ℝ) false s.selectedPrefix = true
    · let O := HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      let G := thirdQ (N : ℝ)
      have hself := rosserAncestor_self_of_length 3 s.selectedPrefix hlen
      have hlvl : O s.selectedPrefix = (N : ℝ)^originalSeed d (N : ℝ) s.selectedPrefix := by
        have h := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
          (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix
        change O (rosserAncestor 3 s.selectedPrefix) = _ at h
        rwa [hself] at h
      have hadO : ordinaryRosserPrefixAdmissible false (O s.selectedPrefix) s.selectedPrefix := by
        rw [hlvl]
        rw [old3_after_two d _ false _ (by omega)] at ho
        simpa [ordinaryParityRosserPolicy,oddFirstExitPolicy] using ho
      have hcap : O s.selectedPrefix ≤ G s.selectedPrefix := by
        rw [hlvl]
        have hlt := originalSeed_lt_third d he (N : ℝ) s.selectedPrefix (by omega) ha.1 ha.2
        simpa only [G,thirdQ,thirdExponent,hself] using Real.rpow_le_rpow_of_exponent_le hN hlt.le
      have hpost (Q : List ℕ → ℝ)
          (had : ordinaryRosserPrefixAdmissible false (Q s.selectedPrefix) s.selectedPrefix) :
          signedTest (frozenParityRosserPolicy false 3 Q) weight (fun _ _ => 1)
            s.selectedPrefix s.positive s.mass s.remaining = -s.mass * lower Q N s.selectedPrefix := by
        rw [signedTest_one_eq_polynomial,firstExitRetainedPolynomial_frozenParity_frontier_density false 3
          (by omega) (beforeThirdPolicy (old3 d (N : ℝ))) Q N N (cutoff N) s hs had]
        simp only [lower,actualFrozenFrontierDensityTerm,← hmass,
          signedTreeCoefficient_evenListLength_eq_negOnePow,ordinaryRosserResidualLower,hlen]
        norm_num
      simp only [admittedTest,hnode,hOld,if_pos ho]
      rw [secondStage_inactive_continuation d (N : ℝ) _ (by omega) hn2,old_third_continuation d _ _ (by omega),
        common_third_supported_continuation d he hsmall _ hN _ (by omega) ha.1 ha.2,
        hpost O hadO,hpost G (ordinaryRosserPrefixAdmissible_mono false _ hcap hadO)]
      rw [saving,if_pos ⟨ha,ho⟩]
      change -s.mass * lower O N s.selectedPrefix - -s.mass * lower G N s.selectedPrefix =
        (s.selectedPrefix.map weight).prod * (lower G N s.selectedPrefix - lower O N s.selectedPrefix)
      rw [← hmass]
      ring
    · simp only [admittedTest,hnode,hOld,if_neg ho,sub_self,saving,if_neg (fun h => ho h.2),mul_zero]
  · have hc := inactive_continuation d he hsmall (N : ℝ) hN _ (by omega) ha
      weight (fun _ _ => 1) s.positive s.mass s.remaining
    simp only [admittedTest,hnode,hc,sub_self,saving,if_neg (fun h => ha h.1),mul_zero]

/-- Sum only retained, genuine third changes. Before-third candidates
include old-rejected and second-restored histories; outside their own
selected third hit every such row cancels exactly. -/
theorem thirdChange_eq (d : OriginalData) (he : 0 ≤ (d.e : ℝ)) (hsmall : (d.e : ℝ) ≤ 11/64000)
    (N : ℕ) (hN : 1 ≤ (N : ℝ)) :
    -thirdChange d (N : ℝ) weight (fun _ _ => 1) (carrier N) =
      ∑ p ∈ candidateTuples d N, (∏ i, weight (p i)) * saving d N (List.ofFn p).reverse := by
  rw [P4AOriginalCausalHistory.thirdChange_eq d he hsmall (N : ℝ) hN,neg_sub]
  rw [signed_difference_before_third (old3 d (N : ℝ)) (common3 d (N : ℝ))
    (secondStage d (N : ℝ)) (common3_through_two d (N : ℝ))
    (fun b pre hl => by simp [secondStage,hl]) weight (fun _ _ => 1) [] (by simp) true 1 (carrier N)]
  rw [← firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 3 (beforeThirdPolicy (old3 d (N : ℝ)))
    weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _) (saving d N)]
  congr 1
  apply List.map_congr_left
  exact fun s hs => row d he hsmall N hN s hs

/-- Original G6 source at the enlarged fifth policy's own third root.
The fifth-data extension does not alter this earlier first/two/third dispatch. -/
theorem original_increment (e : ℚ) (q : ℕ) (a : ℝ) (he : 0 ≤ (e : ℝ))
    (hsmall : (e : ℝ) ≤ 11/64000) (N : ℕ) (hN : 1 ≤ (N : ℝ)) :
    -normalize N (thirdIncrement e q a N) =
      ∑ p ∈ candidateTuples (data e q a) N, (∏ i, weight (p i)) *
        normalize N (saving (data e q a) N (List.ofFn p).reverse) := by
  have h := congrArg (normalize N) (thirdChange_eq (data e q a) he hsmall N hN)
  have hs : thirdIncrement e q a N =
      thirdChange (data e q a) (N : ℝ) weight (fun _ _ => 1) (carrier N) := rfl
  dsimp only [normalize] at h ⊢
  rw [Finset.sum_mul,Finset.sum_div] at h
  calc
    _ = (-(thirdChange (data e q a) (N : ℝ) weight (fun _ _ => 1) (carrier N))) *
        Real.log (N : ℝ) / singularSeries N := by rw [hs]; ring
    _ = _ := h.trans (Finset.sum_congr rfl (fun _ _ => by ring))

end
end ImbalancedChen.P4AOriginalThirdFallbackOccurrence
