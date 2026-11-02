import ImbalancedChen.P4ACatalogFiveHistoricalCoverage
import ImbalancedChen.P4AOriginalSecondResidualSupplier
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ordinary endpoint pair source is now derived from the SAME historical
rank-two parent and the SAME before-rank-three candidate occurrences as P.
The original second action is not redefined as this endpoint source.

The exact discrepancy has two independently defined summands: a selected
coarse-parent change, and an omitted endpoint change on unselected thirds.
The latter includes the disabled-small-third branch.  No bound or smallness
of either discrepancy is a premise, and no limiting source equality is
asserted.  The pair source still has the literal historical firstStop. Its
restriction to every cleared K/M compact trim is proved to be exactly the
M Finset. The untrimmed comparison and all summed error payment remain open.
-/

namespace ImbalancedChen.P4ACatalogFiveActualPairDecomposition
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonThirdScreenedSource P5OriginalCommonFourthSourceLedger
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalCausalHistory P4AOriginalRankThreeRestorationSource

private theorem sum_map_sub (L : List (FirstExitDepthState ℕ))
    (f g : FirstExitDepthState ℕ → ℝ) :
    (L.map (fun s => f s - g s)).sum = (L.map f).sum - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons s L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_map_neg (L : List (FirstExitDepthState ℕ))
    (f : FirstExitDepthState ℕ → ℝ) :
    (L.map (fun s => -f s)).sum = -(L.map f).sum := by
  induction L with
  | nil => simp
  | cons s L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- A comparison cap on the actual pair. This is NOT an actual-parent
replacement: both comparison trees retain the old first two decisions. -/
def pairCap (N : ℝ) (new : Bool) (pre : List ℕ) : ℝ :=
  N ^ v (primeHistoryLogCoordinates N 2 pre (if new then 1 else 0))

def endpointReplacement (d : OriginalData) (N : ℝ) (new : Bool)
    (b : Bool) (pre : List ℕ) : Bool :=
  if secondGuard N pre then frozenParityRosserPolicy false 2 (pairCap N new) b pre
  else old3 d N b pre

def endpointPolicy (d : OriginalData) (N : ℝ) (new : Bool) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 2 (old3 d N) (endpointReplacement d N new)

theorem endpointPolicy_through_two (d : OriginalData) (N : ℝ) (new b : Bool)
    (pre : List ℕ) (hl : pre.length ≤ 2) :
    endpointPolicy d N new b pre = old3 d N b pre := by
  simp only [endpointPolicy, firstExitDepthSplicePolicy, if_pos hl]

/-- Local policy equality is used only on extensions of a fixed ancestor.
This does not assume equality of the global historical and endpoint trees. -/
private theorem signedTest_congr_extensions
    (P Q : Bool → List ℕ → Bool) (base : List ℕ)
    (hPQ : ∀ later b, P b (later ++ base) = Q b (later ++ base))
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (b : Bool) (a : ℝ) (remaining : List ℕ) :
    signedTest P h T base b a remaining = signedTest Q h T base b a remaining := by
  have hrec (later : List ℕ) (b : Bool) (a : ℝ) (rest : List ℕ) :
      signedTest P h T (later ++ base) b a rest =
        signedTest Q h T (later ++ base) b a rest := by
    induction rest generalizing later b a with
    | nil => rfl
    | cons p ps ih =>
        have hp : P (!b) (p :: (later ++ base)) = Q (!b) (p :: (later ++ base)) :=
          hPQ (p :: later) (!b)
        simp only [signedTest, hp]
        rw [ih (later := later) (b := b) (a := a),
          ih (later := p :: later) (b := !b) (a := a * h p)]
  simpa only [List.nil_append] using hrec [] b a remaining

theorem endpointReplacement_continuation (d : OriginalData) (N : ℝ) (new : Bool)
    (base : List ℕ) (hl : 2 ≤ base.length)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (b : Bool) (a : ℝ) (rest : List ℕ) :
    signedTest (endpointReplacement d N new) h T base b a rest =
      if secondGuard N base then
        signedTest (ordinaryParityRosserPolicy false
          (pairCap N new (rosserAncestor 2 base))) h T base b a rest
      else signedTest (old3 d N) h T base b a rest := by
  by_cases hg : secondGuard N base
  · rw [if_pos hg]
    apply signedTest_congr_extensions
    intro later c
    have hg' := (secondGuard_append N later base hl).mpr hg
    simp only [endpointReplacement, if_pos hg', frozenParityRosserPolicy,
      ancestorFrozenPolicy, rosserAncestor_append 2 later base hl]
  · rw [if_neg hg]
    apply signedTest_congr_extensions
    intro later c
    have hg' : ¬secondGuard N (later ++ base) :=
      fun hh => hg ((secondGuard_append N later base hl).mp hh)
    simp only [endpointReplacement, if_neg hg']

theorem endpointPolicy_continuation (d : OriginalData) (N : ℝ) (new : Bool)
    (base : List ℕ) (hl : 2 ≤ base.length)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (b : Bool) (a : ℝ) (rest : List ℕ) :
    signedTest (endpointPolicy d N new) h T base b a rest =
      if secondGuard N base then
        signedTest (ordinaryParityRosserPolicy false
          (pairCap N new (rosserAncestor 2 base))) h T base b a rest
      else signedTest (old3 d N) h T base b a rest := by
  rw [endpointPolicy, signedTest_splice_after_rank 2 _ _ h T base rest b a hl]
  exact endpointReplacement_continuation d N new base hl h T b a rest

def endpointRow (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  admittedTest (endpointPolicy d N false) h T s -
    admittedTest (endpointPolicy d N true) h T s

def endpointSource (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (carrier : List ℕ) : ℝ :=
  signedTest (endpointPolicy d N false) h T [] true 1 carrier -
    signedTest (endpointPolicy d N true) h T [] true 1 carrier

/-- P's before-admission theorem is reused, not re-proved. Every candidate
occurrence remains present, including old-rejected/new-admitted triples. -/
theorem endpointSource_eq_candidate_sum (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    endpointSource d N h T carrier =
      ((candidates d N h carrier).map (endpointRow d N h T)).sum := by
  exact signed_difference_before_third (old3 d N)
    (endpointPolicy d N true) (endpointPolicy d N false)
    (endpointPolicy_through_two d N true) (endpointPolicy_through_two d N false)
    h T [] (by simp) true 1 carrier

def coarseRow (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  if activeSecond d N s.selectedPrefix then
    admittedTest (old3 d N) h T s - admittedTest (endpointPolicy d N false) h T s
  else 0

def omittedRow (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  if secondGuard N s.selectedPrefix ∧ ¬selectedThird d N s.selectedPrefix then
    endpointRow d N h T s else 0

private theorem admitted_endpoint_new_eq_second (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hl : 3 ≤ s.selectedPrefix.length) (ha : activeSecond d N s.selectedPrefix) :
    admittedTest (endpointPolicy d N true) h T s =
      admittedTest (secondStage d N) h T s := by
  have hcap : pairCap N true (rosserAncestor 2 s.selectedPrefix) =
      N ^ secondExponent N s.selectedPrefix := by
    simp only [pairCap, Bool.true_eq_true, if_true, secondExponent]
  have hnode : endpointPolicy d N true s.positive s.selectedPrefix =
      ordinaryParityRosserPolicy false (N ^ secondExponent N s.selectedPrefix)
        s.positive s.selectedPrefix := by
    simp only [endpointPolicy, firstExitDepthSplicePolicy,
      if_neg (by omega : ¬s.selectedPrefix.length ≤ 2), endpointReplacement,
      if_pos ha.2, frozenParityRosserPolicy, ancestorFrozenPolicy, hcap]
  rw [admittedTest, admittedTest, hnode,
    secondStage_supported_decision d N _ hl ha]
  by_cases hn : ordinaryParityRosserPolicy false (N ^ secondExponent N s.selectedPrefix)
      s.positive s.selectedPrefix = true
  · rw [if_pos hn, if_pos hn,
      endpointPolicy_continuation d N true _ (by omega) h T,
      if_pos ha.2, hcap,
      secondStage_supported_continuation d N _ hl ha h T]
  · simp only [if_neg hn]

private theorem endpointRow_zero_of_guard_false (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hl : 3 ≤ s.selectedPrefix.length) (hg : ¬secondGuard N s.selectedPrefix) :
    endpointRow d N h T s = 0 := by
  have hnode (new : Bool) : endpointPolicy d N new s.positive s.selectedPrefix =
      old3 d N s.positive s.selectedPrefix := by
    simp [endpointPolicy, firstExitDepthSplicePolicy, endpointReplacement, hg,
      show ¬s.selectedPrefix.length ≤ 2 by omega]
  simp only [endpointRow, admittedTest, hnode,
    endpointPolicy_continuation d N false _ (by omega) h T,
    endpointPolicy_continuation d N true _ (by omega) h T, if_neg hg, sub_self]

theorem actual_row_saving_eq_endpoint_add_coarse_sub_omitted
    (d : OriginalData) (N : ℝ) (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (s : FirstExitDepthState ℕ) (hl : s.selectedPrefix.length = 3) :
    -rowChange d N h T s = endpointRow d N h T s +
      coarseRow d N h T s - omittedRow d N h T s := by
  by_cases ha : activeSecond d N s.selectedPrefix
  · have hn := admitted_endpoint_new_eq_second d N h T s (by omega) ha
    have hnot : ¬(secondGuard N s.selectedPrefix ∧ ¬selectedThird d N s.selectedPrefix) :=
      fun hh => hh.2 ha.1
    rw [coarseRow, if_pos ha, omittedRow, if_neg hnot, endpointRow, hn, rowChange]
    ring
  · have hnode : secondStage d N s.positive s.selectedPrefix =
        old3 d N s.positive s.selectedPrefix := by
      simp only [secondStage, if_neg (by omega : ¬s.selectedPrefix.length ≤ 2), if_neg ha]
    have hc := secondStage_inactive_continuation d N _ (by omega) ha h T
      s.positive s.mass s.remaining
    have hz : rowChange d N h T s = 0 := by
      simp only [rowChange, admittedTest, hnode, hc, sub_self]
    rw [hz, coarseRow, if_neg ha]
    by_cases hg : secondGuard N s.selectedPrefix
    · have hs : ¬selectedThird d N s.selectedPrefix := fun hs => ha ⟨hs,hg⟩
      simp only [omittedRow, if_pos (And.intro hg hs), neg_zero, add_zero, sub_self]
    · rw [endpointRow_zero_of_guard_false d N h T s (by omega) hg]
      simp [omittedRow, hg]

/-- Exact actual-source comparison. The two error sums are NOT assumed
small; their signs and every full continuation are retained. -/
theorem second_saving_eq_endpoint_add_actual_discrepancies
    (d : OriginalData) (N : ℝ) (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (carrier : List ℕ) :
    -secondChange d N h T carrier = endpointSource d N h T carrier +
      ((candidates d N h carrier).map (coarseRow d N h T)).sum -
      ((candidates d N h carrier).map (omittedRow d N h T)).sum := by
  rw [secondChange_eq_candidate_sum, endpointSource_eq_candidate_sum]
  have hrows : ((candidates d N h carrier).map (fun s => -rowChange d N h T s)).sum =
      ((candidates d N h carrier).map (fun s => endpointRow d N h T s +
        coarseRow d N h T s - omittedRow d N h T s)).sum := by
    congr 1
    apply List.map_congr_left
    intro s hs
    exact actual_row_saving_eq_endpoint_add_coarse_sub_omitted d N h T s
      (firstExitDepthFrontier_selected_length 3 (beforeThirdPolicy (old3 d N)) h []
        carrier true 1 (by simp) s hs)
  simpa only [sum_map_neg, sum_map_sub, List.sum_map_add] using hrows

/-- The equation is also literally about P's retained-plus-restored source.
No old rank-three frontier is substituted for its candidate enumeration. -/
theorem retained_restored_saving_eq_endpoint_add_actual_discrepancies
    (d : OriginalData) (he : 0 ≤ (d.e : ℝ)) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    -((candidates d N h carrier).map (fun s => retainedTerm d N h T s +
      restoredTerm d N h T s)).sum = endpointSource d N h T carrier +
      ((candidates d N h carrier).map (coarseRow d N h T)).sum -
      ((candidates d N h carrier).map (omittedRow d N h T)).sum := by
  rw [← secondChange_eq_retained_and_restored d he N hN]
  exact second_saving_eq_endpoint_add_actual_discrepancies d N h T carrier

/-- On a disabled-small-third occurrence the actual change is zero, while
the entire endpoint change is charged to omission, not discarded. -/
theorem omittedRow_small_third (d : OriginalData) (N : ℝ)
    (p1 p2 p3 : ℕ) (hp : (p3 : ℝ) < N ^ d.omega)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (b : Bool) (a : ℝ) (rest : List ℕ)
    (hg : secondGuard N [p3,p2,p1]) :
    let s : FirstExitDepthState ℕ := ⟨[p3,p2,p1],b,a,rest⟩
    omittedRow d N h T s = endpointRow d N h T s ∧ coarseRow d N h T s = 0 := by
  dsimp only
  have hs := small_third_not_selected d N p1 p2 p3 hp
  simp [omittedRow, coarseRow, activeSecond, hg, hs]

/-! The endpoint expression, disintegrated at the actual rank TWO. -/

def pairEndpointRow (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (endpointReplacement d N false) h T
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest (endpointReplacement d N true) h T
      s.selectedPrefix s.positive s.mass s.remaining

theorem endpointSource_eq_historical_pair_sum (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    endpointSource d N h T carrier =
      ((firstExitDepthFrontier 2 (old3 d N) h [] true 1 carrier).map
        (pairEndpointRow d N h T)).sum := by
  unfold endpointSource endpointPolicy
  rw [signedTest_splice_eq_stopped_add_frontier,
    signedTest_splice_eq_stopped_add_frontier, add_sub_add_left_eq_sub]
  simp only [pairEndpointRow, sum_map_sub]

private theorem upper_pair_admissible_of_cube (Q : ℝ) (p1 p2 : ℕ)
    (hp2 : 0 < p2) (h21 : p2 < p1) (hQ : (p1 : ℝ)^3 < Q) :
    ordinaryRosserPrefixAdmissible false Q [p2,p1] := by
  have hf1 : ({p2,p1} : Finset ℕ).filter (fun q => p1 ≤ q) = {p1} := by
    ext q; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega
  have hf2 : ({p2,p1} : Finset ℕ).filter (fun q => p2 ≤ q) = {p2,p1} := by
    ext q; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]; omega
  have h1 : (1 : ℝ) ≤ p1 := by exact_mod_cast Nat.succ_le_of_lt (hp2.trans h21)
  have h2 : (p2 : ℝ) ≤ p1 := by exact_mod_cast h21.le
  have hp : (([p2,p1].prod : ℕ) : ℝ) < Q := by
    have hsq : (p1 : ℝ)^2 ≤ (p1 : ℝ)^3 := by
      nlinarith [mul_nonneg (sq_nonneg (p1 : ℝ)) (sub_nonneg.mpr h1)]
    have hprod : (p2 : ℝ) * p1 ≤ (p1 : ℝ)^2 :=
      by simpa only [pow_two] using mul_le_mul_of_nonneg_right h2
        (Nat.cast_nonneg (α := ℝ) p1)
    simpa only [List.prod_cons, List.prod_nil, mul_one, Nat.cast_mul] using
      hprod.trans_lt (hsq.trans_lt hQ)
  refine ⟨hp, ?_⟩
  change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet Q {p2,p1}
  intro q hq hodd
  rcases Finset.mem_insert.mp hq with rfl | hq
  · rw [hf2] at hodd
    norm_num [h21.ne] at hodd
  · have hq1 := Finset.mem_singleton.mp hq
    subst q
    rw [hf1]
    simpa only [Finset.prod_singleton, pow_succ, mul_comm] using hQ

private theorem actual_pair_endpoint_admissible (d : OriginalData) (N cap : ℕ)
    (hN : 1 < N) (z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 2 (old3 d (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (hg : secondGuard (N : ℝ) s.selectedPrefix) (new : Bool) :
    ordinaryRosserPrefixAdmissible false (pairCap (N : ℝ) new s.selectedPrefix)
      s.selectedPrefix := by
  obtain ⟨hlen, hsort, hP, _, _, _, _⟩ :=
    actualPrimeFrontier_geometry 2 (by omega) (old3 d (N : ℝ)) N cap z s hs
  obtain ⟨p2,p1,hpre⟩ := List.length_eq_two.mp hlen
  have h21 : p2 < p1 := by simpa [hpre] using hsort
  have hp2 : 0 < p2 := by
    by_contra hh
    have hz : p2 = 0 := by omega
    simp [hpre, hz] at hP
  have hp1 : 0 < p1 := hp2.trans h21
  have hself := rosserAncestor_self_of_length 2 s.selectedPrefix hlen
  have hregion : SecondRegion
      (Real.log (p1 : ℝ) / Real.log (N : ℝ))
      (Real.log (p2 : ℝ) / Real.log (N : ℝ)) := by
    simpa [secondGuard, hself, hpre, primeHistoryLogCoordinates, primeHistoryTuple] using hg
  have hcube := above_mu_old_cap_gt_cube hregion.1 hregion.2.1
  have hnew := new_cap_gt_old hregion.1 hregion.2.2.1 hregion.2.2.2
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (Real.log (p1 : ℝ) / Real.log (N : ℝ)) = p1 := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hNr) (by exact_mod_cast hp1)).mp
    exact div_mul_cancel₀ _ (Real.log_pos hNr).ne'
  have hcubePow : (p1 : ℝ)^3 < (N : ℝ) ^
      v (Real.log (p1 : ℝ) / Real.log (N : ℝ)) := by
    have hh := (Real.rpow_lt_rpow_left_iff hNr).mpr hcube
    rw [mul_comm (3 : ℝ), Real.rpow_mul (zero_lt_one.trans hNr).le,
      hpow, Real.rpow_natCast] at hh
    exact hh
  rw [hpre]
  apply upper_pair_admissible_of_cube _ p1 p2 hp2 h21
  cases new with
  | false => simpa [pairCap, hpre, primeHistoryLogCoordinates, primeHistoryTuple] using hcubePow
  | true =>
      have hh := (Real.rpow_lt_rpow_left_iff hNr).mpr hnew
      simpa [pairCap, hpre, primeHistoryLogCoordinates, primeHistoryTuple] using hcubePow.trans hh

def pairResidualRow (d : OriginalData) (N cap : ℕ) (s : FirstExitDepthState ℕ) : ℝ :=
  if secondGuard (N : ℝ) s.selectedPrefix then s.mass *
    (actualSmallRosserPlusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
      (pairCap (N : ℝ) false s.selectedPrefix / (s.selectedPrefix.prod : ℝ)) -
     actualSmallRosserPlusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
      (pairCap (N : ℝ) true s.selectedPrefix / (s.selectedPrefix.prod : ℝ)))
  else 0

/-- No prefix-admission licence is assumed: the original second guard pays
both endpoint cubes on the real prime pair. The residual is UPPER at rank2. -/
theorem pairEndpointRow_eq_actual_upper_residual (d : OriginalData) (N cap : ℕ)
    (hN : 1 < N) (z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 2 (old3 d (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    pairEndpointRow d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ)-1)) (fun _ _ => 1) s =
      pairResidualRow d N cap s := by
  obtain ⟨hlen, _, _, _, _, _, hmass⟩ :=
    actualPrimeFrontier_geometry 2 (by omega) (old3 d (N : ℝ)) N cap z s hs
  have hself := rosserAncestor_self_of_length 2 s.selectedPrefix hlen
  rw [pairEndpointRow,
    endpointReplacement_continuation d (N : ℝ) false _ (by omega),
    endpointReplacement_continuation d (N : ℝ) true _ (by omega)]
  by_cases hg : secondGuard (N : ℝ) s.selectedPrefix
  · rw [if_pos hg, if_pos hg, hself, pairResidualRow, if_pos hg]
    have hd (new : Bool) := firstExitRetainedPolynomial_frozenParity_frontier_density
      false 2 (by omega) (old3 d (N : ℝ)) (pairCap (N : ℝ) new) N cap z s hs
      (actual_pair_endpoint_admissible d N cap hN z s hs hg new)
    have ho := hd false
    have hn := hd true
    rw [firstExitRetainedPolynomial_frozenParityRosser_eq false 2 _ _ _ _ _ _ hlen] at ho
    rw [firstExitRetainedPolynomial_frozenParityRosser_eq false 2 _ _ _ _ _ _ hlen] at hn
    simp only [signedTest_one_eq_polynomial]
    rw [ho, hn]
    simp only [actualFrozenFrontierDensityTerm, ← hmass,
      signedTreeCoefficient_evenListLength_eq_negOnePow, ordinaryRosserResidualLower, hlen]
    norm_num <;> ring
  · simp only [if_neg hg, pairResidualRow, sub_self]

/-- This is the genuine pair-density side of the finite conversion.
The actual parent frontier, target deletion, complete product, multiplicity,
positive pair sign, and strict last-prime cutoff are all unchanged. -/
theorem endpointSource_eq_actual_historical_pair_residual_sum
    (d : OriginalData) (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    endpointSource d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ)-1)) (fun _ _ => 1)
      (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 2 (old3 d (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
        (pairResidualRow d N cap)).sum := by
  rw [endpointSource_eq_historical_pair_sum]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact pairEndpointRow_eq_actual_upper_residual d N cap hN z s hs

theorem v_eq_catalog_endpoint (t : ℝ) :
    v t = Certificates.AboveMuSecondCoarse.endpointEnvelope t := by
  rw [v_eq_min]
  unfold A C Certificates.AboveMuSecondCoarse.endpointEnvelope
  congr 1 <;> ring

/-- The source guard, including both open endpoints, is the same domain
used by K and M. There is no added y >= 3/16 filter or sorting factorial. -/
theorem secondRegion_iff_catalog_domain (x y : ℝ) :
    SecondRegion x y ↔ (x,y) ∈ Certificates.AboveMuSecondCoarse.physicalDomain := by
  rw [P4AOriginalSecondPhysicalIntegral.physicalDomain_iff]
  constructor
  · rintro ⟨hx,hr,hy,hxy⟩
    have hb : 2 * v x - 1 = P4AOriginalSecondPhysicalIntegral.lowerBoundary x := by
      rw [v_eq_C hx.le]
      unfold C P4AOriginalSecondPhysicalIntegral.lowerBoundary
      ring
    exact ⟨⟨hx,hr⟩,⟨hb ▸ hy,hxy⟩⟩
  · rintro ⟨⟨hx,hr⟩,hy,hxy⟩
    have hb : 2 * v x - 1 = P4AOriginalSecondPhysicalIntegral.lowerBoundary x := by
      rw [v_eq_C hx.le]
      unfold C P4AOriginalSecondPhysicalIntegral.lowerBoundary
      ring
    exact ⟨hx,hr,hb.symm ▸ hy,hxy⟩

def historicalPairs (d : OriginalData) (N cap : ℕ) (z : ℝ) : Finset (Fin 2 → ℕ) :=
  firstExitAdmittedTuples 2 (old3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z)

def historyResidual (N cap : ℕ) (pre : List ℕ) : ℝ :=
  if secondGuard (N : ℝ) pre then
    actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      (pairCap (N : ℝ) false pre / (pre.prod : ℝ)) -
    actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      (pairCap (N : ℝ) true pre / (pre.prod : ℝ))
  else 0

theorem endpointSource_eq_historical_tuple_sum
    (d : OriginalData) (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    endpointSource d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ)-1)) (fun _ _ => 1)
      (roughPrimeUniverse N cap 0 z) =
      ∑ p ∈ historicalPairs d N cap z, (∏ i, 1 / ((p i : ℝ)-1)) *
        historyResidual N cap (List.ofFn p).reverse := by
  rw [endpointSource_eq_actual_historical_pair_residual_sum d N cap hN z]
  unfold historicalPairs
  rw [← firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 2 (old3 d (N : ℝ))
    (fun p : ℕ => 1 / ((p : ℝ)-1)) (roughPrimeUniverse N cap 0 z)
    (roughPrimeUniverse_nodup N cap 0 z) (historyResidual N cap)]
  congr 1
  apply List.map_congr_left
  intro s hs
  have hm := (actualPrimeFrontier_geometry 2 (by omega) (old3 d (N : ℝ)) N cap z s hs).2.2.2.2.2.2
  rw [← hm]
  by_cases hg : secondGuard (N : ℝ) s.selectedPrefix <;>
    simp only [pairResidualRow, historyResidual, hg, if_pos, if_neg, mul_zero]

private theorem normalized_historyResidual (N cap : ℕ) (p : Fin 2 → ℕ) :
    historyResidual N cap (List.ofFn p).reverse * Real.log (N : ℝ) / singularSeries N =
      if (actualPrimeTupleLog N p 0, actualPrimeTupleLog N p 1) ∈
          Certificates.AboveMuSecondCoarse.physicalDomain then
        actualPrimeTupleInitialSaving N cap
          (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 0))
          (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 1)) p
      else 0 := by
  have hp : (List.ofFn p).reverse = [p 1,p 0] := by simp [List.ofFn_succ]
  have hg : secondGuard (N : ℝ) (List.ofFn p).reverse ↔
      (actualPrimeTupleLog N p 0, actualPrimeTupleLog N p 1) ∈
        Certificates.AboveMuSecondCoarse.physicalDomain := by
    rw [← secondRegion_iff_catalog_domain]
    simp [secondGuard, hp, rosserAncestor, primeHistoryLogCoordinates,
      primeHistoryTuple, actualPrimeTupleLog]
  unfold historyResidual
  simp only [hg]
  split_ifs with h
  · simp [hp, pairCap, primeHistoryLogCoordinates, primeHistoryTuple,
      v_eq_catalog_endpoint, actualPrimeTupleInitialSaving, actualPrimeTupleLog,
      Fin.prod_univ_two, Nat.cast_mul, mul_comm]
  · simp

/-- The normalized summand is EXACTLY M's ordinary-pair summand. The only
remaining carrier restriction visible here is the actual historical pair
frontier; it has not been replaced by the full ideal strip by declaration. -/
theorem normalized_endpointSource_eq_catalog_summands_on_actual_pairs
    (d : OriginalData) (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    endpointSource d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ)-1)) (fun _ _ => 1)
        (roughPrimeUniverse N cap 0 z) * Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ historicalPairs d N cap z,
        if (actualPrimeTupleLog N p 0, actualPrimeTupleLog N p 1) ∈
            Certificates.AboveMuSecondCoarse.physicalDomain then
          (∏ i, 1 / ((p i : ℝ)-1)) * actualPrimeTupleInitialSaving N cap
            (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 0))
            (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 1)) p
        else 0 := by
  rw [endpointSource_eq_historical_tuple_sum d N cap hN z, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_assoc, mul_div_assoc, normalized_historyResidual]
  split_ifs <;> simp only [mul_zero]

/-- A concrete K/M trimmed prime pair passes the ACTUAL first-label stop,
once its clearance covers 4e plus one old mesh width. No later label is
projected to choose this parent. -/
theorem catalog_trimmed_pair_mem_historical (d : OriginalData) (delta : ℝ)
    (hd : 0 < delta) (he : 0 ≤ (d.e : ℝ))
    (hbuffer : 4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) (p : Fin 2 → ℕ)
    (hp : p ∈ P4AOriginalSecondResidualSupplier.trimmedPrimePairs delta N) :
    p ∈ historicalPairs d N N ((N : ℝ) ^ (19 / 96 : ℝ)) := by
  have hpi := mem_actualPrimeBoxTuples_iff.mp (Finset.mem_filter.mp hp).1
  have hpos : ∀ i, 0 < p i := fun i => (hpi i).1.pos
  have ht := (Finset.mem_filter.mp hp).2
  have hdomain := P4AOriginalSecondResidualSupplier.trimmedRegion_subset_physicalDomain hd ht
  obtain ⟨hx,hy⟩ := (P4AOriginalSecondPhysicalIntegral.physicalDomain_iff _ _).mp hdomain
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hxbox : actualPrimeTupleLog N p 0 ∈ Set.Ico (0 : ℝ) (19 / 96 : ℝ) :=
    ⟨(by norm_num [Certificates.AboveMuSecondCoarse.mu] :
        (0 : ℝ) ≤ Certificates.AboveMuSecondCoarse.mu).trans hx.1.le,hx.2⟩
  obtain ⟨i,hil,hiu⟩ := exists_logPrimeMeshInterval 0 (19 / 96) d.m hxbox
  have hmesh := P4ACatalogFiveHistoricalCoverage.meshStep_pos d.m
  have hhi := logPrimeMeshPoint_succ 0 (19 / 96) d.m i.val
  have hxtrim : actualPrimeTupleLog N p 0 ≤ (19 / 96 : ℝ) - delta := ht.2.1
  have hstop : HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) [p 0] := by
    have hcoord : primeHistoryLogCoordinates (N : ℝ) 1 [p 0] 0 = actualPrimeTupleLog N p 0 := by
      simp [primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
    refine ⟨i,hcoord.symm ▸ hil,hcoord.symm ▸ hiu,?_⟩
    dsimp [P4ACatalogFiveHistoricalCoverage.meshStep] at hbuffer
    rw [hhi]
    dsimp [extendedFirstStop]
    linarith
  have hstopPoint : actualPrimeTupleLog N p 0 ≤ extendedFirstStop - 4 * (d.e : ℝ) := by
    dsimp [extendedFirstStop]
    linarith
  have hcube := original_first_cube_from_stop he hstopPoint
  have hcubePow : (p 0 : ℝ)^3 < (N : ℝ)^HistoricalThirdCoarse.initial (d.e : ℝ) := by
    have hh := (Real.rpow_lt_rpow_left_iff hNr).mpr hcube
    rw [mul_comm (3 : ℝ), Real.rpow_mul (zero_lt_one.trans hNr).le,
      actualPrimeTupleLog_rpow hN p hpos 0, Real.rpow_natCast] at hh
    exact hh
  have h21 := P4AOriginalSecondResidualSupplier.trimmedPrimePairs_strict_order hd hN hp
  have hpair := upper_pair_admissible_of_cube _ (p 0) (p 1) (hpos 1) h21 hcubePow
  have hsingle := ordinaryRosserPrefixAdmissible_tail false
    ((N : ℝ)^HistoricalThirdCoarse.initial (d.e : ℝ)) (p 1) [p 0] (hpi 1).1
    (by simpa using h21) hpair
  have hnode : old3 d (N : ℝ) false [p 0] = true := by
    rw [old3, HistoricalThirdCoarse.policy_through_two _ _ _ _ _ _ _ (by simp)]
    simp [HistoricalThirdCoarse.initialPolicy,oddFirstExitPolicy,hsingle,hstop]
  have hvalid : FirstExitValidSelection (old3 d (N : ℝ)) [] true (List.ofFn p) := by
    have heven : old3 d (N : ℝ) true [p 1,p 0] = true :=
      HistoricalThirdCoarse.policy_even _ _ _ _ _ _
    simp [List.ofFn_succ,FirstExitValidSelection,hnode,heven]
  have hanti : StrictAnti p := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> norm_num at hab ⊢
    exact h21
  have hcap : (N : ℝ) ^ (19/96:ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (by norm_num : (19/96:ℝ) ≤ 1)
  apply (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 2 (old3 d (N : ℝ))
    N N 0 ((N : ℝ) ^ (19/96:ℝ)) hcap p).mpr
  exact ⟨hanti,fun i => ⟨(hpi i).1,(hpi i).2.1,Nat.cast_nonneg _,(hpi i).2.2.2⟩,hvalid⟩

/-- Exact compact carrier equality. The old firstStop is PROVED for every
M pair, rather than removed by a source-identity premise. -/
theorem historicalPairs_trim_filter_eq_catalog (d : OriginalData) (delta : ℝ)
    (hd : 0 < delta) (he : 0 ≤ (d.e : ℝ))
    (hbuffer : 4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) :
    (historicalPairs d N N ((N : ℝ) ^ (19/96:ℝ))).filter (fun p =>
      (actualPrimeTupleLog N p 0,actualPrimeTupleLog N p 1) ∈
        P4AOriginalSecondResidualSupplier.trimmedRegion delta) =
      P4AOriginalSecondResidualSupplier.trimmedPrimePairs delta N := by
  ext p
  constructor
  · intro hp
    obtain ⟨hparent,ht⟩ := Finset.mem_filter.mp hp
    have hcarrier := (mem_firstExitAdmittedTuples_iff_of_decreasing 2 (old3 d (N : ℝ))
      (roughPrimeUniverse N N 0 ((N : ℝ) ^ (19/96:ℝ)))
      (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hparent
    apply (P4AOriginalSecondResidualSupplier.mem_trimmedPrimePairs_iff hd hN p).mpr
    refine ⟨?_,ht⟩
    intro i
    have hi := mem_roughPrimeUniverse.mp (hcarrier.2.1 i)
    exact ⟨hi.2.1,hi.2.2.1⟩
  · intro hp
    exact Finset.mem_filter.mpr ⟨catalog_trimmed_pair_mem_historical d delta hd he hbuffer N hN p hp,
      (Finset.mem_filter.mp hp).2⟩

theorem historical_trimmed_sum_eq_catalog_arithmetic (d : OriginalData) (delta : ℝ)
    (hd : 0 < delta) (he : 0 ≤ (d.e : ℝ))
    (hbuffer : 4 * (d.e : ℝ) + P4ACatalogFiveHistoricalCoverage.meshStep d.m ≤ delta)
    (N : ℕ) (hN : 1 < N) :
    (∑ p ∈ (historicalPairs d N N ((N : ℝ) ^ (19/96:ℝ))).filter (fun p =>
      (actualPrimeTupleLog N p 0,actualPrimeTupleLog N p 1) ∈
        P4AOriginalSecondResidualSupplier.trimmedRegion delta),
      (∏ i, 1 / ((p i : ℝ)-1)) * actualPrimeTupleInitialSaving N N
        (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 0))
        (Certificates.AboveMuSecondCoarse.endpointEnvelope (actualPrimeTupleLog N p 1)) p) =
      P4AOriginalSecondResidualSupplier.trimmedArithmeticSaving delta N := by
  rw [historicalPairs_trim_filter_eq_catalog d delta hd he hbuffer N hN]
  rfl

end
end ImbalancedChen.P4ACatalogFiveActualPairDecomposition
