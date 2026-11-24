import ImbalancedChen.P4AOriginalCausalHistory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The catalog-five second action changes rank THREE itself.  Its source must
therefore include candidate third prefixes rejected by the old policy.
This file constructs that before-test frontier from the actual old rank-two
history, rather than assuming a retained rank-three source identity.

Every old-admitted continuation and every newly restored continuation is
kept with its original sign, mass, remaining carrier and terminal test.
Unsupported third histories, including the disabled small-third branch,
give exactly zero.  The restoration term is also identified with its actual
ordinary LOWER residual on the genuine prime carrier.

No equality with the catalog-five endpoint prime-pair integral is claimed:
the old coarse cap and the disabled-history error still require their own
uniform limiting estimates.  No full22/full87 history is assumed.
-/

namespace ImbalancedChen.P4AOriginalRankThreeRestorationSource
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalCausalHistory
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedAncestry
open P5OriginalCommonThirdScreenedSource
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P5OriginalCommonFourthSourceLedger

/-- Test all candidate third nodes, after the unchanged historical first
and second decisions.  This is an enumeration policy, not a new sieve. -/
def beforeThirdPolicy (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 2 parent (fun _ _ => true)

def admittedTest (P : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  if P s.positive s.selectedPrefix = true then
    signedTest P h T s.selectedPrefix s.positive s.mass s.remaining else 0

/-- Exact before-admission identity.  In particular no old rank-three
admission is silently required of a newly restored state. -/
theorem signed_difference_before_third
    (parent old fresh : Bool → List ℕ → Bool)
    (ho : ∀ b pre, pre.length ≤ 2 → old b pre = parent b pre)
    (hn : ∀ b pre, pre.length ≤ 2 → fresh b pre = parent b pre)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length ≤ 2)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest fresh h T pre positive mass remaining -
        signedTest old h T pre positive mass remaining =
      ((firstExitDepthFrontier 3 (beforeThirdPolicy parent) h
        pre positive mass remaining).map
          (fun s => admittedTest fresh h T s - admittedTest old h T s)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      have hb : ¬3 ≤ pre.length := by omega
      simp [signedTest, firstExitDepthFrontier, hb]
  | cons p ps ih =>
      have hb : ¬3 ≤ pre.length := by omega
      have hs := ih (pre := pre) (hlen := hlen) (positive := positive) (mass := mass)
      by_cases hh : pre.length = 2
      · have hc : beforeThirdPolicy parent (!positive) (p :: pre) = true := by
          simp [beforeThirdPolicy, firstExitDepthSplicePolicy, hh]
        have hf : firstExitDepthFrontier 3 (beforeThirdPolicy parent) h
            (p :: pre) (!positive) (mass * h p) ps =
            [{ selectedPrefix := p :: pre, positive := !positive,
               mass := mass * h p, remaining := ps }] := by
          cases ps <;> simp [firstExitDepthFrontier, hh]
        simp only [signedTest, firstExitDepthFrontier, if_neg hb, if_pos hc, hf,
          List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, add_zero]
        dsimp only [admittedTest]
        linarith only [hs]
      · have hnext : (p :: pre).length ≤ 2 := by simp only [List.length_cons]; omega
        have hpo := ho (!positive) (p :: pre) hnext
        have hpn := hn (!positive) (p :: pre) hnext
        have hpc : beforeThirdPolicy parent (!positive) (p :: pre) =
            parent (!positive) (p :: pre) := by
          simp only [beforeThirdPolicy, firstExitDepthSplicePolicy, if_pos hnext]
        by_cases hp : parent (!positive) (p :: pre) = true
        · have ht := ih (pre := p :: pre) (hlen := hnext)
            (positive := !positive) (mass := mass * h p)
          simp only [signedTest, hpo, hpn, if_pos hp, firstExitDepthFrontier,
            if_neg hb, hpc, List.map_append, List.sum_append]
          linarith only [hs, ht]
        · simpa only [signedTest, hpo, hpn, if_neg hp, add_zero,
            firstExitDepthFrontier, if_neg hb, hpc, List.append_nil] using hs

def candidates (d : OriginalData) (N : ℝ) (h : ℕ → ℝ) (carrier : List ℕ) :
    List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 3 (beforeThirdPolicy (old3 d N)) h [] true 1 carrier

def rowChange (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  admittedTest (secondStage d N) h T s - admittedTest (old3 d N) h T s

theorem secondChange_eq_candidate_sum (d : OriginalData) (N : ℝ)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    secondChange d N h T carrier = ((candidates d N h carrier).map
      (rowChange d N h T)).sum := by
  rw [secondChange_eq]
  exact signed_difference_before_third (old3 d N) (old3 d N) (secondStage d N)
    (fun _ _ _ => rfl)
    (fun b pre hp => by simp only [secondStage, if_pos hp])
    h T [] (by simp) true 1 carrier

def activeSecond (d : OriginalData) (N : ℝ) (pre : List ℕ) : Prop :=
  selectedThird d N pre ∧ secondGuard N pre

theorem activeSecond_append (d : OriginalData) (N : ℝ)
    (later pre : List ℕ) (hlen : 3 ≤ pre.length) :
    activeSecond d N (later ++ pre) ↔ activeSecond d N pre := by
  simp only [activeSecond, selectedThird_append d N later pre hlen,
    secondGuard_append N later pre (by omega : 2 ≤ pre.length)]

theorem secondStage_supported_decision (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : 3 ≤ pre.length) (ha : activeSecond d N pre)
    (b : Bool) :
    secondStage d N b pre =
      ordinaryParityRosserPolicy false (N ^ secondExponent N pre) b pre := by
  simp only [secondStage, if_neg (by omega : ¬pre.length ≤ 2), if_pos ha]

/-- A selected third label freezes the second cap on the same pair; it
does not acquire a level from any later selected prime. -/
theorem secondStage_supported_continuation (d : OriginalData) (N : ℝ)
    (base : List ℕ) (hlen : 3 ≤ base.length) (ha : activeSecond d N base)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (secondStage d N) h T base positive mass remaining =
      signedTest (ordinaryParityRosserPolicy false (N ^ secondExponent N base))
        h T base positive mass remaining := by
  have hrec (later : List ℕ) (b : Bool) (a : ℝ) (rest : List ℕ) :
      signedTest (secondStage d N) h T (later ++ base) b a rest =
        signedTest (ordinaryParityRosserPolicy false (N ^ secondExponent N base))
          h T (later ++ base) b a rest := by
    induction rest generalizing later b a with
    | nil => rfl
    | cons p ps ih =>
        have hl : 3 ≤ ((p :: later) ++ base).length := by simp only [List.length_append]; omega
        have ha' := (activeSecond_append d N (p :: later) base hlen).mpr ha
        have hp : secondStage d N (!b) (p :: (later ++ base)) =
            ordinaryParityRosserPolicy false (N ^ secondExponent N base)
              (!b) (p :: (later ++ base)) := by
          change secondStage d N (!b) ((p :: later) ++ base) = _
          rw [secondStage_supported_decision d N _ hl ha',
            secondExponent_append N (p :: later) base (by omega)]
        simp only [signedTest, hp]
        rw [ih (later := later) (b := b) (a := a),
          ih (later := p :: later) (b := !b) (a := a * h p)]
  simpa only [List.nil_append] using hrec [] positive mass remaining

/-- Failure of either original support or the second-source guard is
inherited by every descendant of this third prefix. -/
theorem secondStage_inactive_continuation (d : OriginalData) (N : ℝ)
    (base : List ℕ) (hlen : 3 ≤ base.length) (ha : ¬activeSecond d N base)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (positive : Bool) (mass : ℝ) (remaining : List ℕ) :
    signedTest (secondStage d N) h T base positive mass remaining =
      signedTest (old3 d N) h T base positive mass remaining := by
  induction remaining generalizing base positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hl : 3 ≤ (p :: base).length := by simp; omega
      have ha' : ¬activeSecond d N (p :: base) := by
        simpa only [List.singleton_append] using
          (not_congr (activeSecond_append d N [p] base hlen)).mpr ha
      have hp : secondStage d N (!positive) (p :: base) = old3 d N (!positive) (p :: base) := by
        simp only [secondStage, if_neg (by omega : ¬(p :: base).length ≤ 2),
          if_neg ha']
      simp only [signedTest, hp]
      rw [ih (base := base) (hlen := hlen) (ha := ha) (positive := positive) (mass := mass),
        ih (base := p :: base) (hlen := hl) (ha := ha')
          (positive := !positive) (mass := mass * h p)]

def newValue (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (ordinaryParityRosserPolicy false (N ^ secondExponent N s.selectedPrefix))
    h T s.selectedPrefix s.positive s.mass s.remaining

def retainedTerm (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  if activeSecond d N s.selectedPrefix ∧ old3 d N s.positive s.selectedPrefix = true then
    newValue d N h T s - signedTest (old3 d N) h T
      s.selectedPrefix s.positive s.mass s.remaining else 0

def restoredTerm (d : OriginalData) (N : ℝ) (h : ℕ → ℝ)
    (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ) : ℝ :=
  if activeSecond d N s.selectedPrefix ∧ old3 d N s.positive s.selectedPrefix = false ∧
      ordinaryParityRosserPolicy false (N ^ secondExponent N s.selectedPrefix)
        s.positive s.selectedPrefix = true then newValue d N h T s else 0

theorem supported_old_admission_implies_new (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (N : ℝ) (hN : 1 ≤ N)
    (pre : List ℕ) (hlen : 3 ≤ pre.length) (ha : activeSecond d N pre)
    (b : Bool) (ho : old3 d N b pre = true) :
    ordinaryParityRosserPolicy false (N ^ secondExponent N pre) b pre = true := by
  have hcap := Real.rpow_le_rpow_of_exponent_le hN
    (originalSeed_lt_second d he N pre hlen ha.1 ha.2).le
  rw [old3_after_two d N b pre (by omega)] at ho
  cases b with
  | true => simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]
  | false =>
      have had : ordinaryRosserPrefixAdmissible false (N ^ originalSeed d N pre) pre := by
        simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using ho
      simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using
        ordinaryRosserPrefixAdmissible_mono false pre hcap had

/-- The retained part is a difference; restoration is one whole new
continuation.  No signed-monotonicity argument is used. -/
theorem rowChange_eq_retained_add_restored (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (s : FirstExitDepthState ℕ)
    (hlen : s.selectedPrefix.length = 3) :
    rowChange d N h T s = retainedTerm d N h T s + restoredTerm d N h T s := by
  by_cases ha : activeSecond d N s.selectedPrefix
  · have hd := secondStage_supported_decision d N _ (by omega) ha s.positive
    have hc := secondStage_supported_continuation d N _ (by omega) ha h T
      s.positive s.mass s.remaining
    by_cases ho : old3 d N s.positive s.selectedPrefix = true
    · have hn := supported_old_admission_implies_new d he N hN _ (by omega) ha _ ho
      simp [rowChange, admittedTest, retainedTerm, restoredTerm, newValue, ha, ho, hd, hc, hn]
    · have hof : old3 d N s.positive s.selectedPrefix = false := by
        cases hh : old3 d N s.positive s.selectedPrefix <;> simp_all
      by_cases hn : ordinaryParityRosserPolicy false (N ^ secondExponent N s.selectedPrefix)
          s.positive s.selectedPrefix = true <;>
        simp [rowChange, admittedTest, retainedTerm, restoredTerm, newValue,
          ha, ho, hof, hd, hc, hn]
  · have hd : secondStage d N s.positive s.selectedPrefix = old3 d N s.positive s.selectedPrefix := by
      simp only [secondStage, if_neg (by omega : ¬s.selectedPrefix.length ≤ 2), if_neg ha]
    have hc := secondStage_inactive_continuation d N _ (by omega) ha h T
      s.positive s.mass s.remaining
    simp [rowChange, admittedTest, retainedTerm, restoredTerm, ha, hd, hc]

theorem secondChange_eq_retained_and_restored (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (N : ℝ) (hN : 1 ≤ N)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (carrier : List ℕ) :
    secondChange d N h T carrier = ((candidates d N h carrier).map
      (fun s => retainedTerm d N h T s + restoredTerm d N h T s)).sum := by
  rw [secondChange_eq_candidate_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact rowChange_eq_retained_add_restored d he N hN h T s
    (firstExitDepthFrontier_selected_length 3 (beforeThirdPolicy (old3 d N)) h []
      carrier true 1 (by simp) s hs)

/-- The disabled branch is an exact zero at the before-test source, not
an omitted endpoint residual incorrectly assigned the cap v(x). -/
theorem disabled_small_third_row_zero (d : OriginalData) (N : ℝ)
    (p1 p2 p3 : ℕ) (hp : (p3 : ℝ) < N ^ d.omega)
    (h : ℕ → ℝ) (T : Bool → List ℕ → ℝ) (b : Bool) (a : ℝ) (rest : List ℕ) :
    let s : FirstExitDepthState ℕ := ⟨[p3,p2,p1], b, a, rest⟩
    rowChange d N h T s = 0 ∧ retainedTerm d N h T s = 0 ∧ restoredTerm d N h T s = 0 := by
  dsimp only
  have hsel := small_third_not_selected d N p1 p2 p3 hp
  have ha : ¬activeSecond d N [p3,p2,p1] := fun hh => hsel hh.1
  have hd : secondStage d N b [p3,p2,p1] = old3 d N b [p3,p2,p1] := by
    simp [secondStage, hsel]
  have hc := secondStage_inactive_continuation d N [p3,p2,p1] (by simp) ha h T b a rest
  simp [rowChange, admittedTest, retainedTerm, restoredTerm, ha, hd, hc]

/-- On the genuine candidate-prime frontier, the restored branch has
negative incoming sign and the ordinary LOWER residual.  Old admission is
not a premise: its failure is part of the displayed restoration mask. -/
theorem restoredTerm_eq_actual_lower_residual (d : OriginalData)
    (N cap : ℕ) (z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z)) :
    restoredTerm d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1) s =
      if activeSecond d (N : ℝ) s.selectedPrefix ∧
          old3 d (N : ℝ) s.positive s.selectedPrefix = false ∧
          ordinaryRosserPrefixAdmissible false
            ((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) s.selectedPrefix then
        -s.mass * actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
          (((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) / (s.selectedPrefix.prod : ℝ))
      else 0 := by
  obtain ⟨hlen, _, _, _, _, hsign, hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N cap z s hs
  have hfalse : s.positive = false := by
    have hpar := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1 : ℝ)
    cases hb : evenListLength s.selectedPrefix with
    | false => exact hsign.trans hb
    | true =>
        rw [hb, hlen] at hpar
        norm_num [signedTreeCoefficient] at hpar
  let Q : ℝ := (N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix
  have hbool : ordinaryParityRosserPolicy false Q s.positive s.selectedPrefix = true ↔
      ordinaryRosserPrefixAdmissible false Q s.selectedPrefix := by
    simp [hfalse, ordinaryParityRosserPolicy, oddFirstExitPolicy]
  by_cases hg : activeSecond d (N : ℝ) s.selectedPrefix ∧
      old3 d (N : ℝ) s.positive s.selectedPrefix = false ∧
      ordinaryRosserPrefixAdmissible false Q s.selectedPrefix
  · have hgate : activeSecond d (N : ℝ) s.selectedPrefix ∧
        old3 d (N : ℝ) s.positive s.selectedPrefix = false ∧
        ordinaryParityRosserPolicy false Q s.positive s.selectedPrefix = true :=
      ⟨hg.1, hg.2.1, hbool.mpr hg.2.2⟩
    have hdensity := firstExitRetainedPolynomial_frozenParity_frontier_density false 3
      (by omega) (beforeThirdPolicy (old3 d (N : ℝ))) (fun _ => Q) N cap z s hs hg.2.2
    change firstExitRetainedPolynomial (ordinaryParityRosserPolicy false Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) s.selectedPrefix s.positive s.mass s.remaining = _ at hdensity
    rw [restoredTerm, if_pos hgate, if_pos hg, newValue, signedTest_one_eq_polynomial, hdensity]
    simp only [actualFrozenFrontierDensityTerm, ← hmass,
      signedTreeCoefficient_evenListLength_eq_negOnePow, ordinaryRosserResidualLower, hlen]
    norm_num
  · have hgate : ¬(activeSecond d (N : ℝ) s.selectedPrefix ∧
        old3 d (N : ℝ) s.positive s.selectedPrefix = false ∧
        ordinaryParityRosserPolicy false Q s.positive s.selectedPrefix = true) :=
      fun hh => hg ⟨hh.1, hh.2.1, hbool.mp hh.2.2⟩
    simp only [restoredTerm, if_neg hgate, if_neg hg]

/-- The old-admitted half uses the ACTUAL old coarse level.  Together
with the previous theorem this is a complete literal residual dictionary
for the second action, with restoration rather than a fictitious old term
on formerly rejected nodes. -/
theorem retainedTerm_eq_actual_lower_difference (d : OriginalData)
    (he : 0 ≤ (d.e : ℝ)) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z)) :
    retainedTerm d (N : ℝ) (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1) s =
      if activeSecond d (N : ℝ) s.selectedPrefix ∧
          old3 d (N : ℝ) s.positive s.selectedPrefix = true then
        s.mass *
          (actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
            (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega
              (N : ℝ) s.selectedPrefix / (s.selectedPrefix.prod : ℝ)) -
           actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
            (((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) / (s.selectedPrefix.prod : ℝ)))
      else 0 := by
  obtain ⟨hlen, _, _, _, _, hsign, hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N cap z s hs
  have hfalse : s.positive = false := by
    have hpar := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1 : ℝ)
    cases hb : evenListLength s.selectedPrefix with
    | false => exact hsign.trans hb
    | true =>
        rw [hb, hlen] at hpar
        norm_num [signedTreeCoefficient] at hpar
  by_cases hg : activeSecond d (N : ℝ) s.selectedPrefix ∧
      old3 d (N : ℝ) s.positive s.selectedPrefix = true
  · have hself := rosserAncestor_self_of_length 3 s.selectedPrefix hlen
    have hlevel := P1OriginalVariableFourthContinuation.frozenLevel_eq_rpow_seed
      (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix
    change HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 s.selectedPrefix) =
        (N : ℝ) ^ originalSeed d (N : ℝ) s.selectedPrefix at hlevel
    rw [hself] at hlevel
    have hadOld : ordinaryRosserPrefixAdmissible false
        (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ) s.selectedPrefix)
        s.selectedPrefix := by
      rw [hlevel]
      have hh := hg.2
      rw [hfalse, old3_after_two d (N : ℝ) false s.selectedPrefix (by omega)] at hh
      simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hh
    have hadNew : ordinaryRosserPrefixAdmissible false
        ((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) s.selectedPrefix := by
      have hh := supported_old_admission_implies_new d he (N : ℝ) hN
        s.selectedPrefix (by omega) hg.1 s.positive hg.2
      simpa [hfalse, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hh
    have ho := firstExitRetainedPolynomial_frozenParity_frontier_density false 3 (by omega)
      (beforeThirdPolicy (old3 d (N : ℝ)))
      (HistoricalThirdCoarse.rawLevel (d.e : ℝ) d.chi d.m d.omega (N : ℝ))
      N cap z s hs hadOld
    have hn := firstExitRetainedPolynomial_frozenParity_frontier_density false 3 (by omega)
      (beforeThirdPolicy (old3 d (N : ℝ)))
      (fun _ => (N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix) N cap z s hs hadNew
    change firstExitRetainedPolynomial
      (ordinaryParityRosserPolicy false ((N : ℝ) ^ secondExponent (N : ℝ) s.selectedPrefix))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) s.selectedPrefix s.positive s.mass s.remaining = _ at hn
    have hc := P5OriginalCommonThirdActualLowerSource.old_third_continuation d (N : ℝ)
      s.selectedPrefix (by omega) (fun p : ℕ => 1 / ((p : ℝ) - 1)) (fun _ _ => 1)
      s.positive s.mass s.remaining
    simp only [signedTest_one_eq_polynomial] at hc
    rw [retainedTerm, if_pos hg, if_pos hg, newValue]
    simp only [signedTest_one_eq_polynomial]
    rw [hc, ho, hn]
    have hterm (Q : List ℕ → ℝ) :
        actualFrozenFrontierDensityTerm false N cap Q s.selectedPrefix =
          -s.mass * actualSmallRosserMinusDensity N cap (s.selectedPrefix.headD 0 : ℝ)
            (Q s.selectedPrefix / (s.selectedPrefix.prod : ℝ)) := by
      simp only [actualFrozenFrontierDensityTerm, ← hmass,
        signedTreeCoefficient_evenListLength_eq_negOnePow, ordinaryRosserResidualLower, hlen]
      norm_num
    rw [hterm, hterm]
    ring
  · simp only [retainedTerm, if_neg hg]

end
end ImbalancedChen.P4AOriginalRankThreeRestorationSource
