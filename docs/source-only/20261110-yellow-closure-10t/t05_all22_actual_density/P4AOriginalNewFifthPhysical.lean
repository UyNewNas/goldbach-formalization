import ImbalancedChen.P4AOriginalNewFifthIntegral
import ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
import ImbalancedChen.P4AOriginalFull87JointPhysicalBudget

/-! Original G3 at the same actual policy as the 87-cell gain. The
rank-four requantization and subsequent sixth change remain independently
defined occurrence sums on the union producer's own frontiers. -/
namespace ImbalancedChen.P4AOriginalNewFifthPhysical
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalNewFifthUnion (data original)
open P4AOriginalNewFifthMean (rawDifference unionIntegral tendsto_raw_union)
open P4AOriginalNewFifthIntegral (oldIntegral exists_cofinal_scalar_lower)
open P4AOriginalFull87RawChronology (rawRoot rawChange fifthSaving cutoff thirdIncrement)
open P4AOriginalFull87SlotTwoFive (exists_paid_original_sources sourceBound)
open P4AOriginalFull87JointPhysicalBudget (cutoff_le_target)
open P5OriginalCommonRefinedConstructor (old3 common3 policy5 level5 common3_even)
open P5OriginalCommonPositivePresieve (normalize normalize_add normalize_sub)
open P5OriginalCommonFourthSourceLedger (originalFourthIntegral signedTest_one_eq_polynomial)
open P5OriginalFourthFifthSourceInputs (originalRows4 originalAdmission4)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier)
open P1OriginalFifthMovingScaleLimit (evenTargets)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalVariableFifthPhysicalLedger (physical raw)
open P4AOriginalFull87ActualSavedEndpoint (Scheduled)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)

theorem slot_three : currentUpperEighteenGains 2 = (1648717268323516459667 : ℝ)/2^80 := by
  norm_num [currentUpperEighteenGains]

private theorem cap_covers : ∀ᶠ N : ℕ in evenTargets, cutoff N ≤ (N : ℝ) := by
  filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono (show evenTargets ≤ atTop from inf_le_left)]
    with N hN
  exact cutoff_le_target N (by exact_mod_cast hN)

/-- Newly certified arithmetic increment at the actual old and new fifth
trees. Each one uses its own literal fifth maximizer and the same fourth
tree, target N, cap N, cutoff rho and normalization. -/
def newGain (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (policy5 (original e q a) (N : ℝ)) N -
    rawRoot (policy5 (data e q a) (N : ℝ)) N)

theorem newGain_eq (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    newGain e q a N = rawDifference e q a N N - fifthSaving e q a N := by
  unfold newGain rawDifference fifthSaving P5OriginalArchiveCommonRawMean.normalizedRawDifference
    normalize rawRoot
  change (_-_) * Real.log (N : ℝ) / singularSeries N =
    (_-_) * Real.log (N : ℝ) / singularSeries N - (_-_) * Real.log (N : ℝ) / singularSeries N
  ring

theorem tendsto_newGain (e : ℚ) (he : 0 ≤ e) (q : ℕ) (a : ℝ) (ha : 0 < a) (har : a < 19/96) :
    Tendsto (newGain e q a) evenTargets (𝓝 (unionIntegral e q a - oldIntegral e q a)) := by
  rw [show newGain e q a = fun N => rawDifference e q a N N - fifthSaving e q a N from
    funext (newGain_eq e q a)]
  exact (tendsto_raw_union e he q a ha har (fun N => N) cap_covers).sub
    (P5OriginalArchiveCommonRawMean.tendsto_actual_common_rawDifference
      originalRows4 originalAdmission4 e he q ((e : ℝ)/20) a ha har (fun N => N) cap_covers)

theorem exists_ordinary_new_gain (eps : ℝ) (heps : 0 < eps) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ a : ℝ, 0 < a → a ≤ 1/800 →
      ∀ᶠ N : ℕ in atTop, Even N → currentUpperEighteenGains 2 - eps < newGain e q a N := by
  obtain ⟨e0,he0,hE⟩ := exists_cofinal_scalar_lower (eps/2) (half_pos heps)
  refine ⟨e0,he0,?_⟩
  intro e he her
  obtain ⟨q0,hq0,hQ⟩ := hE e he her
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha har
  have hfloor := hQ q hq a ha har
  have hnear := Metric.tendsto_nhds.1
    (tendsto_newGain e (by exact_mod_cast he.le) q a ha (har.trans_lt (by norm_num))) (eps/2) (half_pos heps)
  rw [Filter.eventually_inf_principal] at hnear
  filter_upwards [hnear,eventually_ge_atTop (2 : ℕ)] with N hnear hN
  intro heven
  have h := hnear (show 0 < N ∧ Even N from ⟨by omega,heven⟩)
  rw [Real.dist_eq] at h
  rw [slot_three]
  linarith [(abs_lt.mp h).1]

def fifthRounding (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := data e q a
  rawChange 4 (common3 d (N : ℝ)) (frozenParityRosserPolicy false 5 (level5 d (N : ℝ)))
    (frozenParityRosserPolicy false 5 (fun h =>
      (N : ℝ)^P4AOriginalFull87DataPolicy.level5Exponent n d (N : ℝ) h)) N

def sixthChange (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := data e q a
  let p := P4AOriginalFull87DataPolicy.fifthPolicy n d (N : ℝ)
  rawChange 6 p p (frozenParityRosserPolicy false 6 (fun h =>
    (N : ℝ)^P4AOriginalFull87DataPolicy.level6Exponent n d (N : ℝ) h)) N

private theorem read_raw (R : Bool → List ℕ → Bool) (hR : ∀ s, R true s = true) (N : ℕ) :
    signedTest R weight (fun _ _ => 1) [] true 1 (carrier N) = rawRoot R N := by
  rw [signedTest_one_eq_polynomial]
  exact UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained R hR N N 0 (cutoff N)

private theorem splice_raw (k : ℕ) (P A B : Bool → List ℕ → Bool)
    (hP : ∀ s, P true s = true) (hA : ∀ s, A true s = true) (hB : ∀ s, B true s = true) (N : ℕ) :
    rawRoot (firstExitDepthSplicePolicy k P B) N - rawRoot (firstExitDepthSplicePolicy k P A) N =
      rawChange k P A B N := by
  rw [← read_raw _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained k P B hP hB),
    ← read_raw _ (UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained k P A hP hA),
    signedTest_splice_eq_stopped_add_frontier,signedTest_splice_eq_stopped_add_frontier,add_sub_add_left_eq_sub]
  unfold rawChange
  generalize firstExitDepthFrontier k P weight [] true 1 (carrier N) = s
  induction s with
  | nil => simp
  | cons h t ih => simp only [List.map_cons,List.sum_cons]; linarith only [ih]

theorem sixth_sub_union_fifth (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) :
    rawRoot (P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N : ℝ)) N -
      rawRoot (policy5 (data e q a) (N : ℝ)) N = fifthRounding n e q a N + sixthChange n e q a N := by
  let d := data e q a
  let p := P4AOriginalFull87DataPolicy.fifthPolicy n d (N : ℝ)
  have h5 : rawRoot p N - rawRoot (policy5 d (N : ℝ)) N = fifthRounding n e q a N :=
    splice_raw 4 _ _ _ (common3_even _ _)
      (fun h => frozenParityRosserPolicy_upper_even 5 _ h) (fun h => frozenParityRosserPolicy_upper_even 5 _ h) N
  have h6 : rawRoot (P4AOriginalFull87DataPolicy.sixthPolicy n d (N : ℝ)) N - rawRoot p N =
      sixthChange n e q a N := by
    simpa only [firstExitDepthSplicePolicy_self] using splice_raw 6 p p
      (frozenParityRosserPolicy false 6 (fun h => (N : ℝ)^P4AOriginalFull87DataPolicy.level6Exponent n d (N : ℝ) h))
      (P4AOriginalFull87DataPolicy.fifth_even n d _) (P4AOriginalFull87DataPolicy.fifth_even n d _)
      (fun h => frozenParityRosserPolicy_upper_even 6 _ h) N
  change rawRoot (P4AOriginalFull87DataPolicy.sixthPolicy n d (N : ℝ)) N - rawRoot (policy5 d (N : ℝ)) N = _
  linarith

/-- The first and third signed/raw terms, the genuine fourth integral,
and both later signed frontiers on the union. The three original fifth-
and second-source entries appear once each. -/
def beforeEight (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  let d := original e q a
  normalize N (rawRoot (old3 d (N : ℝ)) N) + normalize N (thirdIncrement e q a N) -
    originalFourthIntegral d - currentUpperEighteenGains 1 - currentUpperEighteenGains 2 -
    currentUpperEighteenGains 4 + normalize N (fifthRounding n e q a N + sixthChange n e q a N)

private theorem early_scalar (eps eMax : ℝ) (heps : 0 < eps) (heMax : 0 < eMax) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1/800 ∧ ∀ a : ℝ, 0 < a → a ≤ a0 →
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
    ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
    mMin ≤ (original e q a).m ∧
    (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) (original e q a).m ≤
      (∑ i, currentUpperEighteenPositive i) + originalDensityReserve/4) ∧
    ∀ n : ℕ, ∀ᶠ N : ℕ in atTop, Even N →
      normalize N (rawRoot (P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N : ℝ)) N) <
        beforeEight n e q a N + eps := by
  obtain ⟨E,hE,hG⟩ := exists_ordinary_new_gain (eps/2) (half_pos heps)
  obtain ⟨a0,ha0,haSmall,_,hA⟩ := exists_paid_original_sources (eps/2) (min eMax E)
    (half_pos heps) (lt_min heMax hE)
  refine ⟨a0,ha0,haSmall,?_⟩
  intro a ha haa
  obtain ⟨e0,he0,heMax',_,hE'⟩ := hA a ha haa
  refine ⟨e0,he0,heMax'.trans (min_le_left _ _),?_⟩
  intro e he hee qMin mMin
  obtain ⟨qG,_,hGQ⟩ := hG e he (hee.trans_le (heMax'.trans (min_le_right _ _)))
  obtain ⟨q0,hq0,hqMin,hQ⟩ := hE' e he hee (max qMin qG) mMin
  refine ⟨q0,hq0,(le_max_left _ _).trans hqMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hearly⟩ := hQ q hq
  refine ⟨hm,hpos,?_⟩
  intro n
  have hg := hGQ q (((le_max_right _ _).trans hqMin).trans hq) a ha (haa.trans haSmall)
  filter_upwards [hearly 1 n,hg] with N ho hnew
  intro hEven
  have old := (ho hEven).2
  have H := congrArg (normalize N)
    (P4AOriginalFull87RawChronology.licensed_raw_sub_archive_fifth 1 n e q a N)
  rw [normalize_sub] at H
  have hn := hnew hEven
  rw [newGain,normalize_sub] at hn
  have hs := congrArg (normalize N) (sixth_sub_union_fifth n e q a N)
  rw [normalize_sub] at hs
  unfold sourceBound at old
  unfold beforeEight
  linarith only [old,H,hn,hs]

/-- The chosen trim, cap resolution and strip precede the common rational
mesh. Its displacement and fineness can be constrained before taking
the even-target limit. -/
def Joined (eMax : ℝ) (P : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop) : Prop :=
  ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
  ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1/800 ∧ ∀ a : ℝ, 0 < a → a ≤ a0 →
  ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
  ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
    mMin ≤ (data e q a).m ∧
    (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) (data e q a).m ≤
      (∑ i, currentUpperEighteenPositive i) + originalDensityReserve/4) ∧
    ∀ᶠ N : ℕ in atTop, Even N → P r n e q a N

theorem joined_eventually_mono {eMax : ℝ} {P Q : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop}
    (h : Joined eMax P)
    (himp : ∀ᶠ N : ℕ in atTop, ∀ r n e q a, 2 ≤ N → P r n e q a N → Q r n e q a N) :
    Joined eMax Q := by
  obtain ⟨r0,hR⟩ := h
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨a0,ha0,haSmall,hA⟩ := hN n hn
  refine ⟨a0,ha0,haSmall,?_⟩
  intro a ha haa
  obtain ⟨e0,he0,heCap,hE⟩ := hA a ha haa
  refine ⟨e0,he0,heCap,?_⟩
  intro e he hee qMin mMin
  obtain ⟨q0,hq0,hqMin,hQ⟩ := hE e he hee qMin mMin
  refine ⟨q0,hq0,hqMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hN'⟩ := hQ q hq
  refine ⟨hm,hpos,?_⟩
  filter_upwards [hN',himp,eventually_ge_atTop (2 : ℕ)] with N hp himpN hN2
  exact fun hev => himpN r n e q a hN2 (hp hev)

private theorem join_at_sixth {Late P : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop}
    {eta eMax : ℝ} (heta : 0 < eta) (heMax : 0 < eMax) (hLate : Scheduled Late)
    (join : ∀ r n e q a N, 2 ≤ N → Late r n e q a N →
      normalize N (rawRoot (P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N : ℝ)) N) <
        beforeEight n e q a N + eta → P r n e q a N) : Joined eMax P := by
  obtain ⟨r0,hR⟩ := hLate
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hL⟩ := hN n hn
  obtain ⟨a0,ha0,haSmall,hA⟩ := early_scalar eta (min eMax E) heta (lt_min heMax hE)
  refine ⟨a0,ha0,haSmall,?_⟩
  intro a ha haa
  obtain ⟨e0,he0,heCap,hE'⟩ := hA a ha haa
  refine ⟨e0,he0,heCap.trans (min_le_left _ _),?_⟩
  intro e he hee qMin mMin
  obtain ⟨qL,_,hLQ⟩ := hL e (by exact_mod_cast he) (hee.trans_le (heCap.trans (min_le_right _ _)))
  obtain ⟨q0,hq0,hqMin,hQ⟩ := hE' e he hee (max qMin qL) mMin
  refine ⟨q0,hq0,(le_max_left _ _).trans hqMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hEarly⟩ := hQ q hq
  obtain ⟨N0,hN0,hLast⟩ := hLQ q (((le_max_right _ _).trans hqMin).trans hq) a
    ((haa.trans haSmall).trans (by norm_num))
  refine ⟨hm,hpos,?_⟩
  filter_upwards [hEarly n,eventually_ge_atTop N0] with N hearly hNN
  exact fun hev => join r n e q a N (hN0.trans hNN) (hLast N hNN hev) (hearly hev)

theorem exists_joined_ordinary (eps eMax : ℝ) (heps : 0 < eps) (heMax : 0 < eMax) :
    Joined eMax (fun r n e q a N =>
      normalize N (rawRoot (P4AOriginalFull87UnionHistory.policy (width r) n e q a (N : ℝ)) N) <
        beforeEight n e q a N - (savedGain : ℝ) + eps) := by
  apply join_at_sixth (half_pos heps) heMax
    (P4AOriginalFull87ActualSavedEndpoint.union_ordinary_saved_gain (eps/2) (half_pos heps))
  intro r n e q a N hN hg hearly
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hmu : (N : ℝ)^VariableEnvelope.mu ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNR (by norm_num [VariableEnvelope.mu])
  have h := hg N (cutoff N) hmu (cutoff_le_target N hNR)
  rw [normalize_sub] at h
  change (savedGain : ℝ) - eps/2 <
    normalize N (rawRoot (P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N : ℝ)) N) -
    normalize N (rawRoot (P4AOriginalFull87UnionHistory.policy (width r) n e q a (N : ℝ)) N) at h
  linarith only [h,hearly]

/-- One positive-presieve projection of the actual enlarged eighth
tree. All three earlier fifth/catalogue savings and the full eight
archive entries occur at this same cap, cutoff and target. -/
theorem exists_joined_positive_presieve (nu eps betaMax eMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) (heMax : 0 < eMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 ≤ (19/96 : ℝ)/nu ∧
    Joined eMax (fun r n e q a N =>
      let w := (N : ℝ)^(nu*beta^2)
      let L := (N : ℝ)^(nu*beta)
      1 < w ∧ w ≤ cutoff N ∧ normalize N
        (physical (P4AOriginalFull87UnionHistory.policy (width r) n e q a (N : ℝ)) N N w (cutoff N) L) <
          beforeEight n e q a N - (savedGain : ℝ) + eps) := by
  obtain ⟨beta,hb,hb8,hbM,hbs,hLate⟩ :=
    P4AOriginalFull87ActualSavedEndpoint.union_positive_presieve_saved_gain nu (eps/2) betaMax
      hnu (half_pos heps) hMax
  refine ⟨beta,hb,hb8,hbM,hbs,join_at_sixth (half_pos heps) heMax hLate ?_⟩
  intro r n e q a N hN hLg hearly
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hw,hwz,hg⟩ := hLg N (cutoff_le_target N hNR)
  refine ⟨hw,hwz,?_⟩
  change normalize N (physical (P4AOriginalFull87UnionHistory.policy (width r) n e q a (N : ℝ))
      N N ((N : ℝ)^(nu*beta^2)) (cutoff N) ((N : ℝ)^(nu*beta))) <
    normalize N (rawRoot (P4AOriginalFull87UnionHistory.sixthPolicy n e q a (N : ℝ)) N) -
      (savedGain : ℝ) + eps/2 at hg
  linarith only [hg,hearly]

end
end ImbalancedChen.P4AOriginalNewFifthPhysical

