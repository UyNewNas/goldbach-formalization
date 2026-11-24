import ImbalancedChen.P4AOriginalNewFifthOwners
import ImbalancedChen.P5OriginalArchiveCommonRawMean

/-! Finite causal reindexing and the genuine arithmetic mean for the
old-plus-new fifth owner union. The same common/fallback third policy
and the same newly increased fifth maximum enter every term. -/
namespace ImbalancedChen.P4AOriginalNewFifthMean
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchive
open P4AOriginalNewFifthUnion
open P1OriginalPrefixRowDecodeSoundness (decodeFifthRows_source_geometry)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P1OriginalVariableFifthContinuation (FifthRow eligible)
open P1OriginalVariableFourthContinuation (finiteMax_eq_seed_of_outside)
open P5OriginalCommonRefinedConstructor (OriginalData exponent5 common3 old3 policy4 policy5 level4 level5)
open P5OriginalCommonRefinedSeedHull (oldFifth commonInherited oldInherited oldFourth)
open P5OriginalFifthArchiveFallbackSeparation (inherited_eq_old_below_mu fifth_eq_old_below_mu)
open P5OriginalFifthArchiveFiniteIdentity (oldQ4 oldQ5 actual_fifth_carrier_iff_below_mu)
open P5OriginalCommonFifthPhysicalCaller (literalCharge raw_fourth_sub_fifth_eq_actualCharge
  normalized_actualCharge_eq_literalCharge)
open P1CorrectedFifthCausalTupleDictionary
open P4AOriginalVariableFifthPhysicalLedger (raw fifthTupleCharge fifthSaving_normalized_eq_tupleCharge)
open P1ActualVariableFifthGlobalSourceAssembly (normalizedSaving)
open P1ActualVariableFifthUntruncatedDomination (fullSelectedIntegral)
open P1OriginalFifthMovingScaleLimit (evenTargets)

theorem eligible_first_lt_mu (e : ℚ) (q : ℕ) (a : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ (data e q a).rows5) (t : Fin 5 → ℝ)
    (he : eligible e ((e : ℝ)/20) (refinedMesh q) a (data e q a).J5 r t) :
    t 0 < VariableEnvelope.mu := by
  rcases Finset.mem_union.mp hr with ho | hn
  · exact P5OriginalFifthArchiveFallbackSeparation.eligible_archive_first_lt_mu
      P5OriginalFourthFifthSourceInputs.originalRows4 P5OriginalFourthFifthSourceInputs.originalAdmission4
      e q ((e : ℝ)/20) a r ho t ((old_row_eligible_iff e q a r ho t).mp he)
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have hs := (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hj) t he.2.2).2.2.2
    have hu : ((rawRow i).upper 0 : ℝ) ≤ 39/200 := by exact_mod_cast (geometry i).2.2.1
    exact (hs 0).2.trans (hu.trans_lt (by norm_num [VariableEnvelope.mu]))

private theorem no_fifth_above (e : ℚ) (q : ℕ) (a N : ℝ) (pre : List ℕ)
    (hl : pre.length = 5) (hx : VariableEnvelope.mu ≤ primeHistoryLogCoordinates N 5 pre 0) :
    let d := data e q a
    oldFifth d N pre = oldInherited d N pre ∧ exponent5 d N pre = commonInherited d N pre := by
  let d := data e q a
  have hn : ∀ r ∈ d.rows5, ¬eligible d.e d.chi d.m d.omega d.J5 r (primeHistoryLogCoordinates N 5 pre) :=
    fun r hr he => (not_lt_of_ge hx) (eligible_first_lt_mu e q a r hr _ he)
  constructor
  · unfold oldFifth P1OriginalVariableFifthContinuation.exponent5
    rw [if_pos hl]
    exact finiteMax_eq_seed_of_outside _ _ _ _ hn
  · unfold exponent5
    rw [if_pos hl]
    exact finiteMax_eq_seed_of_outside _ _ _ _ hn

private theorem own_congr (N cap : ℕ) (Q R : List ℕ → ℝ) (pre : List ℕ) (h : Q pre = R pre) :
    actualOwnCubeGatedMinusDensity N cap Q pre = actualOwnCubeGatedMinusDensity N cap R pre := by
  simp only [actualOwnCubeGatedMinusDensity, h]

private theorem zero_local (Q4 Q5 : List ℕ → ℝ) (N cap : ℕ) (p : Fin 5 → ℕ)
    (h : Q5 (tupleHistory p) = Q4 (rosserAncestor 4 (tupleHistory p))) :
    literalTupleDifference Q4 Q5 N cap p = 0 := by
  have hraw := own_congr N cap Q5 (fun l => Q4 (rosserAncestor 4 l)) (tupleHistory p) h
  simp only [literalTupleDifference, hraw, sub_self, zero_mul, zero_div]

theorem same_local (e : ℚ) (q : ℕ) (a : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    let d := data e q a
    literalTupleDifference (level4 d (N : ℝ)) (level5 d (N : ℝ)) N cap p =
      literalTupleDifference (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ)) N cap p := by
  let d := data e q a
  have hl : (tupleHistory p).length = 5 := by simp [tupleHistory]
  by_cases hx : primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) 0 < VariableEnvelope.mu
  · have h4 := inherited_eq_old_below_mu d (N : ℝ) (tupleHistory p) hl hx.le
    have h5 := fifth_eq_old_below_mu d (N : ℝ) (tupleHistory p) hl hx.le
    have a4 := own_congr N cap
      (fun pre => level4 d (N : ℝ) (rosserAncestor 4 pre))
      (fun pre => oldQ4 d (N : ℝ) (rosserAncestor 4 pre)) (tupleHistory p)
      (congrArg (fun v : ℝ => (N : ℝ)^v) h4)
    have a5 := own_congr N cap (level5 d (N : ℝ)) (oldQ5 d (N : ℝ)) (tupleHistory p)
      (congrArg (fun v : ℝ => (N : ℝ)^v) h5)
    simp only [literalTupleDifference,a4,a5]
  · have he := no_fifth_above e q a (N : ℝ) (tupleHistory p) hl (le_of_not_gt hx)
    exact (zero_local (level4 d (N : ℝ)) (level5 d (N : ℝ)) N cap p
      (congrArg (fun v : ℝ => (N : ℝ)^v) he.2)).trans
      (zero_local (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ)) N cap p
        (congrArg (fun v : ℝ => (N : ℝ)^v) he.1)).symm

theorem true_literal_charge (e : ℚ) (q : ℕ) (a : ℝ) (N cap : ℕ) (z : ℝ) :
    let d := data e q a
    literalCharge d N cap z = fifthTupleCharge d.e d.chi d.m d.omega d.rows4 d.licensed4
      d.J5 d.rows5 N cap z := by
  let d := data e q a
  let A := firstExitFrontierTuples 4 (common3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z)
  let B := firstExitFrontierTuples 4 (old3 d (N : ℝ)) (roughPrimeUniverse N cap 0 z)
  let F := fun p : Fin 5 → ℕ => (∏ i, 1 / ((p i : ℝ)-1)) *
    literalTupleDifference (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ)) N cap p
  have hz (p : Fin 5 → ℕ) (hx : ¬Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu) :
      F p = 0 := by
    have hl : (tupleHistory p).length = 5 := by simp [tupleHistory]
    have hpre : VariableEnvelope.mu ≤ primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) 0 := by
      simpa only [tupleHistory_log] using le_of_not_gt hx
    have he := (no_fifth_above e q a (N : ℝ) (tupleHistory p) hl hpre).1
    have hzero := zero_local (oldQ4 d (N : ℝ)) (oldQ5 d (N : ℝ)) N cap p
      (congrArg (fun v : ℝ => (N : ℝ)^v) he)
    simp only [F,hzero,mul_zero]
  have hA : (∑ p ∈ A, F p) = ∑ p ∈ A ∪ B, F p := by
    apply Finset.sum_subset Finset.subset_union_left
    intro p hp hn
    by_cases hx : Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu
    · exact False.elim (hn ((actual_fifth_carrier_iff_below_mu d (N : ℝ) _ p hx.le).mpr
        ((Finset.mem_union.mp hp).resolve_left hn)))
    · exact hz p hx
  have hB : (∑ p ∈ B, F p) = ∑ p ∈ A ∪ B, F p := by
    apply Finset.sum_subset Finset.subset_union_right
    intro p hp hn
    by_cases hx : Real.log (p 0 : ℝ) / Real.log (N : ℝ) < VariableEnvelope.mu
    · exact False.elim (hn ((actual_fifth_carrier_iff_below_mu d (N : ℝ) _ p hx.le).mp
        ((Finset.mem_union.mp hp).resolve_right hn)))
    · exact hz p hx
  unfold literalCharge
  simp_rw [same_local e q a]
  exact hA.trans hB.symm

def unionIntegral (e : ℚ) (q : ℕ) (a : ℝ) : ℝ :=
  let d := data e q a
  fullSelectedIntegral d.e d.chi d.m d.omega d.rows4 d.licensed4 d.J5 d.rows5

def rawDifference (e : ℚ) (q : ℕ) (a : ℝ) (N cap : ℕ) : ℝ :=
  let d := data e q a
  let z := (N : ℝ) ^ (19/96 : ℝ)
  (raw (policy4 d (N : ℝ)) N cap 0 z - raw (policy5 d (N : ℝ)) N cap 0 z) *
    Real.log (N : ℝ) / singularSeries N

/-- Fixed-pre-N-mesh ordinary mean for the actual corrected common
fourth/fifth producer. The quantitative compact approximation at the
outer mesh parameters is a separate comparison of concrete integrals. -/
theorem tendsto_raw_union (e : ℚ) (he : 0 ≤ e) (q : ℕ) (a : ℝ)
    (ha : 0 < a) (har : a < 19/96) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets, (N : ℝ)^(19/96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => rawDifference e q a N (cap N)) evenTargets (𝓝 (unionIntegral e q a)) := by
  let d := data e q a
  apply (P1ActualVariableFifthFullMean.tendsto_normalizedSaving_fullSelectedIntegral
    d.e he d.chi d.m d.omega ha har d.rows4 d.licensed4 d.J5 d.rows5 cap hcap).congr'
  filter_upwards [(eventually_ge_atTop (1 : ℕ)).filter_mono
    (show evenTargets ≤ atTop from inf_le_left)] with N hN
  have hR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  change _ = rawDifference e q a N (cap N)
  unfold rawDifference
  rw [raw_fourth_sub_fifth_eq_actualCharge _ N (cap N) hR, normalized_actualCharge_eq_literalCharge,
    true_literal_charge, ← fifthSaving_normalized_eq_tupleCharge]
  rfl

end
end ImbalancedChen.P4AOriginalNewFifthMean

