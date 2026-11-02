import ImbalancedChen.P2OriginalI3ActualCompactKernel
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.ActualPrimeBoxInitialSavingIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The complete original I3 frontier is reindexed, with multiplicity proved,
onto the independently defined ADMITTED prime tuples. All original target
deletions and tests remain. The frozen quotient and logarithmic profile
use all three selected primes. This supplies the arithmetic source of a
future integral argument; it does not assert a fixed-domain integral limit.
-/
namespace ImbalancedChen.P2OriginalI3AdmittedPrimeTupleSource
noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ProjectionAttachmentDefects
open P2OriginalI3FullRawActualPlusDensity
open P2OriginalI3ActualCompactKernel
open MathlibNt.SieveTheory

def history (p : Fin 3 → ℕ) : List ℕ := (List.ofFn p).reverse

def tuples {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (z : ℝ) :
    Finset (Fin 3 → ℕ) :=
  firstExitAdmittedTuples 3 (D.oldPolicy N) (roughPrimeUniverse N cap 0 z)

def tupleWeight (p : Fin 3 → ℕ) : ℝ := ∏ i, 1 / ((p i : ℝ) - 1)

def newCap {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) (pre : List ℕ) : ℝ :=
  (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap

def rawKernel {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (pre : List ℕ) : ℝ :=
  actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ)^(baselineCap D.rho) / (pre.prod : ℝ)) -
    actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
      ((N : ℝ)^(newCap D N pre) / (pre.prod : ℝ))

def profileKernel {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ) (pre : List ℕ) : ℝ :=
  frozenPlusProfile N pre (baselineCap D.rho) -
    frozenPlusProfile N pre (newCap D N pre)

theorem history_tuple (p : Fin 3 → ℕ) : primeHistoryTuple 3 (history p) = p := by
  apply List.ofFn_injective
  rw [primeHistoryTuple_ofFn (by simp [history])]
  simp [history]

theorem history_prod (p : Fin 3 → ℕ) : (history p).prod = ∏ i, p i := by
  simp [history, List.prod_ofFn]

theorem history_head (p : Fin 3 → ℕ) : (history p).headD 0 = p 2 := by
  have h := primeHistoryTuple_last (k := 2) (history := history p) (by simp [history])
  rw [history_tuple] at h
  exact h.symm

/-- Membership has the original fully admitted source, not a freely chosen
box or a next-candidate frontier. The cap may truncate the prime universe. -/
theorem mem_tuples_iff {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (p : Fin 3 → ℕ) :
    p ∈ tuples D N cap z ↔ StrictAnti p ∧
      (∀ i, p i ∈ roughPrimeUniverse N cap 0 z) ∧
      FirstExitValidSelection (D.oldPolicy N) [] true (List.ofFn p) :=
  mem_firstExitAdmittedTuples_iff_of_decreasing 3 (D.oldPolicy N) _
    (roughPrimeUniverse_pairwise_gt N cap 0 z) p

/-- Each admitted tuple comes from an actual state of the original recursion.
The inverse is established before using the pointwise G density estimate. -/
theorem exists_state_of_mem_tuples {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (p : Fin 3 → ℕ) (hp : p ∈ tuples D N cap z) :
    ∃ state ∈ firstExitDepthFrontier 3 (D.oldPolicy N)
      (fun q => 1 / ((q : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      state.selectedPrefix = history p ∧ state.mass = tupleWeight p := by
  have hmem : p ∈ ((firstExitAdmittedChoices 3 (D.oldPolicy N) [] true
      (roughPrimeUniverse N cap 0 z)).map
        (fun chosen => primeHistoryTuple 3 chosen.reverse)) :=
    List.mem_toFinset.mp hp
  have hperm := firstExitRootFrontier_admitted_tuple_perm 3 (D.oldPolicy N)
    (fun q => 1 / ((q : ℝ)-1)) (roughPrimeUniverse N cap 0 z)
  obtain ⟨state, hs, he⟩ := List.mem_map.mp (hperm.mem_iff.mpr hmem)
  have hg := actualPrimeFrontier_geometry 3 (by norm_num) (D.oldPolicy N) N cap z state hs
  refine ⟨state, hs, ?_, ?_⟩
  · rw [history, ← he, primeHistoryTuple_reverse_ofFn hg.1]
  · rw [hg.2.2.2.2.2.2, tupleWeight, ← he, primeHistoryTuple_reciprocal_mass hg.1]

/-- Exact, complete raw I3 on the original arithmetic tuple carrier. -/
theorem complete_raw_I3_eq_admitted_tuple_sum {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (hN : 1 < (N : ℝ)) :
    rawDensity (thirdRetain D N) N cap 0 z - rawDensity (seedRetain D N) N cap 0 z =
      ∑ p ∈ tuples D N cap z, tupleWeight p * rawKernel D N cap (history p) := by
  rw [complete_raw_I3_eq_actual_plus_frontier D N cap z hN]
  simp only [ThirdStage.taggedFrontier, List.map_map, Function.comp_apply]
  calc
    _ = ((firstExitDepthFrontier 3 (D.oldPolicy N) (fun q => 1 / ((q : ℝ)-1))
        [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun state =>
          (state.selectedPrefix.map (fun q => 1 / ((q : ℝ)-1))).prod *
            rawKernel D N cap state.selectedPrefix)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state hs
      have hm := mem_firstExitDepthFrontier_mass_eq_selected_prod 3 (D.oldPolicy N)
        (fun q => 1 / ((q : ℝ)-1)) (roughPrimeUniverse N cap 0 z) state hs
      simp only [actualFullI3PlusTerm, rawKernel, newCap, hm]
    _ = _ := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 3
      (D.oldPolicy N) (fun q => 1 / ((q : ℝ)-1)) (roughPrimeUniverse N cap 0 z)
      (roughPrimeUniverse_nodup N cap 0 z) (rawKernel D N cap)

/-- The G profile also reindexes on this SAME arithmetic source. -/
theorem complete_profile_eq_admitted_tuple_sum {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) :
    ((D.taggedFrontier N cap z (fun q => 1 / ((q : ℝ)-1))).map
      (actualFullI3ProfileTerm D N)).sum =
      ∑ p ∈ tuples D N cap z, tupleWeight p * profileKernel D N (history p) := by
  simp only [ThirdStage.taggedFrontier, List.map_map, Function.comp_apply]
  calc
    _ = ((firstExitDepthFrontier 3 (D.oldPolicy N) (fun q => 1 / ((q : ℝ)-1))
        [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun state =>
          (state.selectedPrefix.map (fun q => 1 / ((q : ℝ)-1))).prod *
            profileKernel D N state.selectedPrefix)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro state hs
      have hm := mem_firstExitDepthFrontier_mass_eq_selected_prod 3 (D.oldPolicy N)
        (fun q => 1 / ((q : ℝ)-1)) (roughPrimeUniverse N cap 0 z) state hs
      simp only [actualFullI3ProfileTerm, profileKernel, newCap, hm]
    _ = _ := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 3
      (D.oldPolicy N) (fun q => 1 / ((q : ℝ)-1)) (roughPrimeUniverse N cap 0 z)
      (roughPrimeUniverse_nodup N cap 0 z) (profileKernel D N)

/-- The exact upper sieve kernel in the original prime logarithms. In
particular the denominator of the quotient removes all three primes. -/
theorem profileKernel_eq_log_kernel {mesh : ℕ} (D : ThirdStage mesh)
    (N : ℕ) (p : Fin 3 → ℕ) (hpos : ∀ i, 0 < p i) :
    profileKernel D N (history p) =
      let t := actualPrimeTupleLog N p
      (2 * Real.exp (-Real.eulerMascheroniConstant) / t 2) *
        (suzukiContinuousUpperFactor ((baselineCap D.rho - ∑ i, t i) / t 2) -
          suzukiContinuousUpperFactor ((newCap D N (history p) - ∑ i, t i) / t 2)) := by
  have hpar (lambda : ℝ) :
      actualRosserQuotientParameters (N : ℝ) ((history p).prod : ℝ)
        ((history p).headD 0 : ℝ) lambda =
      (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p 2) := by
    rw [history_prod, history_head, actualPrimeTupleLog_sum_prod p hpos]
    rfl
  simp only [profileKernel, frozenPlusProfile, hpar]
  ring

/-- The genuine Lebesgue density to which the prime harmonic dictionary
leads. This definition is independent of prime enumeration and uses the
ordinary UPPER factor at both frozen levels. -/
def plusLogIntegrand (lambdaOld lambdaNew : ℝ) (t : Fin 3 → ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) *
    (suzukiContinuousUpperFactor ((lambdaOld - ∑ i, t i) / t 2) -
      suzukiContinuousUpperFactor ((lambdaNew - ∑ i, t i) / t 2))) /
    (t 0 * t 1 * (t 2)^2)

/-- Exact source-to-integrand normalization. The prime harmonic measure
supplies one factor 1/t_i per coordinate and the residual contributes the
second 1/t_2. No statement of convergence to this integral is assumed. -/
theorem actual_profile_harmonic_density_eq_integrand {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z : ℝ) (hN : 1 < (N : ℝ))
    (p : Fin 3 → ℕ) (hp : p ∈ tuples D N cap z) :
    profileKernel D N (history p) * (∏ i, 1 / actualPrimeTupleLog N p i) =
      plusLogIntegrand (baselineCap D.rho) (newCap D N (history p))
        (actualPrimeTupleLog N p) := by
  have hprime (i : Fin 3) : (p i).Prime :=
    mem_roughPrimeUniverse_prime (((mem_tuples_iff D N cap z p).mp hp).2.1 i)
  have ht (i : Fin 3) : 0 < actualPrimeTupleLog N p i := by
    have hpi : (1 : ℝ) < p i := by exact_mod_cast (hprime i).one_lt
    exact div_pos (Real.log_pos hpi) (Real.log_pos hN)
  rw [profileKernel_eq_log_kernel D N p (fun i => (hprime i).pos), Fin.prod_univ_three]
  dsimp only [plusLogIntegrand]
  field_simp [(ht 0).ne', (ht 1).ne', (ht 2).ne']
  <;> ring

end
end ImbalancedChen.P2OriginalI3AdmittedPrimeTupleSource
