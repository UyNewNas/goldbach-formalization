import ImbalancedChen.P1ActualUpperClosedParameterUniformity
import ImbalancedChen.P1ActualUpperNearOneBound
import ImbalancedChen.P1ActualCoarseLevelCeiling
import ImbalancedChen.P1CoarseFirstCubeFallbackMargin
import ImbalancedChen.FirstExitAdmittedFrontierTuples
import ImbalancedChen.P1OriginalCoarseContinuationCells

/-!
# Actual rank-four residual suppliers on the original coarse T3 policy

SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.

The carrier below is literally `HistoricalThirdCoarse.policy`, with its
original first stop, natural-prime activation, selected Gamma values and
Theta fallback.  No arbitrary `HistoricalPrefixCapData` is substituted.
The actual third admission supplies the inherited strict third cube.
Ordering then gives legal upper residuals at rank four without a whole-box
margin.  A fixed positive last-prime cutoff and the actual finite exponent
table place all these quotient parameters in one closed compact window.

This is a uniform arithmetic density supplier before prime summation or
integration.  No mean-value premise or final historical integral is asserted.
-/

namespace ImbalancedChen

noncomputable section
open scoped Classical BigOperators
open Filter Topology
open MathlibNt.SieveTheory

namespace HistoricalThirdCoarse.P1OriginalUpperResidual

/-- Exactly the original T3 admitted rank-four carrier. -/
def admittedTuples (e chi : ℝ) (m : ℕ) (omega rho : ℝ) (N cap : ℕ) :
    Finset (Fin 4 → ℕ) :=
  firstExitAdmittedTuples 4 (policy e chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho))

def thirdHistory (p : Fin 4 → ℕ) : List ℕ := [p 2, p 1, p 0]

/-- This is the actual selected-or-fallback exponent of raw Q3. -/
def oldExponent (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  P1CoarseFirstCubeFallbackMargin.effectiveExponent e chi m omega (N : ℝ) (thirdHistory p)

def oldLevel (e chi : ℝ) (m : ℕ) (omega : ℝ) (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  rawLevel e chi m omega (N : ℝ) (thirdHistory p)

def normalizedResidual (N cap : ℕ) (p : Fin 4 → ℕ) (Q : ℝ) : ℝ :=
  actualSmallRosserPlusDensity N cap (p 3 : ℝ) (Q / (∏ i, p i : ℕ)) *
    Real.log (N : ℝ) / singularSeries N

def closedProfile (N : ℕ) (p : Fin 4 → ℕ) (lambda : ℝ) : ℝ :=
  (2 * Real.exp (-Real.eulerMascheroniConstant) / actualPrimeTupleLog N p 3) *
    P1FourthNearOneKernel.closedUpper
      ((lambda - ∑ i, actualPrimeTupleLog N p i) / actualPrimeTupleLog N p 3)

/-- Raw active-unselected and inactive histories both keep the Theta
entry of the same actual finite exponent table. -/
theorem oldExponent_mem_values (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (p : Fin 4 → ℕ) :
    oldExponent e chi m omega N p ∈ P1ActualCoarseLevelCeiling.exponentValues e chi m := by
  unfold oldExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
  split_ifs with hs
  · exact P1ActualCoarseLevelCeiling.exponent_mem_values e chi m _
  · simp [P1ActualCoarseLevelCeiling.exponentValues]

theorem oldExponent_le_initial (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ)
    (N : ℕ) (p : Fin 4 → ℕ) : oldExponent e chi m omega N p ≤ initial e := by
  exact P1ActualCoarseLevelCeiling.exponentValues_subset_initial e chi he m
    (oldExponent_mem_values e chi m omega N p)

theorem oldLevel_eq_rpow (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (p : Fin 4 → ℕ) :
    oldLevel e chi m omega N p = (N : ℝ) ^ oldExponent e chi m omega N p := by
  exact P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent
    e chi m omega (N : ℝ) (thirdHistory p)

theorem admitted_tuple_data (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (p : Fin 4 → ℕ) (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    StrictAnti p ∧ (∀ i, Nat.Prime (p i)) ∧
      (∀ i, p i ∈ roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho)) ∧
      FirstExitValidSelection (policy e chi m omega (N : ℝ)) [] true (List.ofFn p) := by
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (policy e chi m omega (N : ℝ)) _
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ rho)) p).mp hp
  exact ⟨hd.1, fun i => mem_roughPrimeUniverse_prime (hd.2.1 i), hd.2.1, hd.2.2⟩

/-- The inherited third test is obtained from real admission, rather than
supplied as a geometry field. -/
theorem old_third_cube_log (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
        3 * actualPrimeTupleLog N p 2 < oldExponent e chi m omega N p := by
  obtain ⟨ha, hprime, _hmem, hv⟩ := admitted_tuple_data e chi m omega rho N cap p hp
  have hpos : ∀ i, 0 < p i := fun i => (hprime i).pos
  have hof : List.ofFn p = [p 0, p 1, p 2, p 3] := by simp [List.ofFn_succ]
  rw [hof] at hv
  have hthird : policy e chi m omega (N : ℝ) false [p 2, p 1, p 0] = true := hv.2.2.1
  have hc := ((policy_third_iff e chi m omega (N : ℝ) (p 0) (p 1) (p 2)
    (hpos 2) (ha (by decide : (1 : Fin 4) < 2))
    (ha (by decide : (0 : Fin 4) < 1))).mp hthird).2
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hcube : (N : ℝ) ^ (3 * actualPrimeTupleLog N p 2) = (p 2 : ℝ) ^ 3 := by
    rw [show 3 * actualPrimeTupleLog N p 2 = actualPrimeTupleLog N p 2 * 3 by ring,
      Real.rpow_mul hn0.le, actualPrimeTupleLog_rpow hN p hpos]
    norm_num
  have hprod : (N : ℝ) ^ (actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
      3 * actualPrimeTupleLog N p 2) = (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 := by
    rw [Real.rpow_add hn0, Real.rpow_add hn0,
      actualPrimeTupleLog_rpow hN p hpos, actualPrimeTupleLog_rpow hN p hpos, hcube]
  apply (Real.rpow_lt_rpow_left_iff hn).mp
  rw [hprod, ← oldLevel_eq_rpow]
  simpa only [oldLevel, thirdHistory, Nat.cast_pow] using hc

/-- Pointwise legality can approach one; there is no whole-box sigma. -/
theorem old_plus_legality (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 <
      oldExponent e chi m omega N p := by
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hs := (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hd.2.1 i).pos)).mpr hd.1
  have hc := old_third_cube_log e chi m omega rho N cap hN p hp
  have h32 := hs (by decide : (2 : Fin 4) < 3)
  have hsum : (∑ i, actualPrimeTupleLog N p i) = actualPrimeTupleLog N p 0 +
      actualPrimeTupleLog N p 1 + actualPrimeTupleLog N p 2 + actualPrimeTupleLog N p 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  linarith

theorem admitted_log_pos (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    ∀ i, 0 < actualPrimeTupleLog N p i := by
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  intro i
  have hpi : (1 : ℝ) < p i := by exact_mod_cast (hd.2.1 i).one_lt
  exact div_pos (Real.log_pos hpi) (Real.log_pos hn)

theorem admitted_last_bounds (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    actualPrimeTupleLog N p 3 < rho ∧ (p 3 : ℝ) ≤ (cap : ℝ) := by
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hm := mem_roughPrimeUniverse.mp (hd.2.2.1 3)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  constructor
  · apply (Real.rpow_lt_rpow_left_iff hn).mp
    rw [actualPrimeTupleLog_rpow hN p (fun i => (hd.2.1 i).pos)]
    exact hm.2.2.2.2
  · exact_mod_cast hm.1.le

theorem quotientParameters_eq_tuple (N : ℕ) (p : Fin 4 → ℕ)
    (hpos : ∀ i, 0 < p i) (lambda : ℝ) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) lambda =
      (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p 3) := by
  unfold actualRosserQuotientParameters
  rw [← actualPrimeTupleLog_sum_prod p hpos]
  rfl

def residualWindow (a rho Theta : ℝ) : Set (ℝ × ℝ) :=
  (Set.Icc a Theta ×ˢ Set.Icc a rho) ∩ {q : ℝ × ℝ | q.2 ≤ q.1}

theorem residualWindow_isCompact (a rho Theta : ℝ) :
    IsCompact (residualWindow a rho Theta) := by
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_snd continuous_fst)

theorem residualWindow_legal (a rho Theta : ℝ) (ha : 0 < a) :
    ∀ q ∈ residualWindow a rho Theta, 0 < q.2 ∧ q.2 ≤ q.1 := by
  intro q hq
  exact ⟨ha.trans_le hq.1.2.1, hq.2⟩

/-- Only finite coordinate/exponent inequalities are used to enter the
compact quotient domain.  The full tuple product remains in P. -/
theorem quotientParameters_mem_window (a rho Theta : ℝ) (N : ℕ)
    (p : Fin 4 → ℕ) (hpos : ∀ i, 0 < p i) (lambda : ℝ)
    (htpos : ∀ i, 0 ≤ actualPrimeTupleLog N p i)
    (hlo : a ≤ actualPrimeTupleLog N p 3) (hhi : actualPrimeTupleLog N p 3 ≤ rho)
    (hlegal : actualPrimeTupleLog N p 3 ≤ lambda - ∑ i, actualPrimeTupleLog N p i)
    (hTheta : lambda ≤ Theta) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) lambda ∈
      residualWindow a rho Theta := by
  rw [quotientParameters_eq_tuple N p hpos lambda]
  have hsum : 0 ≤ ∑ i, actualPrimeTupleLog N p i := Finset.sum_nonneg (fun i _ => htpos i)
  exact ⟨⟨⟨hlo.trans hlegal, by linarith⟩, ⟨hlo, hhi⟩⟩, hlegal⟩

theorem old_quotientParameters_mem_window (a rho : ℝ) (e chi : ℝ) (he : 0 ≤ e)
    (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap)
    (hcut : (N : ℝ) ^ a ≤ (p 3 : ℝ)) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ)
        (oldExponent e chi m omega N p) ∈ residualWindow a rho (initial e) := by
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlo : a ≤ actualPrimeTupleLog N p 3 := by
    apply (Real.rpow_le_rpow_left_iff hn).mp
    rw [actualPrimeTupleLog_rpow hN p (fun i => (hd.2.1 i).pos)]
    exact hcut
  apply quotientParameters_mem_window a rho (initial e) N p (fun i => (hd.2.1 i).pos)
    (oldExponent e chi m omega N p)
  · exact fun i => (admitted_log_pos e chi m omega rho N cap hN p hp i).le
  · exact hlo
  · exact (admitted_last_bounds e chi m omega rho N cap hN p hp).1.le
  · linarith [old_plus_legality e chi m omega rho N cap hN p hp]
  · exact oldExponent_le_initial e chi he m omega N p

/-- One threshold precedes EVERY rough-activation omega and every actual
original admitted tuple.  The original finite table, not an abstract D,
supplies the global Theta ceiling. -/
theorem exists_original_old_uniform_error (a rho : ℝ) (ha : 0 < a)
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ omega : ℝ, ∀ cap : ℕ, ∀ p ∈ admittedTuples e chi m omega rho N cap,
        (N : ℝ) ^ a ≤ (p 3 : ℝ) →
          |normalizedResidual N cap p (oldLevel e chi m omega N p) -
            closedProfile N p (oldExponent e chi m omega N p)| < eta := by
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_quotient_compact_normalized_threshold
      (residualWindow a rho (initial e)) (residualWindow_isCompact _ _ _)
      (residualWindow_legal _ _ _ ha) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven omega cap p hp hcut
  have hNnat : 1 < N := by omega
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).pos
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p 3 := by exact_mod_cast hpos 3
  have hmem := old_quotientParameters_mem_window a rho e chi he m omega N cap hNnat p hp hcut
  have hcap := (admitted_last_bounds e chi m omega rho N cap hNnat p hp).2
  have h := hbound N hN hEven (∏ i, p i : ℕ) (p 3 : ℝ)
    (oldExponent e chi m omega N p) hP hy hmem cap hcap
  rw [quotientParameters_eq_tuple N p hpos] at h
  unfold normalizedResidual closedProfile
  rw [oldLevel_eq_rpow]
  exact h

/-- The actual original old Q3 quotient is above its last prime. -/
theorem old_last_lt_quotient (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples e chi m omega rho N cap) :
    (p 3 : ℝ) < oldLevel e chi m omega N p / (∏ i, p i : ℕ) := by
  have hd := admitted_tuple_data e chi m omega rho N cap p hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).pos
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  rw [oldLevel_eq_rpow, ← residual_rpow_level_div _ _ _ hn hP,
    ← actualPrimeTupleLog_sum_prod p hpos, ← actualPrimeTupleLog_rpow hN p hpos 3,
    Real.rpow_lt_rpow_left_iff hn]
  linarith [old_plus_legality e chi m omega rho N cap hN p hp]

theorem exists_original_old_uniform_absolute_bound (a rho : ℝ) (ha : 0 < a)
    (e chi : ℝ) (m : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ omega : ℝ, ∀ cap : ℕ, ∀ p ∈ admittedTuples e chi m omega rho N cap,
        (N : ℝ) ^ a ≤ (p 3 : ℝ) →
          |normalizedResidual N cap p (oldLevel e chi m omega N p)| ≤ M := by
  obtain ⟨M, hM, N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound a ha
  refine ⟨M, hM, N0, hN0, ?_⟩
  intro N hN hEven omega cap p hp hcut
  have hNnat : 1 < N := by omega
  have hcap := (admitted_last_bounds e chi m omega rho N cap hNnat p hp).2
  exact hbound N hN hEven cap (p 3 : ℝ)
    (oldLevel e chi m omega N p / (∏ i, p i : ℕ)) hcut
    (old_last_lt_quotient e chi m omega rho N cap hNnat p hp).le hcap

def fourthHistory (p : Fin 4 → ℕ) : List ℕ := [p 3, p 2, p 1, p 0]

theorem thirdAncestor_fourthHistory (p : Fin 4 → ℕ) :
    rosserAncestor 3 (fourthHistory p) = thirdHistory p := by
  simp [rosserAncestor, fourthHistory, thirdHistory]

def newExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  P1OriginalCoarseContinuation.effectiveExponent4 e chi m omega J4 cap4
    (N : ℝ) (fourthHistory p)

def newLevel (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (N : ℕ) (p : Fin 4 → ℕ) : ℝ :=
  P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4 (N : ℝ) (fourthHistory p)

theorem newLevel_eq_rpow (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (N : ℕ) (p : Fin 4 → ℕ) :
    newLevel e chi m omega J4 cap4 N p =
      (N : ℝ) ^ newExponent e chi m omega J4 cap4 N p := by rfl

/-- The range envelope uses all supplied labels, so it precedes omega as
well as N.  Actual selected fourth cells are a subset of those labels. -/
def allFourthExponentValues (e : ℚ) (chi : ℝ) (m : ℕ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ) : Finset ℚ :=
  P1OriginalCoarseContinuation.thirdExponentValues e chi m ∪ J4.image cap4

theorem newExponent_mem_finite_values (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (N : ℕ) (p : Fin 4 → ℕ) :
    newExponent e chi m omega J4 cap4 N p ∈
      (allFourthExponentValues e chi m J4 cap4).image (fun q : ℚ => (q : ℝ)) := by
  have hm := P1OriginalCoarseContinuation.effectiveExponent4Q_mem_values
    e chi m omega J4 cap4 (N : ℝ) (fourthHistory p)
  have hwide : P1OriginalCoarseContinuation.effectiveExponent4Q
      e chi m omega J4 cap4 (N : ℝ) (fourthHistory p) ∈
        allFourthExponentValues e chi m J4 cap4 := by
    rcases Finset.mem_union.mp hm with hthird | hfourth
    · exact Finset.mem_union_left _ hthird
    · obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hfourth
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j,
        ((P1OriginalCoarseContinuation.mem_selectedFourthCells e chi m omega J4 j).mp hj).1,
        hjv⟩
  exact Finset.mem_image.mpr ⟨_, hwide, rfl⟩

/-- A real ceiling is derived from the ACTUAL finite fourth exponent
table.  No caller-supplied density or infinite-family ceiling is needed. -/
theorem exists_new_uniform_exponent_ceiling (e : ℚ) (chi : ℝ) (m : ℕ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ) :
    ∃ Theta : ℝ, initial (e : ℝ) ≤ Theta ∧ ∀ omega : ℝ, ∀ N : ℕ,
      ∀ p : Fin 4 → ℕ, newExponent e chi m omega J4 cap4 N p ≤ Theta := by
  let V : Finset ℝ := (allFourthExponentValues e chi m J4 cap4).image
    (fun q : ℚ => (q : ℝ))
  obtain ⟨B, hB⟩ := V.finite_toSet.isCompact.bddAbove
  refine ⟨max (initial (e : ℝ)) B, le_max_left _ _, ?_⟩
  intro omega N p
  exact (hB (newExponent_mem_finite_values e chi m omega J4 cap4 N p)).trans
    (le_max_right _ _)

theorem oldLevel_eq_frozenThird (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N : ℕ) (p : Fin 4 → ℕ) :
    oldLevel e chi m omega N p = frozenLevel e chi m omega (N : ℝ) (fourthHistory p) := by
  unfold frozenLevel
  rw [thirdAncestor_fourthHistory]
  rfl

/-- The actual checked original h34 is used only as a finite level
comparison; inherited original admission supplies the old legality. -/
theorem oldLevel_le_newLevel (e : ℚ) (chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (hcheck : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples (e : ℝ) chi m omega rho N cap) :
    oldLevel (e : ℝ) chi m omega N p ≤ newLevel e chi m omega J4 cap4 N p := by
  have hd := admitted_tuple_data (e : ℝ) chi m omega rho N cap p hp
  have hpos : ∀ q ∈ fourthHistory p, 0 < q := by
    intro q hq
    simp only [fourthHistory, List.mem_cons, List.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> exact (hd.2.1 _).pos
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hc := P1OriginalCoarseContinuation.frozenLevel_le_level4
    e chi m omega J4 cap4 (N : ℝ) (fourthHistory p) hcheck hn
      (by simp [fourthHistory]) hpos
  rw [← oldLevel_eq_frozenThird] at hc
  exact hc

theorem oldExponent_le_newExponent (e : ℚ) (chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (hcheck : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (N cap : ℕ) (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : p ∈ admittedTuples (e : ℝ) chi m omega rho N cap) :
    oldExponent (e : ℝ) chi m omega N p ≤ newExponent e chi m omega J4 cap4 N p := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  apply (Real.rpow_le_rpow_left_iff hn).mp
  rw [← oldLevel_eq_rpow, ← newLevel_eq_rpow]
  exact oldLevel_le_newLevel e chi m omega rho J4 cap4 hcheck N cap hN p hp

theorem exists_original_new_uniform_error (a rho : ℝ) (ha : 0 < a)
    (e : ℚ) (chi : ℝ) (m : ℕ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ omega : ℝ, P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true →
        ∀ cap : ℕ, ∀ p ∈ admittedTuples (e : ℝ) chi m omega rho N cap,
          (N : ℝ) ^ a ≤ (p 3 : ℝ) →
            |normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p) -
              closedProfile N p (newExponent e chi m omega J4 cap4 N p)| < eta := by
  obtain ⟨Theta, _hInitial, hTheta⟩ := exists_new_uniform_exponent_ceiling e chi m J4 cap4
  obtain ⟨N0, hN0, hbound⟩ :=
    exists_p1_actualSmallRosserPlusDensity_closed_quotient_compact_normalized_threshold
      (residualWindow a rho Theta) (residualWindow_isCompact _ _ _)
      (residualWindow_legal _ _ _ ha) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven omega hcheck cap p hp hcut
  have hNnat : 1 < N := by omega
  have hn : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hd := admitted_tuple_data (e : ℝ) chi m omega rho N cap p hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).pos
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast Finset.prod_pos (fun i _ => hpos i)
  have hy : (0 : ℝ) < p 3 := by exact_mod_cast hpos 3
  have hlo : a ≤ actualPrimeTupleLog N p 3 := by
    apply (Real.rpow_le_rpow_left_iff hn).mp
    rw [actualPrimeTupleLog_rpow hNnat p hpos]
    exact hcut
  have hmem : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ)
      (newExponent e chi m omega J4 cap4 N p) ∈ residualWindow a rho Theta := by
    apply quotientParameters_mem_window a rho Theta N p hpos _
    · exact fun i => (admitted_log_pos (e : ℝ) chi m omega rho N cap hNnat p hp i).le
    · exact hlo
    · exact (admitted_last_bounds (e : ℝ) chi m omega rho N cap hNnat p hp).1.le
    · have hold := old_plus_legality (e : ℝ) chi m omega rho N cap hNnat p hp
      have hle := oldExponent_le_newExponent e chi m omega rho J4 cap4 hcheck N cap hNnat p hp
      linarith
    · exact hTheta omega N p
  have hcap := (admitted_last_bounds (e : ℝ) chi m omega rho N cap hNnat p hp).2
  have h := hbound N hN hEven (∏ i, p i : ℕ) (p 3 : ℝ)
    (newExponent e chi m omega J4 cap4 N p) hP hy hmem cap hcap
  rw [quotientParameters_eq_tuple N p hpos] at h
  unfold normalizedResidual closedProfile
  rw [newLevel_eq_rpow]
  exact h

/-- Both original actual residual legs have common normalized bounds and
errors before omega, N, the cap and the admitted tuple. -/
theorem exists_original_old_new_uniform_suppliers (a rho : ℝ) (ha : 0 < a)
    (e : ℚ) (chi : ℝ) (he : 0 ≤ (e : ℝ)) (m : ℕ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ omega : ℝ, P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true →
        ∀ cap : ℕ, ∀ p ∈ admittedTuples (e : ℝ) chi m omega rho N cap,
          (N : ℝ) ^ a ≤ (p 3 : ℝ) →
            (|normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p)| ≤ M ∧
              |normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p)| ≤ M) ∧
            |normalizedResidual N cap p (oldLevel (e : ℝ) chi m omega N p) -
                closedProfile N p (oldExponent (e : ℝ) chi m omega N p)| < eta ∧
            |normalizedResidual N cap p (newLevel e chi m omega J4 cap4 N p) -
                closedProfile N p (newExponent e chi m omega J4 cap4 N p)| < eta := by
  obtain ⟨M, hM, NB, hNB, hB⟩ :=
    exists_p1_actualSmallRosserPlusDensity_endpoint_normalized_bound a ha
  obtain ⟨NO, _hNO, hOld⟩ := exists_original_old_uniform_error a rho ha (e : ℝ) chi he m eta heta
  obtain ⟨NN, _hNN, hNew⟩ := exists_original_new_uniform_error a rho ha e chi m J4 cap4 eta heta
  refine ⟨M, hM, max NB (max NO NN), hNB.trans (le_max_left _ _), ?_⟩
  intro N hN hEven omega hcheck cap p hp hcut
  have hNB' : NB ≤ N := (le_max_left _ _).trans hN
  have hNO' : NO ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNN' : NN ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNnat : 1 < N := by omega
  have hcap := (admitted_last_bounds (e : ℝ) chi m omega rho N cap hNnat p hp).2
  have hold := (old_last_lt_quotient (e : ℝ) chi m omega rho N cap hNnat p hp).le
  have hd := admitted_tuple_data (e : ℝ) chi m omega rho N cap p hp
  have hP0 : (0 : ℝ) ≤ (∏ i, p i : ℕ) := Nat.cast_nonneg _
  have hlevels := oldLevel_le_newLevel e chi m omega rho J4 cap4 hcheck N cap hNnat p hp
  have hnew := hold.trans (div_le_div_of_nonneg_right hlevels hP0)
  exact ⟨⟨hB N hNB' hEven cap _ _ hcut hold hcap,
    hB N hNB' hEven cap _ _ hcut hnew hcap⟩,
    hOld N hNO' hEven omega cap p hp hcut,
    hNew N hNN' hEven omega hcheck cap p hp hcut⟩

/-- Exact reverse-history representation, used only for the real rank-four
frontier.  The natural history product and head prime are retained. -/
def historyNormalizedResidual (N cap : ℕ) (history : List ℕ) (Q : ℝ) : ℝ :=
  actualSmallRosserPlusDensity N cap (history.headD 0 : ℝ) (Q / (history.prod : ℝ)) *
    Real.log (N : ℝ) / singularSeries N

theorem normalizedResidual_primeHistoryTuple (N cap : ℕ) {history : List ℕ}
    (hlen : history.length = 4) (Q : ℝ) :
    normalizedResidual N cap (primeHistoryTuple 4 history) Q =
      historyNormalizedResidual N cap history Q := by
  unfold normalizedResidual historyNormalizedResidual
  rw [primeHistoryTuple_prod hlen, primeHistoryTuple_last hlen]

theorem fourthHistory_primeHistoryTuple {history : List ℕ} (hlen : history.length = 4) :
    fourthHistory (primeHistoryTuple 4 history) = history := by
  calc
    fourthHistory (primeHistoryTuple 4 history) =
        (List.ofFn (primeHistoryTuple 4 history)).reverse := by
      simp [fourthHistory, List.ofFn_succ]
    _ = history := primeHistoryTuple_reverse_ofFn hlen

theorem frontier_tuple_mem_admitted (e chi : ℝ) (m : ℕ) (omega rho : ℝ)
    (N cap : ℕ) (weight : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4 (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho))) :
    primeHistoryTuple 4 state.selectedPrefix ∈ admittedTuples e chi m omega rho N cap := by
  have hm : primeHistoryTuple 4 state.selectedPrefix ∈
      (firstExitDepthFrontier 4 (policy e chi m omega (N : ℝ)) weight [] true 1
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho))).map
          (fun s => primeHistoryTuple 4 s.selectedPrefix) :=
    List.mem_map.mpr ⟨state, hstate, rfl⟩
  have ht := (firstExitRootFrontier_admitted_tuple_perm 4
    (policy e chi m omega (N : ℝ)) weight
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho))).mem_iff.mp hm
  simpa only [admittedTuples, firstExitAdmittedTuples, List.mem_toFinset] using ht

/-- The original actual rank-four frontier gets the same suppliers, with
its own reverse history, head prime, product and frozen raw Q3.  There is
no separate validity or normalized-density assumption on frontier states. -/
theorem exists_original_frontier_old_new_uniform_suppliers (a rho : ℝ) (ha : 0 < a)
    (e : ℚ) (chi : ℝ) (he : 0 ≤ (e : ℝ)) (m : ℕ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (cap4 : P1OriginalCoarseContinuation.FourthCell m → ℚ)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ omega : ℝ, P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true →
        ∀ cap : ℕ, ∀ weight : ℕ → ℝ, ∀ state ∈
          firstExitDepthFrontier 4 (policy (e : ℝ) chi m omega (N : ℝ)) weight [] true 1
            (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho)),
          (N : ℝ) ^ a ≤ (state.selectedPrefix.headD 0 : ℝ) →
          let p := primeHistoryTuple 4 state.selectedPrefix
          (|historyNormalizedResidual N cap state.selectedPrefix
              (frozenLevel (e : ℝ) chi m omega (N : ℝ) state.selectedPrefix)| ≤ M ∧
            |historyNormalizedResidual N cap state.selectedPrefix
              (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4
                (N : ℝ) state.selectedPrefix)| ≤ M) ∧
          |historyNormalizedResidual N cap state.selectedPrefix
                (frozenLevel (e : ℝ) chi m omega (N : ℝ) state.selectedPrefix) -
              closedProfile N p (oldExponent (e : ℝ) chi m omega N p)| < eta ∧
          |historyNormalizedResidual N cap state.selectedPrefix
                (P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4
                  (N : ℝ) state.selectedPrefix) -
              closedProfile N p (newExponent e chi m omega J4 cap4 N p)| < eta := by
  obtain ⟨M, hM, N0, hN0, hbound⟩ :=
    exists_original_old_new_uniform_suppliers a rho ha e chi he m J4 cap4 eta heta
  refine ⟨M, hM, N0, hN0, ?_⟩
  intro N hN hEven omega hcheck cap weight state hstate hcut
  let p := primeHistoryTuple 4 state.selectedPrefix
  have hlen : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4 (policy (e : ℝ) chi m omega (N : ℝ))
      weight [] (roughPrimeUniverse N cap 0 ((N : ℝ) ^ rho)) true 1 (by simp) state hstate
  have hp : p ∈ admittedTuples (e : ℝ) chi m omega rho N cap :=
    frontier_tuple_mem_admitted (e : ℝ) chi m omega rho N cap weight state hstate
  have hcutTuple : (N : ℝ) ^ a ≤ (p 3 : ℝ) := by
    simpa only [p, primeHistoryTuple_last hlen] using hcut
  have h := hbound N hN hEven omega hcheck cap p hp hcutTuple
  have hhistory : fourthHistory p = state.selectedPrefix := fourthHistory_primeHistoryTuple hlen
  have hold : oldLevel (e : ℝ) chi m omega N p =
      frozenLevel (e : ℝ) chi m omega (N : ℝ) state.selectedPrefix := by
    rw [oldLevel_eq_frozenThird, hhistory]
  have hnew : newLevel e chi m omega J4 cap4 N p =
      P1OriginalCoarseContinuation.level4 e chi m omega J4 cap4
        (N : ℝ) state.selectedPrefix := by
    unfold newLevel
    rw [hhistory]
  rw [hold, hnew] at h
  simpa only [p, normalizedResidual_primeHistoryTuple N cap hlen] using h

end HistoricalThirdCoarse.P1OriginalUpperResidual

end
end ImbalancedChen
