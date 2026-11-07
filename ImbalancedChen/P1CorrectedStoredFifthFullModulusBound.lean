import ImbalancedChen.P1OriginalVariableFifthFullModulusBound
import ImbalancedChen.P1VariableFifthOriginalBaseQ3Bridge

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A finite rational upper check on the literal selected stored fifth caps
bounds the corrected ORIGINAL fifth policy. The exact variable-fourth
ancestor remains the outside/non-fifth fallback. All retained ranks,
including zero through four and empty d=1, then obey the original Theta
ceiling. h45 dominance is unnecessary for retained-leaf validity and is
not claimed. The actual stored table check remains OPEN until supplied.
-/

namespace ImbalancedChen.P1CorrectedStoredFifthFullModulusBound
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1VariableFifthOriginalBaseQ3Bridge

/-- Literal finite rational upper test on exactly the selected stored
owners. It is independent of N, prime histories and any analytic supplier. -/
def storedCapUpperCheck (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D)) (e : ℚ) : Bool :=
  @decide _ (Finset.decidableDforallFinset (s := D.cells5 ∩ J)
    (p := fun j _ => D.cap5 j ≤ (299 / 500 : ℚ) - 2 * e))

theorem storedCapUpperCheck_iff (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D)) (e : ℚ) :
    storedCapUpperCheck D J e = true ↔
      ∀ j ∈ D.cells5 ∩ J, D.cap5 j ≤ (299 / 500 : ℚ) - 2 * e := by
  simp only [storedCapUpperCheck, decide_eq_true_eq]

/-- Rational endpoint data supplies the real cap upper bounds. No
per-history desired level bound is an input. -/
theorem storedCapUpperCheck_sound (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D)) (e : ℚ)
    (hcheck : storedCapUpperCheck D J e = true) :
    ∀ j ∈ D.cells5 ∩ J, (D.cap5 j : ℝ) ≤ initial (e : ℝ) := by
  intro j hj
  have hq := (storedCapUpperCheck_iff D J e).mp hcheck j hj
  dsimp [initial, extendedDistributionCap]
  exact_mod_cast hq

/-- Half-open uniqueness makes the real lookup either the true fallback
or one selected cap. Its upper bound needs no fallback<=selected premise. -/
theorem fifthLookup_le_of_values_le (m : ℕ)
    (J : Finset (HistoricalThirdCoarse.P1OriginalFifthCells.FifthCell m))
    (caps : HistoricalThirdCoarse.P1OriginalFifthCells.FifthCell m → ℝ)
    (fallback upper : ℝ) (t : Fin 5 → ℝ)
    (hfall : fallback ≤ upper) (hcaps : ∀ j ∈ J, caps j ≤ upper) :
    HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup m J caps fallback t ≤ upper := by
  by_cases hex : ∃ j ∈ J, t ∈ logPrimeMeshCell 0 (19 / 96) m j
  · obtain ⟨j, hj, ht⟩ := hex
    rw [HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup_on_cell m J caps fallback t j hj ht]
    exact hcaps j hj
  · rw [HistoricalThirdCoarse.P1OriginalFifthCells.fifthLookup_outside m J caps fallback t
      (by intro j hj ht; exact hex ⟨j, hj, ht⟩)]
    exact hfall

/-- The corrected stored exponent uses its literal finite selected values
and the actual variable-fourth fallback, including inactive rawQ3. -/
theorem correctedStoredExponent5_le_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true) (pre : List ℕ) :
    correctedStoredExponent5 D J e chi omega N rows4 licensed4 pre ≤ initial (e : ℝ) := by
  have hfall := P1OriginalVariableFifthFullModulusBound.inherited4_le_initial
    e he chi D.m omega N rows4 licensed4 pre
  unfold correctedStoredExponent5
  split_ifs
  · exact fifthLookup_le_of_values_le D.m (D.cells5 ∩ J)
      (fun j => (D.cap5 j : ℝ)) _ _ _ hfall (storedCapUpperCheck_sound D J e hcheck)
  · exact hfall

theorem correctedStoredLevel5_le_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega N : ℝ) (hN : 1 ≤ N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true) (pre : List ℕ) :
    correctedStoredLevel5 D J e chi omega N rows4 licensed4 pre ≤ N ^ initial (e : ℝ) := by
  exact Real.rpow_le_rpow_of_exponent_le hN
    (correctedStoredExponent5_le_initial D J e he chi omega N rows4 licensed4 hcheck pre)

/-- Through rank four the level is the original frozen rawQ3. Later it is
the corrected stored level on the actual fifth ancestor. Both are bounded. -/
theorem corrected_currentLevel_le_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega N : ℝ) (hN : 1 ≤ N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true) (pre : List ℕ) :
    P1OriginalHistoricalRetainedModulusLevel.currentLevel (e : ℝ) chi D.m omega N
      (correctedStoredLevel5 D J e chi omega N rows4 licensed4) pre ≤ N ^ initial (e : ℝ) := by
  unfold P1OriginalHistoricalRetainedModulusLevel.currentLevel
  split_ifs
  · have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    exact P1ActualCoarseLevelCeiling.frozenLevel_le_initial
      (e : ℝ) chi heR D.m omega N hN pre
  · exact correctedStoredLevel5_le_initial D J e he chi omega N hN rows4 licensed4 hcheck _

/-- Generic original-fifth retained validity is sufficient. No h45
comparison, density difference, or rank>=5 assumption is required. -/
theorem corrected_retained_leaf_modulus_lt_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ initial (e : ℝ) := by
  have hv := P1OriginalHistoricalRetainedModulusLevel.actual_original_fifth_retained_leaf_prod_lt_current
    (e : ℝ) chi D.m omega N cap w z
    (correctedStoredLevel5 D J e chi omega (N : ℝ) rows4 licensed4)
    heupper hN weight leaf hleaf
  exact hv.trans_le (corrected_currentLevel_le_initial D J e he chi omega (N : ℝ)
    hN.le rows4 licensed4 hcheck leaf.selected)

/-- ALL selected products in the corrected original rough support, also
at ranks zero through four, satisfy the buffered Theta bound. -/
theorem corrected_retained_modulus_lt_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true)
    (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ firstExitRetainedModuli
      (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4)
      (roughPrimeUniverse N cap w z)) :
    (d : ℝ) < (N : ℝ) ^ initial (e : ℝ) := by
  obtain ⟨leaf, hleaf, hprod⟩ := (mem_firstExitRetainedModuli _ _ d).mp hd
  simpa only [hprod] using corrected_retained_leaf_modulus_lt_initial
    D J e he chi omega rows4 licensed4 hcheck N cap w z heupper hN (fun _ => 1) leaf hleaf

/-- This corrected tree retains the even sign on every history. -/
theorem corrected_even_retained (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) (pre : List ℕ) :
    correctedStoredPolicy5 D J e chi omega N rows4 licensed4 true pre = true := by
  apply fifthCappedUpperPolicy_even_retained
  intro history
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

/-- Only active physical coefficients need the small-factor support
bound; zero coefficients on the displayed carrier may lie above L. -/
theorem corrected_physical_nonzero_modulus_lt_smallLevel_mul_initial
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true)
    (N cap : ℕ) (w z L : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (q : ℕ)
    (hq : actualSmallRoughRho
      (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4 false)
      N cap w z L q ≠ 0) :
    (q : ℝ) < L * (N : ℝ) ^ initial (e : ℝ) := by
  obtain ⟨a, _ha, b, hb, hqprod, haL, _hbc⟩ := actualSmallRoughRho_ne_zero_factors
    (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4 false)
    N cap w z L hq
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4)
    (corrected_even_retained D J e chi omega (N : ℝ) rows4 licensed4) N cap w z] at hb
  have hbBound := corrected_retained_modulus_lt_initial D J e he chi omega rows4 licensed4
    hcheck N cap w z heupper hN b hb
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg a) haL
  rw [hqprod, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg b)).trans_lt
    (mul_lt_mul_of_pos_left hbBound hLpos)

/-- With the primitive small-level allocation, active corrected stored
physical coefficients have exponent 599/1000<1. -/
theorem corrected_physical_nonzero_modulus_lt_599
    (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hcheck : storedCapUpperCheck D J e = true)
    (N cap : ℕ) (w z L : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (hL : L ≤ (N : ℝ) ^ (2 * (e : ℝ) + 1 / 1000)) (q : ℕ)
    (hq : actualSmallRoughRho
      (correctedStoredPolicy5 D J e chi omega (N : ℝ) rows4 licensed4 false)
      N cap w z L q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hexp : (2 * (e : ℝ) + 1 / 1000) + initial (e : ℝ) = (599 / 1000 : ℝ) := by
    dsimp [initial, extendedDistributionCap]
    ring
  calc
    (q : ℝ) < L * (N : ℝ) ^ initial (e : ℝ) :=
      corrected_physical_nonzero_modulus_lt_smallLevel_mul_initial D J e he chi omega
        rows4 licensed4 hcheck N cap w z L heupper hN q hq
    _ ≤ (N : ℝ) ^ (2 * (e : ℝ) + 1 / 1000) * (N : ℝ) ^ initial (e : ℝ) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (zero_lt_one.trans hN).le _)
    _ = (N : ℝ) ^ (599 / 1000 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans hN), hexp]

/-- The all-skip leaf preserves d=1, independently of finite cap checks. -/
theorem corrected_one_mem (D : HistoricalPrefixCapData)
    (J : Finset (P1VariableFifthOriginalBaseQ3Bridge.Label5 D))
    (e : ℚ) (chi omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop) (carrier : List ℕ) :
    1 ∈ firstExitRetainedModuli
      (correctedStoredPolicy5 D J e chi omega N rows4 licensed4) carrier := by
  exact (mem_firstExitRetainedModuli _ _ _).mpr ⟨⟨[], true, 1⟩,
    firstExitRetainedLeaves_skipAll_mem _ _ [] carrier true 1, by simp⟩

end
end ImbalancedChen.P1CorrectedStoredFifthFullModulusBound