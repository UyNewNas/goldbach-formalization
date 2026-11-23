import ImbalancedChen.P1OriginalFourthSmallPrimeStratification
import ImbalancedChen.ActualPrimeBoxMass

/-!
# A prime-weighted small-last bin of the original coarse fourth source

This is a source-only, uncompiled finite domination.  The source is exactly
`HistoricalThirdCoarse.policy` through `smallCellTuples`; its fourth-prime
coordinate and the original outer exponent `19/96` are unchanged.  The
slightly open upper endpoint of the last-prime box pays for the closed upper
endpoint of `smallBin_cutoffs`.  No small-prime asymptotic is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseContinuation
open P1OriginalFourthSmallPrimeStratification

namespace P1OriginalFourthSmallBinWeightedMass

abbrev PrimeTuple := Fin 4 → ℕ

def binLo (omega a : ℝ) (k : ℕ) : Fin 4 → ℝ :=
  fun i => if i = Fin.last 3 then a / ((k : ℝ) + 1) else omega

def binHi (a : ℝ) (k : ℕ) : Fin 4 → ℝ :=
  fun i => if i = Fin.last 3 then
    a / (k : ℝ) + a / ((k : ℝ) * ((k : ℝ) + 1))
  else (19 / 96 : ℝ)

def weightedBinMass (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ)
    (N cap : ℕ) (j : FourthCell m) (k : Bin) : ℝ :=
  ∑ p ∈ sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k,
    (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3)

/-- The original finite bin embeds in a genuine target-deleted prime box.
The first three lower endpoints use the selected *active third* cell;
their upper endpoints retain the original `19/96` universe. -/
theorem smallBin_subset_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (k : Bin) :
    sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k ⊆
      actualPrimeBoxTuples N (binLo omega a k.1) (binHi a k.1) := by
  intro p hp
  have hcuts := smallBin_cutoffs e chi m omega a old new ha N cap hN j k p hp
  obtain ⟨hpS, _howner⟩ := Finset.mem_filter.mp hp
  obtain ⟨had, _hsmall, hcell⟩ := Finset.mem_filter.mp hpS
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp had
  have hrough : ∀ i, p i ∈ roughPrimeUniverse N cap 0
      ((N : ℝ) ^ (19 / 96 : ℝ)) := hd.2.1
  have hprime : ∀ i, Nat.Prime (p i) :=
    fun i => mem_roughPrimeUniverse_prime (hrough i)
  have hfirst := selected_first_three_ge_omega e chi m omega J4 j hj
    (actualPrimeTupleLog N p) hcell
    (admitted_log_data e chi m omega N cap hN p had).1
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hupper (i : Fin 4) :
      actualPrimeTupleLog N p i < (19 / 96 : ℝ) := by
    have h := mem_roughPrimeUniverse_upper (hrough i)
    rw [← actualPrimeTupleLog_rpow hN p (fun x => (hprime x).pos) i] at h
    exact (Real.rpow_lt_rpow_left_iff hn).mp h
  apply (mem_actualPrimeBoxTuples_log_iff hN (binLo omega a k.1) (binHi a k.1) p).mpr
  refine ⟨fun i => ⟨hprime i, mem_roughPrimeUniverse_not_dvd (hrough i)⟩,
    mem_logPrimeBox.mpr (fun i => ?_)⟩
  by_cases hilast : i = Fin.last 3
  · subst i
    constructor
    · simpa [binLo] using hcuts.2.1.le
    · have hkpos : (0 : ℝ) < k.1 := by exact_mod_cast (show 0 < k.1 by omega)
      have hextra : 0 < a / ((k.1 : ℝ) * ((k.1 : ℝ) + 1)) := by positivity
      change actualPrimeTupleLog N p (Fin.last 3) <
        a / (k.1 : ℝ) + a / ((k.1 : ℝ) * ((k.1 : ℝ) + 1))
      exact hcuts.2.2.1.trans_lt (lt_add_of_pos_right _ hextra)
  · have hne : i.val ≠ 3 := by
      intro h
      exact hilast (Fin.ext h)
    have hi3 : i.val < 3 := by have := i.isLt; omega
    let i3 : Fin 3 := ⟨i.val, hi3⟩
    have heq : (⟨i3.val, by omega⟩ : Fin 4) = i := Fin.ext rfl
    constructor
    · simpa [binLo, hilast, heq] using hfirst i3
    · simpa [binHi, hilast] using hupper i

/-- Uniform in the actual enumeration cap and target: a bin's weighted
fourth-prime first moment is paid by one full, target-deleted prime box.
Its first three factors remain on `[omega,19/96)`, rather than on an
artificially enlarged fourth source. -/
theorem weightedBinMass_le_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (k : Bin) :
    weightedBinMass e chi m omega a old new N cap j k ≤
      (a / (k.1 : ℝ)) *
        ∏ i, actualPrimeReciprocalMass N (binLo omega a k.1 i) (binHi a k.1 i) := by
  let S := sourceBin (smallCellTuples e chi m omega a N cap j) a old new N k
  let B := actualPrimeBoxTuples N (binLo omega a k.1) (binHi a k.1)
  have hsub : S ⊆ B := smallBin_subset_prime_box e chi m omega a old new ha J4
    N cap hN j hj k
  have hk : 0 ≤ a / (k.1 : ℝ) := div_nonneg ha.le (Nat.cast_nonneg _)
  calc
    weightedBinMass e chi m omega a old new N cap j k ≤
        ∑ p ∈ S, (∏ i, 1 / ((p i : ℝ) - 1)) * (a / (k.1 : ℝ)) := by
      unfold weightedBinMass
      apply Finset.sum_le_sum
      intro p hp
      have hcuts := smallBin_cutoffs e chi m omega a old new ha N cap hN j k p hp
      exact mul_le_mul_of_nonneg_left hcuts.2.2.1
        (actualPrimeBoxWeight_nonneg (hsub hp))
    _ ≤ ∑ p ∈ B, (∏ i, 1 / ((p i : ℝ) - 1)) * (a / (k.1 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (actualPrimeBoxWeight_nonneg hp) hk
    _ = (a / (k.1 : ℝ)) *
        ∏ i, actualPrimeReciprocalMass N (binLo omega a k.1 i) (binHi a k.1 i) := by
      dsimp [B]
      rw [← actualPrimeBoxMass_eq_prod]
      simp only [actualPrimeBoxMass, Finset.sum_mul]
      ring

end P1OriginalFourthSmallBinWeightedMass

end

end ImbalancedChen
