import ImbalancedChen.P1OriginalFourthMovingPrimeIntervalBound

/-!
# Regrouping the original fourth source by its reciprocal-cutoff index

The two integer residual-floor labels in `sourceBins` must not be paid
separately by a common prime box. This finite regrouping retains every
original tuple once and permits one box payment per natural cutoff index.
Source-only/uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseContinuation
open P1OriginalFourthSmallPrimeStratification
open P1OriginalFourthSmallBinWeightedMass

namespace P1OriginalFourthReciprocalBinRegrouping

abbrev PrimeTuple := Fin 4 → ℕ

def reciprocalOwner (a : ℝ) (N : ℕ) (p : PrimeTuple) : ℕ :=
  ⌊a / actualPrimeTupleLog N p (Fin.last 3)⌋₊

def reciprocalBins (S : Finset PrimeTuple) (a : ℝ) (N : ℕ) : Finset ℕ :=
  S.image (reciprocalOwner a N)

def reciprocalBin (S : Finset PrimeTuple) (a : ℝ) (N r : ℕ) : Finset PrimeTuple :=
  S.filter fun p => reciprocalOwner a N p = r

theorem source_eq_biUnion_reciprocalBins (S : Finset PrimeTuple) (a : ℝ) (N : ℕ) :
    S = (reciprocalBins S a N).biUnion (reciprocalBin S a N) := by
  ext p
  constructor
  · intro hp
    exact Finset.mem_biUnion.mpr ⟨reciprocalOwner a N p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
  · intro hp
    obtain ⟨r, _hr, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hp).1

theorem reciprocalBins_disjoint (S : Finset PrimeTuple) (a : ℝ) (N : ℕ)
    (r s : ℕ) (hrs : r ≠ s) :
    Disjoint (reciprocalBin S a N r) (reciprocalBin S a N s) := by
  rw [Finset.disjoint_left]
  intro p hr hs
  exact hrs ((Finset.mem_filter.mp hr).2.symm.trans (Finset.mem_filter.mp hs).2)

theorem sum_source_eq_reciprocalBins (S : Finset PrimeTuple) (a : ℝ) (N : ℕ)
    (f : PrimeTuple → ℝ) :
    (∑ p ∈ S, f p) =
      ∑ r ∈ reciprocalBins S a N, ∑ p ∈ reciprocalBin S a N r, f p := by
  calc
    _ = ∑ p ∈ (reciprocalBins S a N).biUnion (reciprocalBin S a N), f p :=
      congrArg (fun T : Finset PrimeTuple => ∑ p ∈ T, f p)
        (source_eq_biUnion_reciprocalBins S a N)
    _ = _ := by
      apply Finset.sum_biUnion
      intro r _ s _ hrs
      exact reciprocalBins_disjoint S a N r s hrs

/-- Each coarse reciprocal bin has the same prime box as every one of its
fine `s_old,s_new` descendants, without multiplying by their count. -/
theorem reciprocalBin_subset_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (r : ℕ) :
    reciprocalBin (smallCellTuples e chi m omega a N cap j) a N r ⊆
      actualPrimeBoxTuples N (binLo omega a r) (binHi a r) := by
  intro p hp
  obtain ⟨hpS, howner⟩ := Finset.mem_filter.mp hp
  let k : Bin := (r, ⌊residualS old N p⌋, ⌊residualS new N p⌋)
  have hfine : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j)
      a old new N k := by
    apply Finset.mem_filter.mpr
    refine ⟨hpS, ?_⟩
    change (reciprocalOwner a N p, ⌊residualS old N p⌋,
      ⌊residualS new N p⌋) = k
    rw [howner]
  exact smallBin_subset_prime_box e chi m omega a old new ha J4 N cap hN j hj k hfine

/-- Occupied natural indices cannot grow faster than `a log N/log 3` on
the even-target original carrier. This is the finite range needed to sum
the moving Mertens error once per natural reciprocal bin. -/
theorem occupied_reciprocal_index_le_log3
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (j : FourthCell m) (r : ℕ) (p : PrimeTuple)
    (hp : p ∈ reciprocalBin (smallCellTuples e chi m omega a N cap j) a N r) :
    (r : ℝ) ≤ a * Real.log (N : ℝ) / Real.log 3 := by
  obtain ⟨hpS, howner⟩ := Finset.mem_filter.mp hp
  obtain ⟨had, _hsmall, _hcell⟩ := Finset.mem_filter.mp hpS
  have hd := (mem_firstExitAdmittedTuples_iff_of_decreasing 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ))) p).mp had
  have hq := hd.2.1 (Fin.last 3)
  have hprime := mem_roughPrimeUniverse_prime hq
  have h2N : 2 ∣ N := by
    obtain ⟨u, hu⟩ := hEven
    exact ⟨u, by omega⟩
  have hne : p (Fin.last 3) ≠ 2 := by
    intro heq
    exact mem_roughPrimeUniverse_not_dvd hq (heq ▸ h2N)
  have hthree : 3 ≤ p (Fin.last 3) := by
    have := hprime.two_le
    omega
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlogp : Real.log (3 : ℝ) ≤ Real.log (p (Fin.last 3) : ℝ) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hthree
  have htpos := (admitted_log_data e chi m omega N cap hN p had).2.2 (Fin.last 3)
  have htlow : Real.log (3 : ℝ) / Real.log (N : ℝ) ≤
      actualPrimeTupleLog N p (Fin.last 3) := by
    exact div_le_div_of_nonneg_right hlogp hlogN.le
  have hfloor : (r : ℝ) ≤ a / actualPrimeTupleLog N p (Fin.last 3) := by
    have h := Nat.floor_le (div_nonneg ha.le htpos.le)
    change (reciprocalOwner a N p : ℝ) ≤ _ at h
    rw [howner] at h
    exact h
  have hratio : a / actualPrimeTupleLog N p (Fin.last 3) ≤
      a / (Real.log (3 : ℝ) / Real.log (N : ℝ)) :=
    div_le_div_of_nonneg_left ha.le (div_pos hlog3 hlogN) htlow
  have heq : a / (Real.log (3 : ℝ) / Real.log (N : ℝ)) =
      a * Real.log (N : ℝ) / Real.log 3 := by
    field_simp [hlog3.ne', hlogN.ne']
  rw [heq] at hratio
  exact hfloor.trans hratio

/-- One finite target-deleted box payment per reciprocal index, with no
dependence on the number of occupied integer residual-floor labels. -/
theorem weightedReciprocalBin_le_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a old new : ℝ) (ha : 0 < a)
    (J4 : Finset (FourthCell m)) (N cap : ℕ) (hN : 1 < N)
    (j : FourthCell m) (hj : j ∈ selectedFourthCells e chi m omega J4)
    (r : ℕ) :
    (∑ p ∈ reciprocalBin (smallCellTuples e chi m omega a N cap j) a N r,
      (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3)) ≤
      (a / (r : ℝ)) *
        actualPrimeBoxMass N (binLo omega a r) (binHi a r) := by
  let S := reciprocalBin (smallCellTuples e chi m omega a N cap j) a N r
  let B := actualPrimeBoxTuples N (binLo omega a r) (binHi a r)
  have hsub : S ⊆ B := reciprocalBin_subset_prime_box e chi m omega a old new
    ha J4 N cap hN j hj r
  have hr : 0 ≤ a / (r : ℝ) := div_nonneg ha.le (Nat.cast_nonneg _)
  calc
    (∑ p ∈ S, (∏ i, 1 / ((p i : ℝ) - 1)) *
        actualPrimeTupleLog N p (Fin.last 3)) ≤
        ∑ p ∈ S, (∏ i, 1 / ((p i : ℝ) - 1)) * (a / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpS, howner⟩ := Finset.mem_filter.mp hp
      let k : Bin := (r, ⌊residualS old N p⌋, ⌊residualS new N p⌋)
      have hfine : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j)
          a old new N k := by
        apply Finset.mem_filter.mpr
        refine ⟨hpS, ?_⟩
        change (reciprocalOwner a N p, ⌊residualS old N p⌋,
          ⌊residualS new N p⌋) = k
        rw [howner]
      have hcuts := smallBin_cutoffs e chi m omega a old new ha N cap hN j k p hfine
      exact mul_le_mul_of_nonneg_left hcuts.2.2.1
        (actualPrimeBoxWeight_nonneg (hsub hp))
    _ ≤ ∑ p ∈ B, (∏ i, 1 / ((p i : ℝ) - 1)) * (a / (r : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (actualPrimeBoxWeight_nonneg hp) hr
    _ = (a / (r : ℝ)) * actualPrimeBoxMass N (binLo omega a r) (binHi a r) := by
      dsimp [B]
      simp only [actualPrimeBoxMass, Finset.sum_mul]
      ring

end P1OriginalFourthReciprocalBinRegrouping

end

end ImbalancedChen
