import ImbalancedChen.Part3ActualCompactInitialSupport
import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.UpperRosserCubeCarrier

/-!
# Actual compact rough-frontier support at every rank

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The finite-set Rosser filter at the i-th original decreasing prime is
exactly the first i+1 entries.  Its odd cardinality test therefore gives
the indexed cubic tests required by the pinned numerical admissibility
theorem.  This converts actual set support into full original D-well
support without an hSupport premise.

The final theorem applies to the literal rough-prime frontier of the
actual compact policy, at every rank >= 3 including even ranks.  It uses
the existing causal frontier-validity theorem to preserve the inherited
odd tests on an automatically retained even successor.  Same-rho tensor
reconstruction, attachment, and the signed spectral estimate are not proved.
-/

namespace ImbalancedChen.Part3.ActualCompactAllRankSupport

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
open MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility

/-- Strict decreasing order identifies the original Rosser filter with
the literal indexed prefix, retaining all occurrence positions. -/
theorem decreasing_filter_eq_take (input : List ℕ) (hsort : input.Pairwise (· > ·))
    (i : ℕ) (hi : i < input.length) :
    input.toFinset.filter (fun p => input[i] ≤ p) = (input.take (i + 1)).toFinset := by
  ext p
  simp only [Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hp, hge⟩
    obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.mp hp
    have hki : k ≤ i := by
      by_contra hn
      have hlt := (List.pairwise_iff_getElem.mp hsort) i k hi hk (by omega)
      rw [hkp] at hlt
      omega
    exact List.mem_take_iff_getElem.mpr ⟨k, by omega, hkp⟩
  · intro hp
    obtain ⟨k, hk, hkp⟩ := List.mem_take_iff_getElem.mp hp
    have hkl : k < input.length := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    have hki : k ≤ i := by omega
    refine ⟨List.mem_iff_getElem.mpr ⟨k, hkl, hkp⟩, ?_⟩
    by_cases heq : k = i
    · subst k
      exact le_of_eq hkp
    · rw [← hkp]
      exact ((List.pairwise_iff_getElem.mp hsort) k i hkl hi (by omega)).le

/-- The original set's odd-cardinality tests are exactly the indexed
upper cubes on a decreasing vector.  No total-product or square test is
inserted as an assumption. -/
theorem upper_set_indexed_cubes {D : ℝ} (input : List ℕ)
    (hsort : input.Pairwise (· > ·)) (hadm : UpperAdmissibleSet D input.toFinset) :
    CubicPrefixBound true (fun p : ℕ => (p : ℝ)) D input := by
  intro i hi hpar
  change i % 2 = 0 at hpar
  have hfilter := decreasing_filter_eq_take input hsort i hi
  have hnd : (input.take (i + 1)).Nodup :=
    hsort.nodup.sublist (List.take_sublist _ _)
  have hcard : (input.toFinset.filter (fun p => input[i] ≤ p)).card = i + 1 := by
    rw [hfilter, List.toFinset_card_of_nodup hnd, List.length_take,
      Nat.min_eq_left (by omega)]
  have hodd : ¬Even (input.toFinset.filter (fun p => input[i] ≤ p)).card := by
    rw [hcard, Nat.even_iff]
    omega
  have htest := hadm input[i] (List.mem_toFinset.mpr (List.getElem_mem hi)) hodd
  have hprod : (input.take (i + 1)).toFinset.prod id = (input.take (i + 1)).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  rw [hfilter, hprod, List.take_succ_eq_append_getElem hi] at htest
  simpa only [List.prod_append, List.prod_singleton, Nat.cast_mul,
    actualNatList_cast_prod, pow_succ, mul_assoc, mul_comm, mul_left_comm] using htest

/-- All four fields of the pinned numerical admissibility structure are
produced from primality, original order, and the original set tests. -/
theorem upper_set_numerical_admissible {D : ℝ} (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hsort : input.Pairwise (· > ·))
    (hadm : UpperAdmissibleSet D input.toFinset) :
    Admissible true (fun p : ℕ => (p : ℝ)) D input := by
  refine ⟨?_, ?_, ?_, upper_set_indexed_cubes input hsort hadm⟩
  · intro p hp
    exact_mod_cast (hprime p hp).one_lt.le
  · intro i j hi hj hij
    by_cases heq : i = j
    · subst j
      exact le_rfl
    · have hlt := (List.pairwise_iff_getElem.mp hsort) i j hi hj (by omega)
      exact_mod_cast hlt.le
  · intro hlen
    have hp := hprime input[0] (List.getElem_mem hlen)
    have hone : (1 : ℝ) ≤ input[0] := by exact_mod_cast hp.one_lt.le
    have hcube := upperAdmissibleSet_mem_cube_lt hadm
      (List.mem_toFinset.mpr (List.getElem_mem hlen))
    apply (Real.lt_sqrt (Nat.cast_nonneg input[0])).2
    exact (pow_le_pow_right₀ hone (by norm_num : 2 ≤ 3)).trans_lt hcube

theorem upper_set_dwell_support {D : ℝ} (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hsort : input.Pairwise (· > ·))
    (hadm : UpperAdmissibleSet D input.toFinset) :
    actualDwellSupport D input :=
  actualDwellSupport_of_admissible (upper_set_numerical_admissible input hprime hsort hadm)

/-- Every actual rough frontier, at odd or even rank, has original
full-square support at its actual compact cell level.  Sortedness,
primality, and inherited ordinary validity come from the real generator. -/
theorem actual_compact_frontier_all_rank_support
    (e h : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j) :
    actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      state.selectedPrefix.reverse := by
  have hprime : ∀ p ∈ roughPrimeUniverse N cap w z, Nat.Prime p :=
    fun p hp => mem_roughPrimeUniverse_prime hp
  have hsort : ((roughPrimeUniverse N cap w z).reverse ++ ([] : List ℕ)).Pairwise (· < ·) := by
    simpa only [List.append_nil, List.pairwise_reverse] using
      roughPrimeUniverse_pairwise_gt N cap w z
  have hv := mem_firstExitDepthFrontier_thirdCapped_valid
    (actualExtendedThirdCompactInitialPolicy e m N)
    (actualExtendedThirdCompactRawLevel e h m N) k weight []
    (roughPrimeUniverse N cap w z) true 1 (by simp) rfl hprime hsort state hstate
  have hlen : state.selectedPrefix.length = k :=
    firstExitDepthFrontier_selected_length k _ weight [] _ true 1 (by simp) state hstate
  have hadm := hv.1 (by omega)
  rw [actualExtendedThirdCompactRawLevel_on_cell hj ht] at hadm
  have hleaf := firstExitDepthFrontier_toLeaf_mem k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight []
    (roughPrimeUniverse N cap w z) true 1 state hstate
  have hsub : state.selectedPrefix.reverse <+ roughPrimeUniverse N cap w z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitRetainedLeaves_selected_reverse_sublist
        (actualExtendedThirdCompactUpperPolicy e h m N) weight []
        (roughPrimeUniverse N cap w z) true 1
        { selected := state.selectedPrefix, positive := state.positive, mass := state.mass } hleaf
  apply upper_set_dwell_support state.selectedPrefix.reverse
    (fun p hp => hprime p (hsub.subset hp))
    ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
  simpa only [List.toFinset_reverse] using hadm.2

/-- The same actual all-rank frontier support may now be used directly
by the complete-local endpoint allocator. The physical history is not
replaced by a guessed support list. -/
theorem actual_compact_frontier_upper_local
    (e h : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z x tau theta : ℝ)
    (weight : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (ht : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hN : 0 < N) (hx : 1 < x) (htau : 0 ≤ tau) (upper : ℕ → ℕ)
    (hsize : ∀ p ∈ state.selectedPrefix.reverse, (upper p : ℝ) ≤ x ^ tau * p)
    (hbudget : (Real.log (N : ℝ) / Real.log x) * actualExtendedThirdPhysicalLevel e m j +
      tau * (k + 1) ≤ theta) :
    actualDwellSupport (x ^ theta) (state.selectedPrefix.reverse.map upper) := by
  have hsupport := actual_compact_frontier_all_rank_support e h m N cap k hk w z weight
    state hstate hj ht
  have hlen : state.selectedPrefix.reverse.length ≤ k := by
    rw [List.length_reverse,
      firstExitDepthFrontier_selected_length k _ weight [] _ true 1 (by simp) state hstate]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply ActualCompactInitialSupport.physical_support_upper_local (R := k)
    (lam := actualExtendedThirdPhysicalLevel e m j) (theta := theta) hNr hx htau
    id upper state.selectedPrefix.reverse hlen hsize
  · simpa using hsupport
  · exact hbudget

end

end ImbalancedChen.Part3.ActualCompactAllRankSupport
