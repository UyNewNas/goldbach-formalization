import ImbalancedChen.P2OriginalElevenCompactGatedPolicy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual retained-modulus difference localization for the concrete compact
gating of the common eleven-family supplier.  The first disagreement is
read on the real common first-exit tree.  Its actual six ancestor gives
an ORIGINAL omitted tuple whose product divides the full rough modulus.
This is precisely the divisor cover paid in F, not a NEW ALL16 wall.
-/
namespace ImbalancedChen.P2OriginalElevenActualDifferenceLocalization
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor P2OriginalElevenCompactGatedPolicy
open P2OriginalSixthSourceCompactCores P2OriginalSixthCompactArithmeticFibre
open P2OriginalSixthCommonScheduleAndFullQ

def PaidDivisorCover (n N b : ℕ) : Prop :=
  ∃ (c : Cell) (p : Fin 6 → ℕ), p ∈ omittedTuples c n N ∧ roughProduct p ∣ b

theorem actual_coefficient_difference_in_paid_cover
    (d : OriginalData) (n N cap : ℕ) (hN : 1 < N) (w z : ℝ) (b : ℕ)
    (hd : p1PolicyCoefficientDifference (policy8 d (N : ℝ)) (compactPolicy8 d n (N : ℝ))
      (roughPrimeUniverse N cap w z) b ≠ 0) : PaidDivisorCover n N b := by
  let carrier := roughPrimeUniverse N cap w z
  have hnodup := roughPrimeUniverse_nodup N cap w z
  have hprime : ∀ p ∈ carrier, p.Prime := fun p hp => mem_roughPrimeUniverse_prime hp
  have hsym := p1_policyCoefficientDifference_ne_zero_mem_symmDifference
    (policy8 d (N : ℝ)) (compactPolicy8 d n (N : ℝ)) carrier b hd
  have hsf : Squarefree b := by
    rcases Finset.mem_union.mp hsym with hnew | hold
    · exact firstExitRetainedModuli_squarefree (compactPolicy8 d n (N : ℝ)) carrier
        hnodup hprime (Finset.mem_sdiff.mp hnew).1
    · exact firstExitRetainedModuli_squarefree (policy8 d (N : ℝ)) carrier
        hnodup hprime (Finset.mem_sdiff.mp hold).1
  obtain ⟨state,hstate,hneq,hsub,hfactor⟩ := p1_coefficientDifference_ne_zero_firstDisagreement
    (policy8 d (N : ℝ)) (compactPolicy8 d n (N : ℝ)) (fun _ => 1) carrier hnodup hprime b hd
  have hbad : BadHistory d n (N : ℝ) state.selectedPrefix := by
    by_contra hgood
    exact hneq (policy8_eq_compact_off_bad_history d n (N : ℝ) state.positive state.selectedPrefix hgood)
  obtain ⟨c,hc,hout⟩ := hbad
  let pre := rosserAncestor 6 state.selectedPrefix
  let p : Fin 6 → ℕ := primeHistoryTuple 6 pre
  have hlen : pre.length = 6 := hc.1
  have hpreSub : pre <+ state.selectedPrefix := List.drop_sublist _ _
  have hmem (i : Fin 6) : p i ∈ state.selectedPrefix :=
    hpreSub.subset (primeHistoryTuple_mem hlen i)
  have hpcarrier (i : Fin 6) : p i ∈ carrier :=
    hsub.subset (List.mem_reverse.mpr (hmem i))
  have hpi (i : Fin 6) : (p i).Prime ∧ ¬p i ∣ N :=
    ⟨mem_roughPrimeUniverse_prime (hpcarrier i),mem_roughPrimeUniverse_not_dvd (hpcarrier i)⟩
  have hcoords : actualPrimeTupleLog N p = primeHistoryLogCoordinates (N : ℝ) 6 pre := rfl
  have hphys : PhysicalCell c (actualPrimeTupleLog N p) := by
    rw [hcoords]
    exact hc.2.1
  have hpraw : p ∈ actualPrimeBoxTuples N (fun _ : Fin 6 => (0 : ℝ)) (fun _ => (19/96 : ℝ)) := by
    apply (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
    refine ⟨hpi,mem_logPrimeBox.mpr (fun i => ⟨(hphys.coordinates_pos i).le,?_⟩)⟩
    have htop : actualPrimeTupleLog N p 0 < (19/96 : ℝ) := by
      have h := hphys.largest
      norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu] at h
      linarith
    fin_cases i <;> linarith [hphys.order.1,hphys.order.2.1,hphys.order.2.2.1,
      hphys.order.2.2.2.1,hphys.order.2.2.2.2]
  have hpold : p ∈ originalTuples c N := Finset.mem_filter.mpr ⟨hpraw,hphys⟩
  have hpomitted : p ∈ omittedTuples c n N := by
    apply Finset.mem_filter.mpr
    refine ⟨hpold,?_⟩
    simpa only [hcoords] using hout
  let F : Finset ℕ := Finset.univ.image p
  have hF : F ⊆ b.primeFactors := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hfactor _ (hmem i)
  have hprod : F.prod id = ∏ i, p i := by
    rw [Finset.prod_image]
    · rfl
    · intro i hi j hj heq
      exact original_tuple_injective c N hpold heq
  refine ⟨c,p,hpomitted,?_⟩
  rw [roughProduct_eq,← hprod,← Nat.prod_primeFactors_of_squarefree hsf]
  exact Finset.prod_dvd_prod_of_subset _ _ id hF

theorem actual_fixed_rough_eq_off_paid_cover
    (d : OriginalData) (n N cap : ℕ) (hN : 1 < N) (w z : ℝ) (b : ℕ)
    (hgood : ¬PaidDivisorCover n N b) :
    fixedRoughCoefficient ((compactPolicy8 d n (N : ℝ)) false) N cap w z b =
      fixedRoughCoefficient ((policy8 d (N : ℝ)) false) N cap w z b := by
  have hzero : p1PolicyCoefficientDifference (policy8 d (N : ℝ)) (compactPolicy8 d n (N : ℝ))
      (roughPrimeUniverse N cap w z) b = 0 := by
    by_contra hd
    exact hgood (actual_coefficient_difference_in_paid_cover d n N cap hN w z b hd)
  have heq := sub_eq_zero.mp hzero
  rw [UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
      (compactPolicy8 d n (N : ℝ)) (compactPolicy8_even d n (N : ℝ)) N cap w z b,
    UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
      (policy8 d (N : ℝ)) (policy8_even d (N : ℝ)) N cap w z b]
  exact_mod_cast heq

end
end ImbalancedChen.P2OriginalElevenActualDifferenceLocalization
