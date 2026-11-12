import ImbalancedChen.Part5OriginalH430OwnedRootRosserBalance
import ImbalancedChen.Part5OriginalH430PresieveOutsideFin
import ImbalancedChen.Part5OriginalH430ClassicalTailBV

/-! The actual original U3 classical tail at its selected 430 cell and
the common comparison query. Its nonzero residual coefficients pool by
the full modulus p*r below N^(1/2-τ), even after freezing and refinement. -/
namespace ImbalancedChen.Part5OriginalH430FrozenClassicalRootModuli
noncomputable section
open Finset Real Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct residualLevel)
open P2EnhancedLowerPrimeChildGeometry (parentWindow_logs)
open P2ActualMarkedCountState (root_coefficient_full_Q)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedAdmission
open Part5OriginalH430RequestedMember Part5OriginalH430CutoffCoherence
open Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430PresieveOutsideFin (presieve_below_frozen_root)
open Part5OriginalH430ClassicalTailBV (ordinaryProduct_dvd_common)

def classicalBand (N : ℕ) : Finset ℕ :=
  (originalBand N .U3).filter (fun p => tailCutoff ≤ physicalPrime N p)

def cutoffAt (N n m p : ℕ) (τ : ℝ) : ℝ :=
  cutoff (rootQ N n .U3 τ p) p (queryAt (keyAt N n m .U3 τ p))

def activeDivisors (N n m p : ℕ) (τ : ℝ) : Finset ℕ :=
  let z := cutoffAt N n m p τ
  let D := P2ActualMarkedCountState.rootLevel (rootQ N n .U3 τ p) p
  (ordinarySievePrimeProduct (p*N) z).divisors.filter
    (fun r => ordinaryRosserWeight true N p D z r ≠ 0)

/-- The p belongs to the original U3 band, and the true common right
query has a cutoff below its original specified-prime range. The level
cap follows by downward freezing on the classical branch itself. -/
theorem classical_geometry {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    1 < rootQ N n .U3 τ p / (p : ℝ) ∧ cutoffAt N n m p τ ≤ (N:ℝ)^a ∧
      rootQ N n .U3 τ p ≤ (N:ℝ)^(1/2-τ) := by
  obtain ⟨hb, ht⟩ := Finset.mem_filter.mp hp
  have hg := original_band_geometry hN hb
  have hpp := original_band_prime hb
  have hc : p ∈ rootFibre N n m .U3 τ (keyAt N n m .U3 τ p) :=
    Finset.mem_filter.mpr ⟨hb, rfl⟩
  have hgeo := original_fibre_geometry hN hτ hτ' hn hc
  have hw := coherent_window (root_coherent (by omega : 1<N) hτ hτ' hn hpp hg)
  have hR : 1 < rootQ N n .U3 τ p / (p:ℝ) := by
    simpa only [residualLevel, rootRequest, parentProduct, List.prod_cons,
      List.prod_nil, mul_one] using (parentWindow_logs hw).2.1
  have hs := frozenRoot_argument_bounds hτ hτ' hg (n := n) hn
  refine ⟨hR, ?_, ?_⟩
  · apply presieve_below_frozen_root hN hτ hτ' hn hb
    apply rpow_le_rpow_of_exponent_le hR.le
    exact one_div_le_one_div_of_le (zero_lt_one.trans_le hs.1) hgeo.2.1
  · apply rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    apply (frozenLevel_bounds (root_total_bounds hτ hτ' hg) n).1.trans
    change physicalPrime N p + U3Residual τ (physicalPrime N p) ≤ 1 / 2 - τ
    simp only [U3Residual, if_neg (not_lt.mpr ht), tailResidual]
    linarith

theorem pooled_support {N n m : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    (∀ p ∈ classicalBand N, activeDivisors N n m p τ ⊆
      (sieveProduct N (Nat.ceil ((N:ℝ)^a))).divisors) ∧
    (∀ p ∈ classicalBand N, ∀ r ∈ activeDivisors N n m p τ,
      p*r ≤ ⌊(N:ℝ)^(1/2-τ)⌋₊) := by
  have hP : sieveProduct N (Nat.ceil ((N : ℝ)^a)) ≠ 0 := by
    unfold sieveProduct
    exact Finset.prod_ne_zero_iff.mpr
      (fun ell hell => (mem_sievePrimes_chen_real_cap.mp hell).2.1.pos.ne')
  constructor
  · intro p hp r hr
    have h := classical_geometry (m := m) hN hτ hτ' hn hp
    have hd := (Finset.mem_filter.mp hr).1
    exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hd).1.trans
      (ordinaryProduct_dvd_common N p h.2.1), hP⟩
  · intro p hp r hr
    have h := classical_geometry (m := m) hN hτ hτ' hn hp
    have hpp := (original_band_prime (Finset.mem_filter.mp hp).1).1
    exact Nat.le_floor ((root_coefficient_full_Q hpp.pos h.1 (Finset.mem_filter.mp hr).2).1.trans h.2.2)

end
end ImbalancedChen.Part5OriginalH430FrozenClassicalRootModuli
