import ImbalancedChen.Part5OriginalH430ClassicalReceiverSubfamily

/-! The actual rejected unit-tail shell at a classical root.  It is
paid from the finite cube credit, with its Rosser surplus retained.
No estimate of the desired rejected total is a premise. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRejectedShell
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct)
open P2FrozenReceiverCountActions (frozenCount)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2ActualMarkedCountState (root_level_geometry)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430FrozenTableRootMass (frozenQuery)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RootRosserSurplus
open Part5OriginalH430ClassicalRootThetaPayment Part5OriginalH430ClassicalRootCredits
open Part5OriginalH430ClassicalRootPriceGeometry (actual_classical_queries)
open Part5OriginalH430ClassicalRootH430Boundary

/-- Lowering the terminal sieve cutoff enlarges the actual rejected
set. The original N^a prefix/residual tests are unchanged. -/
theorem rejected_antitone_cutoff (N B D : ℕ) {z w : ℝ} (hwz : w ≤ z) :
    rejectedChild N B D z ⊆ rejectedChild N B D w := by
  intro q hq
  obtain ⟨hz,hout⟩ := Finset.mem_sdiff.mp hq
  have hw : q ∈ chenSiftedQuotientPrimeSource N B w := by
    obtain ⟨hs,hr⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hs,fun r hp hd => hwz.trans (hr r hp hd)⟩
  refine Finset.mem_sdiff.mpr ⟨hw,?_⟩
  intro hin
  exact hout (Finset.mem_filter.mpr ⟨hz,(Finset.mem_filter.mp hin).2⟩)

theorem unit_inherited_eq_original (N p : ℕ) {z : ℝ} (hz : z ≤ (N:ℝ)^a) :
    inheritedChild N p 1 z = originalReceiver N p := by
  ext q
  constructor
  · intro hq
    obtain ⟨hs,_,hrough⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1,hrough⟩
  · intro hq
    obtain ⟨hs,hrough⟩ := Finset.mem_filter.mp hq
    have hone : ChenPrimeRough ((N:ℝ)^a) 1 := by
      intro r hr hd
      exact False.elim (hr.ne_one (Nat.dvd_one.mp hd))
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨hs,fun r hr hd => hz.trans (hrough r hr hd)⟩,hone,hrough⟩

theorem unit_frozen_split {N p : ℕ} {z : ℝ}
    (hp : ChenPrimeRough z p) (hz : z ≤ (N:ℝ)^a) :
    (frozenCount N p (receiver N) z : ℝ) =
      ((originalReceiver N p).card:ℝ) + ((rejectedChild N p 1 z).card:ℝ) := by
  have hsub : inheritedChild N p 1 z ⊆ chenSiftedQuotientPrimeSource N p z :=
    Finset.filter_subset _ _
  have hc : (chenSiftedQuotientPrimeSource N p z).card =
      (inheritedChild N p 1 z).card + (rejectedChild N p 1 z).card := by
    simpa only [rejectedChild,Nat.add_comm] using
      (Finset.card_sdiff_add_card_eq_card hsub).symm
  rw [unit_inherited_eq_original N p hz] at hc
  rw [frozenCount_eq_original_count N p z hp]
  exact_mod_cast hc

/-- Exact rejected-shell accounting at the real selected common root
query. The surplus is nonnegative and is not copied onto survivors. -/
theorem root_query_rejected_balance {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    ((rejectedChild N p 1 (cutoffAt N n m p τ)).card:ℝ) +
      surplus N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) = cubeCredit N n p τ := by
  have hg := classical_geometry (m := m) hN hτ hτ' hn hp
  have hb := (Finset.mem_filter.mp hp).1
  have hpr := original_band_prime hb
  have hr : ChenPrimeRough (cutoffAt N n m p τ) p := by
    intro r hr hd
    rw [(Nat.prime_dvd_prime_iff_eq hr hpr.1).mp hd]
    exact hg.2.1.trans (Finset.mem_filter.mp hb).2.1
  have hs := unit_frozen_split hr hg.2.1
  have hc := frozen_count_plus_surplus (rootQ N n .U3 τ p) (cutoffAt N n m p τ) hpr.2
  have hcredit := (original_classical_credit (m := m) hN hτ hτ' hn hp).2
  linarith only [hs,hc,hcredit]

/-- The named rejectedChild really is the existing least-prime shell,
not a new numerical reserve or an assumed root-count deficit. -/
theorem root_query_rejected_eq_firstPrimeMass {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    ((rejectedChild N p 1 (cutoffAt N n m p τ)).card:ℝ) =
      firstPrimeMass N (rootQ N n .U3 τ p) (queryAt (keyAt N n m .U3 τ p)) p := by
  have hr := root_query_rejected_balance hN hτ hτ' hn hp
  have hc := (original_classical_credit (m := m) hN hτ hτ' hn hp).1
  linarith only [hr,hc]

theorem root_query_rejected_le_cubeCredit {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    ((rejectedChild N p 1 (cutoffAt N n m p τ)).card:ℝ) ≤ cubeCredit N n p τ := by
  have hg := classical_geometry (m := m) hN hτ hτ' hn hp
  have hq := actual_classical_queries (m := m) hN hτ hτ' hn hp
  have hw : 1 ≤ queryAt (keyAt N n m .U3 τ p) := by linarith only [hq.1,hq.2.2.1]
  have hd := root_level_geometry hg.1 hw
  have hs : 0 ≤ surplus N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) :=
    surplus_nonneg hd.1 hd.2
  have he := root_query_rejected_balance hN hτ hτ' hn hp
  linarith only [hs,he]

/-- The common right query lowers the cutoff. The actual root keeps
its original physical argument; no query is reset along retention. -/
theorem common_cutoff_le_origin {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    cutoffAt N n m p τ ≤ memberCutoff (rootQ N n .U3 τ p)
      (origin (N := N) 430 (rootRequest N n .U3 τ p)) := by
  have hg := classical_geometry (m := m) hN hτ hτ' hn hp
  have hq := actual_classical_queries (m := m) hN hτ hτ' hn hp
  change cutoff (rootQ N n .U3 τ p) p (queryAt (keyAt N n m .U3 τ p)) ≤
    cutoff (rootQ N n .U3 τ p) p (frozenQuery n .U3 τ (physicalPrime N p))
  unfold cutoff
  exact Real.rpow_le_rpow_of_exponent_le hg.1.le
    (one_div_le_one_div_of_le (by linarith only [hq.1]) hq.2.2.1)

/-- Directed credit pool. Its generally main-order subtraction of the
ACTUAL original receiver count is retained in the conclusion. -/
theorem classical_cubeCredit_pool {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N, cubeCredit N n p τ) ≤
        (1+ε)*classicalMass N n τ -
          ∑ p ∈ classicalBand N, ((originalReceiver N p).card:ℝ) := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he] with N hd
  intro hEven n hn
  have hsum := Finset.sum_le_sum (s := classicalBand N)
    (fun p _ => le_abs_self (rootDifference N n p τ))
  simp only [rootDifference,Finset.sum_sub_distrib,Finset.sum_add_distrib] at hsum
  change _ + _ - classicalMass N n τ ≤ _ at hsum
  have herr := (hd hEven n hn).1
  linarith only [hsum,herr]

end
end ImbalancedChen.Part5OriginalH430ClassicalRejectedShell
