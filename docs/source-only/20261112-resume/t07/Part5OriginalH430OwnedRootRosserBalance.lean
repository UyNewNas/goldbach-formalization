import ImbalancedChen.Part5OriginalH430OwnedRootCounts
import ImbalancedChen.Part5OriginalH430RootRosserSurplus

/-! The original U3 and U4 families are sifted after fixing the labelled
prime p and the common physical level of its box. The surplus and the
least-prime shell are both on the favorable side of the upper estimate.
Each signed remainder is paid once per p and tag. -/
namespace ImbalancedChen.Part5OriginalH430OwnedRootRosserBalance
noncomputable section
open Finset Real Wu2008DoubleSieve
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode (residual)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2FrozenReceiverCountActions (markedPhi frozenCount)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2ActualMarkedCountState (root_level_geometry)
open P2SameQPhysicalRosserSeed (cutoff_log_coordinate)
open P2Selected430CausalOccurrenceExporter (iterate)
open P5OriginalU5FrozenSource (receiver)
open P5CanonicalUpperCancellation (upperA)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedOriginalRowFreeze
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430OwnedRootCounts Part5OriginalH430RootRosserSurplus
open Part5OriginalH430SameQCanonicalMains (model physical_main_sides)

private theorem queryAt_le_six {n m : ℕ} (c : RootKey n m) : queryAt c ≤ 6 := by
  unfold queryAt
  split
  · norm_num
  · apply (min_le_left _ _).trans
    cases h : c.2.1 with
    | none => exact le_rfl
    | some i =>
      change 1 + ((i.val : ℝ) + 1) / 50 ≤ 6
      have hi : (i.val : ℝ) < 200 := by exact_mod_cast i.isLt
      linarith

private theorem box_geometry {N n m p : ℕ} {k : Root} {τ : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) (hp : p ∈ rootFibre N n m k τ c) :
    let Q := cellQ N n c.1
    let s := queryAt c
    2 ≤ s ∧ s ≤ 6 ∧ 1 < Q / (p : ℝ) ∧
      (N : ℝ) ^ ((11 / 384 : ℝ) / 6) ≤ cutoff Q p s ∧
      cutoff Q p s ≤ (N : ℝ) ^ a ∧ p ≤ N := by
  let v := (frozenRoot n k τ (physicalPrime N p)).physical
  let o : Occurrence N := origin 430 (rootRequest N n k τ p)
  let Q := cellQ N n c.1
  have hb := (Finset.mem_filter.mp hp).1
  have hgeo := original_fibre_geometry hN hτ hτ' hn hp
  have hg := original_band_geometry hN hb
  have hr : (11 / 384 : ℝ) ≤ residual v := (frozenRoot_residual_bounds hτ hτ' hg hn).1
  have hr0 : 0 < residual v := lt_of_lt_of_le (by norm_num) hr
  have hv : (2 : ℝ) ≤ v.argument := le_max_left _ _
  have hs := hv.trans hgeo.2.1
  have hs6 := queryAt_le_six c
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have ho : o ∈ rootHistory N n k τ p := List.mem_cons_self
  have hpow (w : ℝ) : cutoff Q p w = (N : ℝ) ^ (residual v / w) := by
    change cutoff (cellQ N n c.1) p w = _
    rw [hgeo.1]
    simpa only [o, origin, rootRequest, parentProduct, List.prod_cons, List.prod_nil,
      mul_one, v] using history_cutoff_power hN hτ hτ' hn hb ho w
  have hdiv : Q / (p : ℝ) = (N : ℝ) ^ residual v := by
    simpa [cutoff] using hpow 1
  have hcar : p ∈ chenAdditivePrimeCarrier N := by
    cases k <;> exact (Finset.mem_filter.mp hb).1
  refine ⟨hs, hs6, (one_lt_rpow hNr hr0).trans_eq hdiv.symm, ?_, ?_,
    (mem_chenAdditivePrimeCarrier_iff_le.mp hcar).1⟩
  · rw [hpow]
    apply rpow_le_rpow_of_exponent_le hNr.le
    exact (div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 6)).trans
      (div_le_div_of_nonneg_left hr0.le (by linarith : 0 < queryAt c) hs6)
  · rw [hpow]
    apply rpow_le_rpow_of_exponent_le hNr.le
    exact (div_le_div_of_nonneg_left hr0.le (by linarith : 0 < v.argument)
      hgeo.2.1).trans ((frozen_cutoff_ratio hτ hτ' hg hn).le.trans (min_le_left _ _))

/-- The common box has the precise original 430 lookup, including both
closed-cell knots and exterior values. Its entire actual receiver count
and both favorable finite terms equal the signed ordinary model. -/
theorem original_box_balance {N n m : ℕ} (k : Root) (τ : ℝ) (c : RootKey n m)
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    let B := rootFibre N n m k τ c
    let Q := cellQ N n c.1
    let s := queryAt c
    ((∑ p ∈ B, ((originalReceiver N p).card : ℝ)) +
      ∑ p ∈ B, firstPrimeMass N Q s p) + (∑ p ∈ B, surplus N p Q (cutoff Q p s)) =
      ∑ p ∈ B, (model true N Q p (cutoff Q p s) + signedAP N p Q (cutoff Q p s)) := by
  dsimp only
  rw [← owned_root_marked_count_exact k τ c hN hτ hτ' hn, markedPhi, ← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  simpa only [id_eq, one_mul] using frozen_count_plus_surplus
    (N := N) (p := p) (cellQ N n c.1) (cutoff (cellQ N n c.1) p (queryAt c))
    (original_band_prime (Finset.mem_filter.mp hp).1).2

/-- Exact one-box difference from the manuscript's proposed upper table
bound. Its last term is the original query's actual 430 read, weighted
once per selected p by its physical Theta. -/
theorem original_closed_owner_difference {N n m : ℕ} (k : Root) (τ : ℝ) (c : RootKey n m)
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    let B := rootFibre N n m k τ c
    let Q := cellQ N n c.1
    let s := queryAt c
    (∑ p ∈ B, ((originalReceiver N p).card : ℝ)) -
        (upperA s - ownerFloor c) * Theta N Q B (fun _ => 1) =
      (∑ p ∈ B, (model true N Q p (cutoff Q p s) + signedAP N p Q (cutoff Q p s) -
        upperA s * thetaAtom N Q p - surplus N p Q (cutoff Q p s) - firstPrimeMass N Q s p)) +
      ∑ p ∈ B, thetaAtom N (rootQ N n k τ p) p *
        requestValue (iterate 430) (rootRequest N n k τ p) := by
  dsimp only
  rw [← owned_root_theta_floor_exact k τ c hN hτ hτ' hn]
  have h := original_box_balance k τ c hN hτ hτ' hn
  dsimp only at h
  simp only [sum_add_distrib] at h
  simp only [Theta_eq_sum_atoms, one_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  linear_combination h

/-- Every original surviving quotient has zero local upper-Rosser
surplus even after the actual level and common one-sided query are
frozen. The two tags retain their separate counts at the common
physical level on the original U4 overlap. -/
theorem original_quotient_zero_box_surplus {N n m p q : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (hp : p ∈ rootFibre N n m k τ c) (hq : q ∈ originalReceiver N p) :
    let Q := cellQ N n c.1
    ∃ ell ∈ (goldbachDivisible N p).filter (receiver N), (N-ell)/p = q ∧
      primeSurplus N p Q (cutoff Q p (queryAt c)) ell = 0 := by
  obtain ⟨hs, _, hR, _, hz, _⟩ := box_geometry hN hτ hτ' hn hp
  have hb := (Finset.mem_filter.mp hp).1
  have hp' := (original_band_prime hb).1
  have hlow : (N : ℝ)^a ≤ (p : ℝ) := by cases k <;> exact (Finset.mem_filter.mp hb).2.1
  apply true_quotient_zero_surplus (root_level_geometry hR (le_trans (by norm_num : (1:ℝ)≤2) hs)).1
  · intro r hr hdiv
    rw [(Nat.prime_dvd_prime_iff_eq hr hp').mp hdiv]
    exact hz.trans hlow
  · obtain ⟨hraw, hrough⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hraw, fun r hr hdiv => hz.trans (hrough r hr hdiv)⟩

def bandUpper (N n m : ℕ) (k : Root) (τ ε : ℝ) : ℝ :=
  ∑ c : RootKey n m, ∑ p ∈ rootFibre N n m k τ c,
    let Q := cellQ N n c.1
    let s := queryAt c
    let z := cutoff Q p s
    (upperA s + ε) * thetaAtom N Q p + signedAP N p Q z -
      surplus N p Q z - firstPrimeMass N Q s p

/-- A single threshold precedes both bands, all common levels and all
original queries. The signed error and both finite credits are retained
on each labelled p-fibre. The H430 improvement still requires their
aggregate comparison with the actual closed-cell table price. -/
theorem original_U34_at_signed_root_AP {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ (n m : ℕ) (τ : ℝ),
      0 ≤ τ → τ ≤ 1 / 12 → 1 / ((n : ℝ) + 1) ≤ 11 / 384 →
      currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        bandUpper N n m .U3 τ ε + bandUpper N n m .U4 τ ε := by
  obtain ⟨T, h4, hT⟩ := physical_main_sides (by norm_num : (0:ℝ) < (11/384:ℝ)/6) he
  refine ⟨T, h4, ?_⟩
  intro N hN hEven n m τ hτ hτ' hn
  have h2 : 2 ≤ N := by omega
  rw [original_U34_eq_owned_root_counts N n m τ h2 hτ hτ' hn]
  have hband (k : Root) : ownedRootCount N n m k τ ≤ bandUpper N n m k τ ε := by
    unfold ownedRootCount bandUpper
    apply sum_le_sum
    intro c _
    rw [markedPhi, ← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    let Q := cellQ N n c.1
    let s := queryAt c
    let z := cutoff Q p s
    have hb := (Finset.mem_filter.mp hp).1
    have hpp := original_band_prime hb
    obtain ⟨hs, hs6, hR, hz, _, hpN⟩ := box_geometry h2 hτ hτ' hn hp
    have hm := (hT N hN hEven Q z s p hpp.1.pos hpN hR hz
      (cutoff_log_coordinate hR (by linarith : 0 < s)) hs (by linarith : s ≤ 10)).1
    have heq := frozen_count_plus_surplus (N := N) (p := p) Q z hpp.2
    change 1 * (frozenCount N p (receiver N) z : ℝ) - firstPrimeMass N Q s p ≤
      (upperA s + ε) * thetaAtom N Q p + signedAP N p Q z -
        surplus N p Q z - firstPrimeMass N Q s p
    linarith only [heq, hm]
  exact add_le_add (hband .U3) (hband .U4)

end
end ImbalancedChen.Part5OriginalH430OwnedRootRosserBalance
