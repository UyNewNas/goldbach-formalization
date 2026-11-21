import ImbalancedChen.Part5OriginalH430ClassicalRootH430Boundary
import ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback

/-! Source-only candidate.  Actual classical U3 receipt counts, with the
original additive-prime mask and every original RootKey retained.  No
claim about the rejected-child complement or about fresh descendants. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalReceiverSubfamily
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedLowerPrimeChildCarriers (parentProduct physicalPrime)
open P2FrozenReceiverCountActions (frozenCount)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2ActualMarkedCountState (root_level_geometry)
open P5OriginalU5FrozenSource (receiver)
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RequestedHistory
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment
open Part5OriginalH430ClassicalRootCredits
open Part5OriginalH430ClassicalRootPriceGeometry (actual_classical_queries)
open Part5OriginalH430RootRosserSurplus (surplus surplus_nonneg frozen_count_plus_surplus)
open Part5OriginalH430ClassicalRootH430Boundary
open Part5OriginalH430OriginalReceiptMemberPullback

def classicalFibre (N n m : ℕ) (τ : ℝ) (c : RootKey n m) : Finset ℕ :=
  (classicalBand N).filter (fun p => keyAt N n m .U3 τ p = c)

theorem classicalFibre_subset_rootFibre {N n m : ℕ} {τ : ℝ} (c : RootKey n m) :
    classicalFibre N n m τ c ⊆ rootFibre N n m .U3 τ c := by
  intro p hp
  obtain ⟨hb,hc⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1,hc⟩

theorem sum_classicalFibre (N n m : ℕ) (τ : ℝ) (f : ℕ → ℝ) :
    (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c, f p) =
      ∑ p ∈ classicalBand N, f p := by
  exact Finset.sum_fiberwise_of_maps_to (s := classicalBand N) (t := Finset.univ)
    (g := keyAt N n m .U3 τ) (fun _ _ => Finset.mem_univ _) f

/-- The physical normalizer stays inside its actual root-key fibre. -/
def classicalOwnTheta (N n m : ℕ) (τ : ℝ) : ℝ :=
  ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
    thetaAtom N (cellQ N n c.1) p

theorem classicalOwnTheta_eq {N n m : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) :
    classicalOwnTheta N n m τ = classicalMass N n τ := by
  unfold classicalOwnTheta
  calc
    _ = ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        thetaAtom N (rootQ N n .U3 τ p) p := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(original_fibre_geometry hN hτ hτ' hn
        (classicalFibre_subset_rootFibre c hp)).1]
    _ = classicalMass N n τ := sum_classicalFibre N n m τ _

theorem classical_original_card_bound {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ p ∈ classicalBand N, ((originalReceiver N p).card : ℝ)) ≤
        (1+ε)*classicalMass N n τ := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n hn
  have hrow (p : ℕ) (hp : p ∈ classicalBand N) :
      ((originalReceiver N p).card : ℝ) ≤
        thetaAtom N (rootQ N n .U3 τ p) p + |rootDifference N n p τ| := by
    have hc := cubeCredit_nonneg hN hτ.le hτ' hn hp
    have ha := le_abs_self (rootDifference N n p τ)
    unfold rootDifference at ha
    linarith only [hc,ha]
  have hs := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib] at hs
  have he' := (hd hEven n hn).1
  change _ ≤ classicalMass N n τ + _ at hs
  linarith only [hs,he']

/-- A real emitted additive-prime count is bounded by the ORIGINAL root
receipt population.  Its physical cutoff and full old prefix remain in
the left side; the mask is essential. -/
theorem actual_masked_member_le_root {N n m p : ℕ} {τ : ℝ}
    {c : RootKey n m} {o : Occurrence N} (hN : 2 ≤ N)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12) (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p ∈ classicalFibre N n m τ c)
    (ho : o ∈ rootHistory N n .U3 τ p) :
    (frozenCount N (parentProduct o.current.old) (rootMask N p)
      (memberCutoff (cellQ N n c.1) o) : ℝ) ≤
        ((originalReceiver N p).card : ℝ) := by
  rw [owned_member_masked_count hN hτ hτ' hn
    (classicalFibre_subset_rootFibre c hp) ho]
  exact_mod_cast Finset.card_le_card
    (Finset.filter_subset (fun r => tailProduct o ∣ r ∧
      ChenPrimeRough (memberCutoff (cellQ N n c.1) o) (r/tailProduct o))
      (originalReceiver N p))

/-- The original request is an actual member of the emitted list.  This
pays its complete masked all-receiver count, with the threshold chosen
before both resolutions and with its own Q in every RootKey fibre. -/
theorem actual_classical_origins_paid {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        (frozenCount N (parentProduct
          (origin (N := N) 430 (rootRequest N n .U3 τ p)).current.old)
          (rootMask N p) (memberCutoff (cellQ N n c.1)
            (origin (N := N) 430 (rootRequest N n .U3 τ p))) : ℝ)) ≤
        (1+ε)*classicalOwnTheta N n m τ := by
  filter_upwards [classical_original_card_bound hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn]
  apply le_trans ?_ (hd hEven n hn)
  rw [← sum_classicalFibre N n m τ (fun p => ((originalReceiver N p).card : ℝ))]
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro p hp
  exact actual_masked_member_le_root hN hτ.le hτ' hn hp List.mem_cons_self

/-- The common-query root count is UNMASKED.  Its least-prime shell is
paid by the actual cube credit; no rejected quotient is dropped here. -/
theorem classical_unmasked_root_row {N n m p : ℕ} {τ : ℝ}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalBand N) :
    (frozenCount N p (receiver N) (cutoffAt N n m p τ) : ℝ) ≤
      thetaAtom N (rootQ N n .U3 τ p) p + |rootDifference N n p τ| := by
  have hg := classical_geometry (m := m) hN hτ hτ' hn hp
  have hq := actual_classical_queries (m := m) hN hτ hτ' hn hp
  have hw : 1 ≤ queryAt (keyAt N n m .U3 τ p) := by
    linarith only [hq.1,hq.2.2.1]
  have hd := root_level_geometry hg.1 hw
  have hs : 0 ≤ surplus N p (rootQ N n .U3 τ p) (cutoffAt N n m p τ) :=
    surplus_nonneg hd.1 hd.2
  have hc := frozen_count_plus_surplus (rootQ N n .U3 τ p)
    (cutoffAt N n m p τ) (original_band_prime (Finset.mem_filter.mp hp).1).2
  have hi := (original_classical_credit (m := m) hN hτ hτ' hn hp).2
  have ha := le_abs_self (rootDifference N n p τ)
  unfold rootDifference at ha
  linarith only [hs,hc,hi,ha]

/-- Complete real receiver count at every original selected classical
root query.  The sum uses all RootKeys and each key's own Q; there is no
assumed per-fibre relative error and no query-mesh multiplicity factor. -/
theorem actual_classical_unmasked_roots_paid {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        (frozenCount N p (receiver N) (cutoff (cellQ N n c.1) p (queryAt c)) : ℝ)) ≤
          (1+ε)*classicalOwnTheta N n m τ := by
  filter_upwards [actual_classical_and_clamp_distance hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  have hrows : (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
      (frozenCount N p (receiver N) (cutoff (cellQ N n c.1) p (queryAt c)) : ℝ)) ≤
      ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        (thetaAtom N (rootQ N n .U3 τ p) p + |rootDifference N n p τ|) := by
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro p hp
    have hQ := (original_fibre_geometry hN hτ.le hτ' hn
      (classicalFibre_subset_rootFibre c hp)).1
    obtain ⟨hb,hkey⟩ := Finset.mem_filter.mp hp
    rw [hQ,← hkey]
    exact classical_unmasked_root_row hN hτ.le hτ' hn hb
  rw [sum_classicalFibre,Finset.sum_add_distrib] at hrows
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn]
  change _ ≤ classicalMass N n τ + _ at hrows
  have herr := (hd hEven n hn).1
  linarith only [hrows,herr]

end
end ImbalancedChen.Part5OriginalH430ClassicalReceiverSubfamily
