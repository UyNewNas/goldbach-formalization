import ImbalancedChen.P3U5FullSourcePartition
import ImbalancedChen.OrderedBad

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Internal arithmetic meaning of the three nonconstant U5 root branches.
A rising/falling sum root fixes the original product, hence the ordered
prime pair; a head root fixes the larger prime. This is not a prime-count
or mass estimate. In particular it supplies no uniform positive harmonic
mass to the nonconstant fibres and does not require such a claim for PP.
-/
namespace ImbalancedChen.P3U5AffineRootFibers
noncomputable section
open scoped Classical BigOperators
open P3U5RootAtlas P3U5FullSourcePartition
open P2GammaSelectedPhysicalTheta P2GammaRootFiberRelative
open P2OriginalU5SmallPartnerRootPayment
open P5OriginalU5CausalFinite (pairSupport coordinates)

private theorem coordinate_power {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) (i : Fin 2) :
    (N : ℝ)^(coordinates N t i) = (![t.1,t.2] : Fin 2 → ℕ) i := by
  have hpos : ∀ j : Fin 2,0 < (![t.1,t.2] : Fin 2 → ℕ) j := by
    intro j
    fin_cases j
    · exact (pair_primes ht).1.pos
    · exact (pair_primes ht).2.pos
  exact actualPrimeTupleLog_rpow (show 1 < N by omega) ![t.1,t.2] hpos i

theorem pair_product_coordinate_power {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) :
    ((t.1*t.2 : ℕ) : ℝ) = (N : ℝ)^(coordinates N t 0 + coordinates N t 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_add hNp,coordinate_power hN ht 0,coordinate_power hN ht 1]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_mul]

/-- Injectivity is used only in the EXPONENT, not for arbitrary products. -/
theorem same_root_same_lane_level {N : ℕ} (hN : 2 ≤ N) {t s : Pair}
    (ht : t ∈ pairSupport N) (hs : s ∈ pairSupport N) (l : Lane)
    (htl : actualLane N t = l) (hsl : actualLane N s = l)
    (hroot : rootQ N t = rootQ N s) :
    laneLevel l (coordinates N t 0) (coordinates N t 1) =
      laneLevel l (coordinates N s 0) (coordinates N s 1) := by
  rw [rootQ_eq_owned hN ht,rootQ_eq_owned hN hs,htl,hsl] at hroot
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact le_antisymm ((Real.rpow_le_rpow_left_iff hNr).mp hroot.le)
    ((Real.rpow_le_rpow_left_iff hNr).mp hroot.symm.le)

/-- In either product-sum branch a root fixes the ACTUAL old product. -/
theorem product_eq_of_same_sum_root {N : ℕ} (hN : 2 ≤ N) {t s : Pair}
    (ht : t ∈ pairSupport N) (hs : s ∈ pairSupport N) (l : Lane)
    (hl : l = Lane.rise ∨ l = Lane.fall)
    (htl : actualLane N t = l) (hsl : actualLane N s = l)
    (hroot : rootQ N t = rootQ N s) : t.1*t.2 = s.1*s.2 := by
  have he := same_root_same_lane_level hN ht hs l htl hsl hroot
  have hsum : coordinates N t 0 + coordinates N t 1 =
      coordinates N s 0 + coordinates N s 1 := by
    rcases hl with rfl | rfl
    · dsimp [laneLevel,VariableEnvelope.A] at he
      linarith
    · dsimp [laneLevel,VariableEnvelope.C] at he
      linarith
  have hp : ((t.1*t.2 : ℕ) : ℝ) = ((s.1*s.2 : ℕ) : ℝ) := by
    rw [pair_product_coordinate_power hN ht,pair_product_coordinate_power hN hs,hsum]
  exact_mod_cast hp

/-- Ordered prime-factor uniqueness is reused with all labels retained. -/
theorem pair_eq_of_same_sum_root {N : ℕ} (hN : 2 ≤ N) {t s : Pair}
    (ht : t ∈ pairSupport N) (hs : s ∈ pairSupport N) (l : Lane)
    (hl : l = Lane.rise ∨ l = Lane.fall)
    (htl : actualLane N t = l) (hsl : actualLane N s = l)
    (hroot : rootQ N t = rootQ N s) : t = s := by
  have htorder : t.1 < t.2 := (Finset.mem_filter.mp ht).2.2.1
  have hsorder : s.1 < s.2 := (Finset.mem_filter.mp hs).2.2.1
  have hp := ordered_prime_factors_unique
    (pair_primes ht).1 (pair_primes ht).2 (pair_primes hs).1 (pair_primes hs).2
    htorder.le hsorder.le (product_eq_of_same_sum_root hN ht hs l hl htl hsl hroot)
  exact Prod.ext hp.1 hp.2

def laneRootFiber (N : ℕ) (keep : Pair → Prop) (l : Lane) (Q : ℝ) : Finset Pair :=
  (laneSupport N keep l).filter (fun t => rootQ N t = Q)

/-- A fixed-Q fibre in either nonconstant sum branch has at most one
original ordered pair. Nothing here calls that fibre a positive-area box. -/
theorem sum_lane_rootFiber_card_le_one {N : ℕ} (hN : 2 ≤ N)
    (keep : Pair → Prop) (l : Lane) (hl : l = Lane.rise ∨ l = Lane.fall) (Q : ℝ) :
    (laneRootFiber N keep l Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro t ht s hs
  obtain ⟨htlane,htQ⟩ := Finset.mem_filter.mp ht
  obtain ⟨hslane,hsQ⟩ := Finset.mem_filter.mp hs
  have ht' := (mem_laneSupport N keep l t).mp htlane
  have hs' := (mem_laneSupport N keep l s).mp hslane
  exact pair_eq_of_same_sum_root hN ht'.1 hs'.1 l hl ht'.2.2 hs'.2.2
    (htQ.trans hsQ.symm)

/-- Both original primes keep their original lower endpoint. -/
theorem original_pair_product_floor {N : ℕ} (hN : 2 ≤ N) {t : Pair}
    (ht : t ∈ pairSupport N) :
    (N : ℝ)^(2*Part5OriginalUpsilon5CausalDictionary.a) ≤ ((t.1*t.2 : ℕ) : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (N : ℝ)^Part5OriginalUpsilon5CausalDictionary.a ≤ (t.1 : ℝ) :=
    (Finset.mem_filter.mp ht).2.1
  have hord : (t.1 : ℝ) ≤ t.2 := by
    exact_mod_cast (Finset.mem_filter.mp ht).2.2.1.le
  have hq := hp.trans hord
  rw [show 2*Part5OriginalUpsilon5CausalDictionary.a =
    Part5OriginalUpsilon5CausalDictionary.a+Part5OriginalUpsilon5CausalDictionary.a by ring,
    Real.rpow_add hNp,Nat.cast_mul]
  exact mul_le_mul hp hq (Real.rpow_nonneg hNp.le _) (Nat.cast_nonneg _)

/-- A finite SPARSE-fibre bound, not a PP counterexample. It explains why
an all-fibre logarithmic mass floor is not a suitable new task for this
absolute-PP interface. No mass lower bound or distribution input is used. -/
theorem sum_lane_reciprocalMass_le {N : ℕ} (hN : 2 ≤ N)
    (keep : Pair → Prop) (l : Lane) (hl : l = Lane.rise ∨ l = Lane.fall)
    (Q height : ℝ) (hh : 0 ≤ height) (sigma : Pair → ℝ)
    (hsigma : ∀ t ∈ laneRootFiber N keep l Q,sigma t ≤ height) :
    reciprocalMass (laneRootFiber N keep l Q) sigma ≤
      height/(N : ℝ)^(2*Part5OriginalUpsilon5CausalDictionary.a) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : 0 < (N : ℝ)^(2*Part5OriginalUpsilon5CausalDictionary.a) :=
    Real.rpow_pos_of_pos hNp _
  have hcard : ((laneRootFiber N keep l Q).card : ℝ) ≤ 1 := by
    exact_mod_cast sum_lane_rootFiber_card_le_one hN keep l hl Q
  calc
    _ ≤ ∑ _t ∈ laneRootFiber N keep l Q,
        height/(N : ℝ)^(2*Part5OriginalUpsilon5CausalDictionary.a) := by
      apply Finset.sum_le_sum
      intro t ht
      have hpair := laneSupport_subset N keep l (Finset.mem_filter.mp ht).1
      have hf := original_pair_product_floor hN hpair
      exact (div_le_div_of_nonneg_right (hsigma t ht) (Nat.cast_nonneg _)).trans
        (div_le_div_of_nonneg_left hh hpow hf)
    _ ≤ _ := by
      simpa only [Finset.sum_const,nsmul_eq_mul,one_mul] using
        mul_le_mul_of_nonneg_right hcard (div_nonneg hh hpow.le)

/-- The head branch fixes q, but need not fix the smaller prime p. -/
theorem larger_prime_eq_of_same_head_root {N : ℕ} (hN : 2 ≤ N) {t s : Pair}
    (ht : t ∈ pairSupport N) (hs : s ∈ pairSupport N)
    (htl : actualLane N t = Lane.head) (hsl : actualLane N s = Lane.head)
    (hroot : rootQ N t = rootQ N s) : t.2 = s.2 := by
  have he := same_root_same_lane_level hN ht hs Lane.head htl hsl hroot
  have hc : coordinates N t 1 = coordinates N s 1 := by
    dsimp [laneLevel,VariableEnvelope.A] at he
    linarith
  have hp := congrArg (fun z : ℝ => (N : ℝ)^z) hc
  rw [coordinate_power hN ht 1,coordinate_power hN hs 1] at hp
  exact_mod_cast hp

/-- Source reconstruction can also use the combined lane/root key.
It does not assert a logarithmic bound on the number of occurring roots. -/
theorem sum_lane_rootFibers {α : Type*} [AddCommMonoid α]
    (N : ℕ) (keep : Pair → Prop) (F : Pair → α) :
    (∑ l : Lane,∑ Q ∈ (laneSupport N keep l).image (rootQ N),
      ∑ t ∈ laneRootFiber N keep l Q,F t) = ∑ t ∈ kept N keep,F t := by
  calc
    _ = ∑ l : Lane,∑ t ∈ laneSupport N keep l,F t := by
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_fiberwise_of_maps_to
        (s := laneSupport N keep l) (t := (laneSupport N keep l).image (rootQ N))
        (g := rootQ N) (fun t ht => Finset.mem_image_of_mem _ ht) F
    _ = _ := sum_lanes N keep F

end
end ImbalancedChen.P3U5AffineRootFibers
