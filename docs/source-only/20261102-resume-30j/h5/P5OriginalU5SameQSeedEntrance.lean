import ImbalancedChen.P5OriginalU5FrozenSource
import ImbalancedChen.P2SameQPhysicalRosserSeed
import ImbalancedChen.P2OriginalU5SmallPartnerRootPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual original L5/U5 root entrance into the existing immutable-old count
recursion.  Q=N^V is the real enhanced max-level root; the argument is
(V-log_N(p*q))/a and its physical cutoff is proved to be exactly N^a.
One threshold precedes every original ordered prime pair, bank and round.

These are signed-error-bearing ordinary seed inequalities at the enhanced
physical level.  The raw finite state is not identified with h248.  In
particular individual arithmetic enclosures do not give pointwise positive
table defects, nor do varying pair roots give a common analytic marked box.
-/
namespace ImbalancedChen.P5OriginalU5SameQSeedEntrance

noncomputable section
open Finset Wu2008DoubleSieve
open P5OriginalU5CausalFinite (pairSupport coordinates originalResidual)
open P5OriginalU5FrozenSource (receiver)
open P2OriginalU5SmallPartnerRootPayment (rootQ pair_product_pos
  root_residual_identity root_residual_gt_one root_level_cap)
open P2ActualMarkedCountState (Query rootLevel)
open P2FrozenReceiverCountActions
open P2SameQPhysicalRosserSeed
open P2SameQSeedCoprimeMean
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

def rootArgument (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  Part5OriginalUpsilon5CausalDictionary.argument (coordinates N t)

theorem root_cutoff_identity {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    P2EnhancedTwentyOneSameQWeighted.cutoff (rootQ N t) (t.1*t.2) (rootArgument N t) =
      P5OriginalU5CausalFinite.cutoff N := by
  unfold P2EnhancedTwentyOneSameQWeighted.cutoff
  rw [root_residual_identity (by omega) ht, ← Real.rpow_mul (Nat.cast_nonneg N)]
  apply congrArg (fun e : ℝ => (N : ℝ)^e)
  simpa only [originalResidual, rootArgument, div_eq_mul_inv, one_div, one_mul,
    Part5OriginalUpsilon5CausalDictionary.a] using
    Part5OriginalUpsilon5CausalDictionary.residual_div_argument
      (P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht)

/-- The residual power needed by the same-Q seed is supplied on the full
actual pair selector; it is not an extra source/class premise. -/
theorem root_residual_power_floor {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    (N : ℝ)^(34/125 : ℝ) ≤ rootQ N t / ((t.1*t.2 : ℕ) : ℝ) := by
  rw [root_residual_identity (by omega) ht]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega))
    (P5OriginalU5CausalFinite.original_geometry hN ht).1

/-- Every nonzero coefficient of the actual root Rosser seed has the
original full modulus cap and primitive target residue.  This is a seed
support theorem, not a W/history licence for the full enhanced coefficient. -/
theorem root_seed_coefficient_support {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) {side : Bool} {r : ℕ}
    (hr : ordinaryRosserWeight side N (t.1*t.2) (rootLevel (rootQ N t) (t.1*t.2))
      (P5OriginalU5CausalFinite.cutoff N) r ≠ 0) :
    (((t.1*t.2)*r : ℕ) : ℝ) ≤ (N : ℝ)^(153/256 : ℝ) ∧
      ((t.1*t.2)*r).Coprime N := by
  have hc := P2ActualMarkedCountState.root_coefficient_full_Q
    (pair_product_pos ht) (root_residual_gt_one hN ht) hr
  refine ⟨hc.1.trans (root_level_cap (by omega) t), ?_⟩
  have hdN := (chenY5PrimeSelector_sieve_data ht).2.1
  exact hdN.mul_left (hc.2.of_dvd_right (dvd_mul_left N (t.1*t.2)))

def rootSeed (side : Bool) (N : ℕ) (eta : ℝ) (t : ℕ × ℕ) : ℝ :=
  seedMain side N (t.1*t.2) (rootQ N t) (rootArgument N t) eta

def rootError (side : Bool) (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  seedError side N (t.1*t.2) (rootQ N t) (rootArgument N t) (receiver N)

def rootLower (N : ℕ) (bank : List Query) (rounds : ℕ) (t : ℕ × ℕ) : ℝ :=
  (rawIterate N (rootQ N t) (receiver N) bank rounds).lower (t.1*t.2)
    (P5OriginalU5CausalFinite.cutoff N)

def rootUpper (N : ℕ) (bank : List Query) (rounds : ℕ) (t : ℕ × ℕ) : ℝ :=
  (rawIterate N (rootQ N t) (receiver N) bank rounds).upper (t.1*t.2)
    (P5OriginalU5CausalFinite.cutoff N)

/-- The remaining seed error is literally the original prime AP error
and mean shift under the unchanged signed seed coefficient. -/
theorem rootError_eq_actual_signed_AP {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (side : Bool) :
    rootError side N t =
      ∑ r ∈ (ordinarySievePrimeProduct ((t.1*t.2)*N)
        (P5OriginalU5CausalFinite.cutoff N)).divisors,
        ordinaryRosserWeight side N (t.1*t.2) (rootLevel (rootQ N t) (t.1*t.2))
          (P5OriginalU5CausalFinite.cutoff N) r *
          (finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N ((t.1*t.2)*r) +
            (((chenAdditivePrimeCarrier N).card : ℝ) - logarithmicIntegral N -
              chenPrimeDivisorCount N ((t.1*t.2)*r)) / (Nat.totient ((t.1*t.2)*r) : ℝ)) := by
  unfold rootError seedError
  rw [← frozenRemainder_eq_coprime_split, root_cutoff_identity hN ht]
  exact P5OriginalU5FrozenSource.frozenRemainder_eq_actual_signed_AP side N (t.1*t.2)
    (rootLevel (rootQ N t) (t.1*t.2)) (P5OriginalU5CausalFinite.cutoff N)
    (chenY5PrimeSelector_sieve_data ht).2.1

/-- The root error reaches the existing sharp-prime-prefix discrepancy
interface with both prime corrections and the true-li shift intact. -/
theorem rootError_eq_sharp_prime_error {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) (side : Bool) :
    rootError side N t =
      ∑ r ∈ (ordinarySievePrimeProduct ((t.1*t.2)*N)
        (P5OriginalU5CausalFinite.cutoff N)).divisors,
        ordinaryRosserWeight side N (t.1*t.2) (rootLevel (rootQ N t) (t.1*t.2))
          (P5OriginalU5CausalFinite.cutoff N) r *
          (finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((t.1*t.2)*r) +
            (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N -
              chenPrimeDivisorCount N ((t.1*t.2)*r)) / (Nat.totient ((t.1*t.2)*r) : ℝ) -
            chenCentrePrimeAPCount N N ((t.1*t.2)*r)) := by
  unfold rootError seedError
  rw [← frozenRemainder_eq_coprime_split, root_cutoff_identity hN ht]
  exact P5OriginalU5FrozenSource.frozenRemainder_eq_sharp_prime_error side N (t.1*t.2)
    (rootLevel (rootQ N t) (t.1*t.2)) (P5OriginalU5CausalFinite.cutoff N)

/-- Actual seed, actual old-generation state, actual U5 fibre.  The fixed
threshold is chosen before every pair and every finite recursion choice. -/
theorem original_root_seed_entrance {eta : ℝ} (heta : 0 < eta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ t ∈ pairSupport N, ∀ bank : List Query, ∀ rounds : ℕ,
        rootSeed false N eta t + rootError false N t ≤ rootLower N bank rounds t ∧
        rootLower N bank rounds t ≤
          ((chenSiftedQuotientPrimeSource N (t.1*t.2)
            (P5OriginalU5CausalFinite.cutoff N)).card : ℝ) ∧
        ((chenSiftedQuotientPrimeSource N (t.1*t.2)
            (P5OriginalU5CausalFinite.cutoff N)).card : ℝ) ≤ rootUpper N bank rounds t ∧
        rootUpper N bank rounds t ≤ rootSeed true N eta t + rootError true N t := by
  obtain ⟨N0, hN0, hseed⟩ := sameQ_seed_attached_to_H
    (by norm_num : (0 : ℝ) < 34/125) heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN he t ht bank rounds
  have hN2 : 2 ≤ N := by omega
  have hs := (P5OriginalU5CausalFinite.original_geometry hN2 ht).2.2.2.1
  have hh := hseed N hN he (rootQ N t) (t.1*t.2) (rootArgument N t)
    (receiver N) bank rounds (pair_product_pos ht) (root_residual_power_floor hN2 ht)
    hs.1 (hs.2.trans (by norm_num))
  have hc := P5OriginalU5FrozenSource.frozenCount_eq_original_count N (t.1*t.2)
    (P5OriginalU5CausalFinite.cutoff N) (P5OriginalU5CausalFinite.row_multiplier_rough ht)
  have hcut := root_cutoff_identity hN2 ht
  simpa only [rootSeed, rootError, rootLower, rootUpper, hcut, hc] using hh

/-- Finite aggregation preserves the original ordered-pair multiplicity.
The signed arithmetic errors are retained, with no h5 conclusion premise. -/
theorem originalU5_seed_and_state_entrance {eta : ℝ} (heta : 0 < eta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ bank : List Query, ∀ rounds : ℕ,
        (∑ t ∈ pairSupport N, rootSeed false N eta t) +
            (∑ t ∈ pairSupport N, rootError false N t) ≤
          (∑ t ∈ pairSupport N, rootLower N bank rounds t) ∧
        (∑ t ∈ pairSupport N, rootLower N bank rounds t) ≤ currentChenUpsilon5 N ∧
        currentChenUpsilon5 N ≤ (∑ t ∈ pairSupport N, rootUpper N bank rounds t) ∧
        (∑ t ∈ pairSupport N, rootUpper N bank rounds t) ≤
          (∑ t ∈ pairSupport N, rootSeed true N eta t) +
            (∑ t ∈ pairSupport N, rootError true N t) := by
  obtain ⟨N0, hN0, hseed⟩ := original_root_seed_entrance heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN he bank rounds
  have hh := fun t ht => hseed N hN he t ht bank rounds
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sum_add_distrib]
    exact sum_le_sum (fun t ht => (hh t ht).1)
  · rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
    exact sum_le_sum (fun t ht => (hh t ht).2.1)
  · rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
    exact sum_le_sum (fun t ht => (hh t ht).2.2.1)
  · rw [← sum_add_distrib]
    exact sum_le_sum (fun t ht => (hh t ht).2.2.2)

end
end ImbalancedChen.P5OriginalU5SameQSeedEntrance
