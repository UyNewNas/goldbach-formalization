import ImbalancedChen.Part5OriginalH430RequestedLevelRealization
import ImbalancedChen.Part5OriginalU34PhysicalCutoffSource

/-!
P5.6 / h34: manuscript-local ORIGINAL U3/U4 arithmetic row to
the FROZEN selected-request root's physical cutoff.

SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

This is an actual one-sided finite arithmetic-count comparison, NOT an
identity of the full U3/U4 count sources with the generated feedback
history. Frozen roots use a LOWER total Q than the original varying
source. The resulting smaller cutoff admits at least as many sifted
prime receivers; reversing this inequality would invalidate h34.

The retained physical max-two clamp and the source's real alpha are
used literally. No arbitrary count licence, root weight, selected
owner, base/seed term, PP same-rho estimate, or external proof is added.
-/

namespace ImbalancedChen.Part5OriginalH430RequestedOriginalRowFreeze

noncomputable section
open Set
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode (residual)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport

/-- The frozen level is lower: its residual is no larger than the
ORIGINAL source residual at the same prime coordinate. -/
theorem frozen_residual_le_original {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) :
    residual (frozenRoot n k tau t).physical ≤ sourceResidual k tau t := by
  have hb := (frozenLevel_bounds
    (root_total_bounds htau htauhi ht) n).1
  change frozenLevel n (t + sourceResidual k tau t) ≤
    t + sourceResidual k tau t at hb
  rw [frozenRoot_residual]
  linarith only [hb]

/-- The physical cutoff exponent is min(a,R/2), not just R/2.
This proof does NOT discard the max-two clamp. -/
theorem frozen_exponent_le_original {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) :
    min a (residual (frozenRoot n k tau t).physical / 2) ≤
      physicalExponent (sourceResidual k tau) t := by
  have hr := frozen_residual_le_original htau htauhi ht (n := n)
  change min a (residual (frozenRoot n k tau t).physical / 2) ≤
    min a (sourceResidual k tau t / 2)
  apply le_min
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (by linarith only [hr])

/-- The frozen root keeps its exact physical quotient and max-two query.
This equality is internal geometry, NOT a count/density assertion. -/
theorem frozen_cutoff_ratio {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    residual (frozenRoot n k tau t).physical /
      (frozenRoot n k tau t).physical.argument =
        min a (residual (frozenRoot n k tau t).physical / 2) := by
  have hR : 0 < frozenLevel n (sourceRoot k tau t).physical.total - t := by
    have hb := (frozenRoot_residual_bounds htau htauhi ht hn).1
    rw [frozenRoot_residual] at hb
    linarith only [hb]
  change (frozenLevel n (sourceRoot k tau t).physical.total - t) /
      max 2 ((frozenLevel n (sourceRoot k tau t).physical.total - t) / a) =
        min a ((frozenLevel n (sourceRoot k tau t).physical.total - t) / 2)
  simpa only [rootArgument, physicalExponent] using
    (residual_div_rootArgument
      (r := fun _ : ℝ => frozenLevel n (sourceRoot k tau t).physical.total - t)
      (t := 0) hR)

/-- Exact same-Q expression for the FROZEN root's own sieve cutoff.
Here rootQ is the root's actual LOWER frozen total; no substitution of
the varying original rowTotalLevel is made. -/
theorem frozen_root_sameQ_cutoff_power (N n p : ℕ)
    (k : Root) (tau : ℝ)
    (hN : 2 ≤ N) (hp : 0 < p)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hb : physicalPrime N p ∈ rootBand k)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    (rootQ N n k tau p / (p : ℝ)) ^
        (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument) =
      (N : ℝ) ^
        min a (residual (frozenRoot n k tau (physicalPrime N p)).physical / 2) := by
  let R := residual (frozenRoot n k tau (physicalPrime N p)).physical
  have hR : 0 < R := by
    have hb' := (frozenRoot_residual_bounds htau htauhi hb hn).1
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 384) hb'
  have htotal : primeCoordinate N p + R = rootLevel N n k tau p := by
    change primeCoordinate N p +
      residual (frozenRoot n k tau (physicalPrime N p)).physical = _
    rw [show primeCoordinate N p = physicalPrime N p from rfl,
      frozenRoot_residual]
    unfold rootLevel
    ring
  have hQ : rowTotalLevel N p (fun _ : ℝ => R) = rootQ N n k tau p := by
    unfold rowTotalLevel rootQ
    rw [htotal]
  have harg :
      rootArgument (fun _ : ℝ => R) (primeCoordinate N p) =
        (frozenRoot n k tau (physicalPrime N p)).physical.argument := by
    change max 2 (R / a) =
      max 2 ((frozenLevel n
        (sourceRoot k tau (physicalPrime N p)).physical.total -
          physicalPrime N p) / a)
    rw [show R = frozenLevel n
      (sourceRoot k tau (physicalPrime N p)).physical.total -
        physicalPrime N p from frozenRoot_residual n k tau (physicalPrime N p)]
  have hcut := row_sameQ_cutoff hN hp
    (r := fun _ : ℝ => R) (by simpa using hR)
  rw [hQ, harg] at hcut
  simpa only [physicalExponent] using hcut

/-- Monotonicity of the EXISTING sieve source in its strict cutoff.
Retain the original prime receiver, congruence and coprimality tests. -/
private theorem sifted_source_antitone (N p : ℕ) {z w : ℝ}
    (hzw : z ≤ w) :
    chenSiftedQuotientPrimeSource N p w ⊆
      chenSiftedQuotientPrimeSource N p z := by
  intro q hq
  obtain ⟨hq, hs⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr
    ⟨hq, fun ell hell hdiv => hzw.trans (hs ell hell hdiv)⟩

/-- The original U3/U4 arithmetic prime receiver count is bounded ABOVE
by the corresponding FROZEN-root sieve count. Both have the same N,p,
but the root Q is lowered. This only pays the root-cutoff direction:
feedback selection and original count weights are still separate. -/
theorem original_row_card_le_frozen_row_card
    (N n p : ℕ) (k : Root) (tau : ℝ)
    (hN : 2 ≤ N) (hp : 0 < p)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hb : physicalPrime N p ∈ rootBand k)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    ((chenSiftedQuotientPrimeSource N p
      ((rowTotalLevel N p (sourceResidual k tau) / (p : ℝ)) ^
        (1 / rootArgument (sourceResidual k tau)
          (primeCoordinate N p)))).card : ℝ) ≤
    ((chenSiftedQuotientPrimeSource N p
      ((rootQ N n k tau p / (p : ℝ)) ^
        (1 / (frozenRoot n k tau (physicalPrime N p)).physical.argument))).card : ℝ) := by
  have hr : 0 < sourceResidual k tau (primeCoordinate N p) := by
    have h := (sourceResidual_bounds htau htauhi hb).1
    simpa only [show primeCoordinate N p = physicalPrime N p from rfl] using
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 11 / 192) h)
  rw [row_sameQ_cutoff hN hp hr,
    frozen_root_sameQ_cutoff_power N n p k tau hN hp htau htauhi hb hn]
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have he : min a
      (residual (frozenRoot n k tau (physicalPrime N p)).physical / 2) ≤
        physicalExponent (sourceResidual k tau) (physicalPrime N p) :=
    frozen_exponent_le_original htau htauhi hb
  have hc : (N : ℝ) ^
      min a (residual (frozenRoot n k tau (physicalPrime N p)).physical / 2) ≤
        (N : ℝ) ^ physicalExponent (sourceResidual k tau)
          (primeCoordinate N p) := by
    exact Real.rpow_le_rpow_of_exponent_le hNr
      (by simpa only [show primeCoordinate N p = physicalPrime N p from rfl] using he)
  exact_mod_cast Finset.card_le_card (sifted_source_antitone N p hc)

/-- Actual original U3+U4 arithmetic counts, including their TWO
overlapping prime bands, are bounded by the corresponding frozen-root
physical cutoff counts. No deduplication of the bands is performed.
The right side is NOT identified with a generated feedback history. -/
theorem original_U34_le_frozen_root_cutoff_counts (N n : ℕ)
    (hN : 2 ≤ N) (tau : ℝ) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(1/3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((rootQ N n .U3 tau p / (p : ℝ)) ^
            (1 / (frozenRoot n .U3 tau (physicalPrime N p)).physical.argument))).card : ℝ)) +
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(59/250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p
          ((rootQ N n .U4 tau p / (p : ℝ)) ^
            (1 / (frozenRoot n .U4 tau (physicalPrime N p)).physical.argument))).card : ℝ) := by
  calc
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
        (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(1/3 : ℝ)),
          ((chenSiftedQuotientPrimeSource N p
            ((rowTotalLevel N p (U3Residual tau) / (p : ℝ)) ^
              (1 / rootArgument (U3Residual tau) (primeCoordinate N p)))).card : ℝ)) +
        ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ)^a) ((N : ℝ)^(59/250 : ℝ)),
          ((chenSiftedQuotientPrimeSource N p
            ((rowTotalLevel N p mainResidual / (p : ℝ)) ^
              (1 / rootArgument mainResidual (primeCoordinate N p)))).card : ℝ) :=
        original_U34_le_sameQ_clamped_counts hN htau htauhi
    _ ≤ _ := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro p hp
        have hc := primeCoordinate_mem hN hp
        have hb : physicalPrime N p ∈ rootBand .U3 :=
          ⟨hc.1, hc.2.le⟩
        have hprime : 0 < p :=
          (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
        simpa only [sourceResidual] using
          (original_row_card_le_frozen_row_card N n p .U3 tau hN hprime
            htau htauhi hb hn)
      · apply Finset.sum_le_sum
        intro p hp
        have hc := primeCoordinate_mem hN hp
        have hb : physicalPrime N p ∈ rootBand .U4 :=
          ⟨hc.1, hc.2.le⟩
        have hprime : 0 < p :=
          (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.pos
        simpa only [sourceResidual] using
          (original_row_card_le_frozen_row_card N n p .U4 tau hN hprime
            htau htauhi hb hn)

end
end ImbalancedChen.Part5OriginalH430RequestedOriginalRowFreeze
