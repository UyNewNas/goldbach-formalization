import ImbalancedChen.Part5OriginalH430ActualRootStageReceipts
import ImbalancedChen.FirstExitCandidateGeometry

/-!
P5.6 / h34: actual stage-zero first-exit mass versus ORIGINAL U3/U4
quotient receipt multiplicity. This is a source-only, uncompiled consumer.

The historical first selection has mass 1/(p-1), negative sign and
the genuine strict p-suffix. A single historical candidate is NOT one
independent weighted occurrence for every original quotient q.
The positive surplus in a nontrivial q fibre is an UNPAID ledger term;
it is not a constructed full/selected/inherited owner or a count bound.
-/ 

namespace ImbalancedChen.Part5OriginalH430StageZeroMassFibreGap

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ActualRootStageReceipts

/-- The historical first-selected prime weight, as opposed to the
generated request history root mark (which is exactly one). -/
def historicalFirstRootMass (p : ℕ) : ℝ :=
  1 / ((p : ℝ) - 1)

/-- Literal enumerator mass and sign at an ACTUAL stage-zero candidate.
The proof inspects the original enumerator rather than assuming any
count-to-history interface. -/
theorem stage_zero_candidate_mass_sign
    (N cap p : ℕ) (z0 : ℝ) (c : FirstExitDepthState ℕ)
    (hc : c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : c.selectedPrefix = [p]) :
    c.positive = false ∧ c.mass = historicalFirstRootMass p := by
  obtain ⟨before, q, after, hlist, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] (roughPrimeUniverse N cap 0 z0) true 1 c).mp hc
  rw [hstate] at hp
  have hqp : q = p := (List.cons.inj hp).1
  subst q
  rw [hstate]
  simp [historicalFirstRootMass]

/-- The same candidate's remaining list is the REAL descending
prime carrier strictly below the selected p, not an arbitrary tail.
No cap >= N hypothesis is inserted. -/
theorem stage_zero_candidate_exact_suffix
    (N cap p : ℕ) (z0 : ℝ) (c : FirstExitDepthState ℕ)
    (hc : c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hp : c.selectedPrefix = [p]) :
    c.remaining = roughPrimeUniverse N cap 0 (p : ℝ) := by
  obtain ⟨before, q, after, hlist, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] (roughPrimeUniverse N cap 0 z0) true 1 c).mp hc
  rw [hstate] at hp
  have hqp : q = p := (List.cons.inj hp).1
  subst q
  have hmember : p ∈ roughPrimeUniverse N cap 0 z0 := by
    rw [hlist]
    simp
  have hafter : after = roughPrimeUniverse N cap 0 (p : ℝ) := by
    calc
      after = (roughPrimeUniverse N cap 0 z0).filter
          (fun r => r < p) := by
        rw [hlist]
        exact decreasingList_suffix_eq_filter_lt before after p
          (hlist ▸ roughPrimeUniverse_pairwise_gt N cap 0 z0)
      _ = _ := roughPrimeUniverse_filter_lt_eq N cap 0 z0 p
        (mem_roughPrimeUniverse_upper hmember).le
  rw [hstate]
  exact hafter

/-- The actual tag/p-dependent physical Q and Boolean root policy
are retained as witnesses, while the historical mass and suffix are
read from the REAL rank-one enumerator. -/
theorem original_stage_root_exact_geometry
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) (p : ℕ)
    (hroot : originalStageRoot N cap precision tau z0 lower k p) :
    ∃ c : FirstExitDepthState ℕ,
      c ∈ firstExitNextSelectionCandidates
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      c.selectedPrefix = [p] ∧
      ordinaryRosserRetainedPolicy lower (rootQ N precision k tau p)
        c.positive c.selectedPrefix = true ∧
      c.positive = false ∧
      c.mass = historicalFirstRootMass p ∧
      c.remaining = roughPrimeUniverse N cap 0 (p : ℝ) := by
  obtain ⟨c, hc, hp, hpolicy⟩ := hroot
  obtain ⟨hsign, hmass⟩ :=
    stage_zero_candidate_mass_sign N cap p z0 c hc hp
  have hrem := stage_zero_candidate_exact_suffix N cap p z0 c hc hp
  exact ⟨c, hc, hp, hpolicy, hsign, hmass, hrem⟩

/-- The exact ORIGINAL q-receipt mass if each q is erroneously charged
with its shared first-root historical mark. This is NOT a valid owner
payment; its cardinal factor is explicit. -/
theorem original_quotient_fibre_root_mass (N p : ℕ) :
    (∑ q ∈ originalReceiver N p, historicalFirstRootMass p) =
      ((originalReceiver N p).card : ℝ) * historicalFirstRootMass p := by
  simp [Finset.sum_const, nsmul_eq_mul]

/-- All stage-zero admitted original U3/U4 receivers, still separated
by tag and by every original q, have this EXACT receipt-weighted total.
The first-exit candidate is not replicated by the reindexing. -/
theorem stage_original_receipt_root_mass_total
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      historicalFirstRootMass (arithmeticPrime z)) =
    (∑ p ∈ originalStageBand N cap precision tau z0 lower .U3,
      ((originalReceiver N p).card : ℝ) * historicalFirstRootMass p) +
    (∑ p ∈ originalStageBand N cap precision tau z0 lower .U4,
      ((originalReceiver N p).card : ℝ) * historicalFirstRootMass p) := by
  rw [selected_stage_signed_original_fibres N cap precision tau z0 lower
    (fun z => historicalFirstRootMass (arithmeticPrime z))]
  simp only [arithmeticPrime]
  simp_rw [original_quotient_fibre_root_mass]

/-- The real discrepancy between counting EVERY original q at its
historical p-weight and counting ONE first-stage mass per tagged root.
It remains visible, even across overlapping U3/U4 root bands. -/
theorem stage_original_root_mass_gap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      historicalFirstRootMass (arithmeticPrime z)) =
    ((∑ p ∈ originalStageBand N cap precision tau z0 lower .U3,
      historicalFirstRootMass p) +
     (∑ p ∈ originalStageBand N cap precision tau z0 lower .U4,
      historicalFirstRootMass p)) +
    ((∑ p ∈ originalStageBand N cap precision tau z0 lower .U3,
      (((originalReceiver N p).card : ℝ) - 1) * historicalFirstRootMass p) +
     (∑ p ∈ originalStageBand N cap precision tau z0 lower .U4,
      (((originalReceiver N p).card : ℝ) - 1) * historicalFirstRootMass p)) := by
  rw [stage_original_receipt_root_mass_total]
  have hband (k : Root) :
      (∑ p ∈ originalStageBand N cap precision tau z0 lower k,
        ((originalReceiver N p).card : ℝ) * historicalFirstRootMass p) =
      (∑ p ∈ originalStageBand N cap precision tau z0 lower k,
        historicalFirstRootMass p) +
      (∑ p ∈ originalStageBand N cap precision tau z0 lower k,
        (((originalReceiver N p).card : ℝ) - 1) * historicalFirstRootMass p) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hband .U3, hband .U4]
  ring

/-- Any actual original admitted root is prime; its genuine historical
first-stage mass is strictly positive. -/
theorem actual_admitted_root_mass_pos
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) {p : ℕ}
    (hp : p ∈ originalStageBand N cap precision tau z0 lower k) :
    0 < historicalFirstRootMass p := by
  have hband : p ∈ originalBand N k := (Finset.mem_filter.mp hp).1
  have hprime := (original_band_prime hband).1
  have hlarge : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hprime.one_lt
  unfold historicalFirstRootMass
  exact one_div_pos.mpr (by linarith)

/-- A genuine admitted root with at least two original quotient q values
has a STRICTLY POSITIVE unpaid surplus relative to one first-root mass.
This is a conditional obstruction, not an assertion that such a root exists
for the pinned N or that some other later owner cannot cover it. -/
theorem two_quotients_force_positive_root_surplus
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k : Root) {p : ℕ}
    (hp : p ∈ originalStageBand N cap precision tau z0 lower k)
    (hq : 2 ≤ (originalReceiver N p).card) :
    0 < (((originalReceiver N p).card : ℝ) - 1) *
      historicalFirstRootMass p := by
  have hcount : (1 : ℝ) < ((originalReceiver N p).card : ℝ) := by
    exact_mod_cast (show 1 < (originalReceiver N p).card by omega)
  exact mul_pos (by linarith)
    (actual_admitted_root_mass_pos N cap precision tau z0 lower k hp)

end
end ImbalancedChen.Part5OriginalH430StageZeroMassFibreGap
