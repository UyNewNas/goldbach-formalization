import ImbalancedChen.Part5OriginalU34PrimeCorrectionPayment
import ImbalancedChen.Part5OriginalU34ClampIntegral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual U3+U4 upper COUNT consumer of the unchanged-row-Q arithmetic
recursion and the proved deterministic AP/mean correction payment.
The positive seed-only430 ANALYTIC action licence remains OPEN: the
signed sharp AP term, pi/li normalization, actual switched K costs,
and enhanced common-Q marked-family table interpretation are not assumed.
-/
namespace ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance

noncomputable section
open Set Finset Filter Topology
open Part5OriginalUpsilon5CausalDictionary (a)
open P2ActualMarkedCountState (Query)
open scoped Classical BigOperators

def groupedStateUpper (N : ℕ) (tau : ℝ) (bank : List Query) (rounds : ℕ) : ℝ :=
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
    (rowState N p (U3Residual tau) bank rounds).upper p (rowCutoff N p (U3Residual tau))) +
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
    (rowState N p mainResidual bank rounds).upper p (rowCutoff N p mainResidual)

def groupedSeedUpper (N : ℕ) (tau eta : ℝ) : ℝ :=
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
    rowSeed true N p (U3Residual tau) eta) +
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
    rowSeed true N p mainResidual eta

/-- A genuine count statement on the whole original U3/U4 bands. Its
remaining analytic errors are explicit, rather than packaged as h34,
H430 soundness, or an assumed enhanced source distribution theorem. -/
theorem eventually_originalU34_count_with_prime_corrections_paid
    {eta epsilon : ℝ} (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1 / 12 → ∀ bank : List Query, ∀ rounds : ℕ,
        currentChenUpsilon3 N + currentChenUpsilon4 N ≤ groupedStateUpper N tau bank rounds ∧
        groupedStateUpper N tau bank rounds ≤
          groupedSeedUpper N tau eta + groupedSharpError true N tau +
            epsilon * singularNormalization N := by
  obtain ⟨N0, hN0, hseed⟩ := row_seed_and_joint_count heta
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop (2 : ℕ),
    eventually_grouped_prime_corrections_normalized epsilon hepsilon]
    with N hN hN2 hpaid
  intro he tau htau htauhi bank rounds
  have h3 (p : ℕ)
      (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
    have ht := primeCoordinate_mem hN2 hp
    have hr := U3Residual_bounds htau htauhi ⟨ht.1, ht.2.le⟩
    exact hseed N hN he (1 / 3) p hp (U3Residual tau) hr.1 hr.2 bank rounds
  have h4 (p : ℕ)
      (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ))) := by
    have hr := U4_residual_bounds (primeCoordinate_mem hN2 hp)
    exact hseed N hN he (59 / 250) p hp mainResidual hr.1 hr.2 bank rounds
  constructor
  · have hsource := original_U34_le_sameQ_clamped_counts hN2 htau htauhi
    change currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p (rowCutoff N p (U3Residual tau))).card : ℝ)) +
      ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((chenSiftedQuotientPrimeSource N p (rowCutoff N p mainResidual)).card : ℝ) at hsource
    exact hsource.trans (add_le_add
      (sum_le_sum (fun p hp => (h3 p hp).2.2.1))
      (sum_le_sum (fun p hp => (h4 p hp).2.2.1)))
  · have h3last := sum_le_sum (fun p hp => (h3 p hp).2.2.2)
    have h4last := sum_le_sum (fun p hp => (h4 p hp).2.2.2)
    have hstate : groupedStateUpper N tau bank rounds ≤
        groupedSeedUpper N tau eta + groupedRowError true N tau := by
      unfold groupedStateUpper groupedSeedUpper groupedRowError
      simp only [sum_add_distrib] at h3last h4last
      linarith
    have herror := (le_abs_self
      (groupedRowError true N tau - groupedSharpError true N tau)).trans
      (hpaid tau htau htauhi true)
    linarith

/-- On the positive-mass clamp the arithmetic query is exactly two and
the ADOPTED lookup still takes BOTH adjacent closed cells. This identity
does not turn those integers into a proved count defect. -/
theorem clamp_query_retains_adjacent_cells {N p : ℕ}
    (ht : clampStart ≤ primeCoordinate N p) :
    rowCutoff N p (U3Residual 0) =
        (rowTotalLevel N p (U3Residual 0) / (p : ℝ)) ^ (1 / 2 : ℝ) ∧
    H430 (rootArgument (U3Residual 0) (primeCoordinate N p)) =
      min (floorValue H430Numerators 49) (floorValue H430Numerators 50) := by
  have hs := U3_rootArgument_eq_two_iff.mpr ht
  constructor
  · simp only [rowCutoff, P2EnhancedTwentyOneSameQWeighted.cutoff, hs]
  · rw [hs, H430_two_eq_adjacent_min]

end
end ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance
