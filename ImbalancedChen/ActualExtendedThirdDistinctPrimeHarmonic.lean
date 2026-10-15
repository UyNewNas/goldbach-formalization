import ImbalancedChen.ActualExtendedThirdCompactPrimeHarmonic

/-!
# The same cell harmonic limit on strictly ordered prime atoms

The literal prime harmonic tests kept ordering-wall atoms. The arithmetic
first-exit tuple dictionary instead needs distinct primes. We therefore
construct the strict ordered selector and prove its limit separately by
the actual pointwise affine sandwich. Only the continuous Lebesgue
integral uses null walls; no arithmetic wall is assumed empty or null.

Both tests converge to the same original cell integral. Their difference
therefore tends to zero, including all genuine repeated-prime wall atoms.
The positive cutoff, buffer and grid still precede the arithmetic target.
This does not identify the full signed first-exit coefficient or pay its
physical counting remainder.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open VariableEnvelope
open scoped Classical BigOperators

def actualExtendedThirdDistinctCellPrimeRegion (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Set (Fin 3 → ℝ) :=
  actualExtendedThirdCompactCellPrimeRegion m j ∩
    primeAffineGateRegion actualExtendedThirdCompactOrderForms (fun _ => 0)

theorem measurableSet_actualExtendedThirdDistinctCellPrimeRegion (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) :
    MeasurableSet (actualExtendedThirdDistinctCellPrimeRegion m j) :=
  (measurableSet_actualExtendedThirdCompactCellPrimeRegion m j).inter
    (measurableSet_primeAffineGateRegion actualExtendedThirdCompactOrderForms (fun _ => 0))

theorem actualExtendedThirdDistinctCellPrimeRegion_sandwich {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    primeAffineGateRegion actualExtendedThirdCompactCellForms
        (actualExtendedThirdCompactCellBounds m j) ⊆ actualExtendedThirdDistinctCellPrimeRegion m j ∧
      ∀ t ∈ actualExtendedThirdDistinctCellPrimeRegion m j, ∀ i,
        actualExtendedThirdCompactCellForms i t ≤ actualExtendedThirdCompactCellBounds m j i := by
  have hsand := actualExtendedThirdCompactCellPrimeRegion_sandwich hh hj
  constructor
  · intro t ht
    exact ⟨hsand.1 ht, ((mem_primeIcoBoxStrictGateRegion
      (actualExtendedThirdDyadicLo m j) (actualExtendedThirdDyadicHi m j)
      actualExtendedThirdCompactOrderForms (fun _ : Fin 2 => 0) t).mp ht).2⟩
  · intro t ht
    exact hsand.2 t ht.1

/-- Strict logarithmic order is the actual strict natural-prime order.
Primality and exclusion of the target's prime divisors stay in the carrier. -/
theorem actualExtendedThirdDistinctCellPrimeRegion_prime_order {N m : ℕ}
    (hN : 1 < N) {a b : Fin 3 → ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N a b) {j : ActualExtendedThirdDyadicLabel m}
    (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j) :
    p 1 < p 0 ∧ p 2 < p 1 := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpos (i : Fin 3) : 0 < p i := (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
  have hlt (i k : Fin 3) : actualPrimeTupleLog N p i < actualPrimeTupleLog N p k ↔ p i < p k := by
    rw [← Real.rpow_lt_rpow_left_iff hNr,
      actualPrimeTupleLog_rpow hN p hpos, actualPrimeTupleLog_rpow hN p hpos]
    exact Nat.cast_lt
  have h10 := ht.2 0
  have h21 := ht.2 1
  change actualPrimeTupleLog N p 1 - actualPrimeTupleLog N p 0 < 0 at h10
  change actualPrimeTupleLog N p 2 - actualPrimeTupleLog N p 1 < 0 at h21
  exact ⟨(hlt 1 0).mp (by linarith only [h10]),
    (hlt 2 1).mp (by linarith only [h21])⟩

/-- The original reciprocal-totient normalization is exact on these
distinct prime atoms, rather than a diagonal-sensitive approximation. -/
theorem actualExtendedThirdDistinctCellPrimeRegion_totient {N m : ℕ}
    (hN : 1 < N) {a b : Fin 3 → ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N a b) {j : ActualExtendedThirdDyadicLabel m}
    (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j) :
    (Nat.totient (∏ i : Fin 3, p i) : ℝ) =
      ((p 0 : ℝ) - 1) * ((p 1 : ℝ) - 1) * ((p 2 : ℝ) - 1) := by
  have hprime (i : Fin 3) : Nat.Prime (p i) := (mem_actualPrimeBoxTuples_iff.mp hp i).1
  obtain ⟨h10, h21⟩ := actualExtendedThirdDistinctCellPrimeRegion_prime_order hN hp ht
  have h01 := (Nat.coprime_primes (hprime 0) (hprime 1)).mpr h10.ne'
  have h02 := (Nat.coprime_primes (hprime 0) (hprime 2)).mpr (h21.trans h10).ne'
  have h12 := (Nat.coprime_primes (hprime 1) (hprime 2)).mpr h21.ne'
  rw [Fin.prod_univ_three, Nat.totient_mul (h02.mul_left h12), Nat.totient_mul h01,
    Nat.totient_prime (hprime 0), Nat.totient_prime (hprime 1), Nat.totient_prime (hprime 2),
    Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (hprime 0).one_lt.le,
    Nat.cast_sub (hprime 1).one_lt.le, Nat.cast_sub (hprime 2).one_lt.le, Nat.cast_one]

theorem actualExtendedThirdDistinctCellPrimeRegion_weight {N m : ℕ}
    (hN : 1 < N) {a b : Fin 3 → ℝ} {p : Fin 3 → ℕ}
    (hp : p ∈ actualPrimeBoxTuples N a b) {j : ActualExtendedThirdDyadicLabel m}
    (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdDistinctCellPrimeRegion m j) :
    (∏ i : Fin 3, 1 / ((p i : ℝ) - 1)) = 1 / (Nat.totient (∏ i : Fin 3, p i) : ℝ) := by
  rw [actualExtendedThirdDistinctCellPrimeRegion_totient hN hp ht, Fin.prod_univ_three]
  simp only [one_div, mul_inv_rev]
  ring

/-- The integral equality is paid by actual nonzero affine rows. It is not
an assertion about the mass of primes on either ordering wall. -/
theorem integral_actualExtendedThirdDistinctCellPrimeRegion {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) (g : (Fin 3 → ℝ) → ℝ) :
    (∫ t in logPrimeBox (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1) ∩
      actualExtendedThirdDistinctCellPrimeRegion m j, g t) =
      ∫ t in logPrimeBox (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1) ∩
        actualExtendedThirdCompactCellPrimeRegion m j, g t := by
  rw [← setIntegral_indicator (measurableSet_actualExtendedThirdDistinctCellPrimeRegion m j),
    ← setIntegral_indicator (measurableSet_actualExtendedThirdCompactCellPrimeRegion m j)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ae_primeAffineGate_no_wall
    actualExtendedThirdCompactCellForms (actualExtendedThirdCompactCellBounds m j)
    actualExtendedThirdCompactCellForms_ne_zero)] with t ht
  have hiff : t ∈ actualExtendedThirdDistinctCellPrimeRegion m j ↔
      t ∈ actualExtendedThirdCompactCellPrimeRegion m j := by
    constructor
    · exact fun hr => hr.1
    · intro hr
      have hg : t ∈ primeAffineGateRegion actualExtendedThirdCompactCellForms
          (actualExtendedThirdCompactCellBounds m j) :=
        fun i => lt_of_le_of_ne
          ((actualExtendedThirdCompactCellPrimeRegion_sandwich hh hj).2 t hr i) (ht i)
      exact ⟨hr, ((mem_primeIcoBoxStrictGateRegion
        (actualExtendedThirdDyadicLo m j) (actualExtendedThirdDyadicHi m j)
        actualExtendedThirdCompactOrderForms (fun _ : Fin 2 => 0) t).mp hg).2⟩
  by_cases hr : t ∈ actualExtendedThirdCompactCellPrimeRegion m j
  · simp only [indicator_of_mem hr, indicator_of_mem (hiff.mpr hr)]
  · simp only [indicator_of_notMem hr, indicator_of_notMem (mt hiff.mp hr)]

def actualExtendedThirdDistinctCellPrimeSum (N : ℕ) (e h : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 3 => h / 2) (fun _ => thirdPrefixRho + 1)
    ((actualExtendedThirdDistinctCellPrimeRegion m j).indicator
      (actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j)))

theorem tendsto_actualExtendedThirdDistinctCellPrimeSum {e h : ℝ} {m : ℕ}
    (hh : 0 < h) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m) :
    Tendsto (fun N : ℕ => actualExtendedThirdDistinctCellPrimeSum N e h m j) atTop
      (𝓝 (actualExtendedThirdRetainedCellIntegral e m j)) := by
  have hhrho : h ≤ thirdPrefixRho :=
    (Finset.mem_filter.mp hj).2.trans
      ((actualExtendedThirdDyadic_bounds m j 2).2.1.le.trans
        (actualExtendedThirdDyadic_bounds m j 2).2.2)
  have hab : h / 2 < thirdPrefixRho + 1 := by linarith
  let f := actualExtendedThirdCompactHarmonicProfile e h (actualExtendedThirdPhysicalLevel e m j)
  have hf := (continuous_actualExtendedThirdCompactHarmonicProfile hh e
    (actualExtendedThirdPhysicalLevel e m j)).continuousOn
  have hsand := actualExtendedThirdDistinctCellPrimeRegion_sandwich hh hj
  have hlim := tendsto_actualPrimeBoxTestSum_cube_affineSandwich (half_pos hh) hab
    actualExtendedThirdCompactCellForms (actualExtendedThirdCompactCellBounds m j)
    actualExtendedThirdCompactCellForms_ne_zero (actualExtendedThirdDistinctCellPrimeRegion m j)
    (measurableSet_actualExtendedThirdDistinctCellPrimeRegion m j) hsand.1 hsand.2 f hf
  have hold := actualExtendedThirdCompactCellPrimeRegion_sandwich hh hj
  have hfull := tendsto_actualPrimeBoxTestSum_cube_affineSandwich (half_pos hh) hab
    actualExtendedThirdCompactCellForms (actualExtendedThirdCompactCellBounds m j)
    actualExtendedThirdCompactCellForms_ne_zero (actualExtendedThirdCompactCellPrimeRegion m j)
    (measurableSet_actualExtendedThirdCompactCellPrimeRegion m j) hold.1 hold.2 f hf
  have heq := tendsto_nhds_unique hfull (tendsto_actualExtendedThirdCompactCellPrimeSum hh hj)
  have hint := integral_actualExtendedThirdDistinctCellPrimeRegion hh hj
    (fun t => f t * ∏ i : Fin 3, 1 / t i)
  simpa only [actualExtendedThirdDistinctCellPrimeSum, hint, heq] using hlim

def actualExtendedThirdDistinctCompactPrimeSum (N : ℕ) (e h : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ actualExtendedThirdCompactCells e h m, actualExtendedThirdDistinctCellPrimeSum N e h m j

theorem tendsto_actualExtendedThirdDistinctCompactPrimeSum {e h : ℝ}
    (hh : 0 < h) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    Tendsto (fun N : ℕ => actualExtendedThirdDistinctCompactPrimeSum N e h m) atTop
      (𝓝 (actualExtendedThirdCompactCellFunctional e h m)) := by
  rw [actualExtendedThirdCompactCellFunctional_eq_sum_cells he0 he m]
  exact tendsto_finsetSum _ (fun _j hj => tendsto_actualExtendedThirdDistinctCellPrimeSum hh hj)

/-- This difference includes the genuine arithmetic ordering-wall atoms;
its limit follows from two proved arithmetic limits, not from a null-wall
claim about the prime measure. -/
theorem tendsto_actualExtendedThirdCompactPrimeSum_sub_distinct {e h : ℝ}
    (hh : 0 < h) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    Tendsto (fun N : ℕ => actualExtendedThirdCompactPrimeSum N e h m -
      actualExtendedThirdDistinctCompactPrimeSum N e h m) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_actualExtendedThirdCompactPrimeSum hh he0 he m).sub
      (tendsto_actualExtendedThirdDistinctCompactPrimeSum hh he0 he m)

/-- Strictly ordered prime atoms recover the same full manuscript ideal,
with the cutoff and every policy parameter chosen before N. -/
theorem exists_actualExtendedThirdDistinctCompactPrimeSum_approx_ideal {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ, 0 < h ∧ ∃ e : ℝ, 0 < e ∧ e ≤ 1 / 384 ∧ ∃ m : ℕ,
      ∀ᶠ N : ℕ in atTop,
        |actualExtendedThirdDistinctCompactPrimeSum N e h m - actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨h, hh, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdCompactCellFunctional_uniform_approx (half_pos hε)
  have hepos : 0 < e₀ / 2 := half_pos he₀
  have hecap : e₀ / 2 ≤ 1 / 384 := (by linarith : e₀ / 2 ≤ e₀).trans he₀cap
  have hcont : |actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀ -
      actualExtendedThirdIdealFunctional| ≤ ε / 2 :=
    hb (e₀ / 2) hepos.le (by linarith) m₀ le_rfl
  have hprime : ∀ᶠ N : ℕ in atTop,
      |actualExtendedThirdDistinctCompactPrimeSum N (e₀ / 2) h m₀ -
        actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀| < ε / 2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (tendsto_actualExtendedThirdDistinctCompactPrimeSum hh hepos.le hecap m₀)
        (ε / 2) (half_pos hε)
  refine ⟨h, hh, e₀ / 2, hepos, hecap, m₀, ?_⟩
  filter_upwards [hprime] with N hN
  apply (abs_sub_le _ (actualExtendedThirdCompactCellFunctional (e₀ / 2) h m₀) _).trans
  exact (add_le_add hN.le hcont).trans (by linarith)

end

end ImbalancedChen
