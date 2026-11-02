import ImbalancedChen.Part5OriginalU34SameQCountEntrance
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the TWO actual deterministic prime corrections in the signed U3/U4
seed error at its unchanged enhanced row Q. The primitive sharp AP sum
and the signed pi-minus-li mean remain visible. No enhanced distribution
estimate, adopted positive seed, H430 soundness or full h34 is an input.

The payment is uniform in the entire finite-reserve U3 band, including
the positive-measure max-two tail. Neither cell49 nor cell50 is discarded.
-/
namespace ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance

noncomputable section
open Set Finset Filter Topology Wu2008DoubleSieve
open Part5OriginalUpsilon5CausalDictionary (a)
open P2FrozenReceiverCountActions P2SameQSeedCoprimeMean
open P2ActualMarkedCountState (Query rootLevel)
open P5OriginalU5FrozenSource (receiver)
open P2SameQPhysicalRosserSeed (seedError)
open MathlibNt.SieveTheory.LinearSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open scoped Classical BigOperators

def rowDivisors (N p : ℕ) (r : ℝ → ℝ) : Finset ℕ :=
  (ordinarySievePrimeProduct (p * N) (rowCutoff N p r)).divisors

def rowWeight (side : Bool) (N p : ℕ) (r : ℝ → ℝ) (q : ℕ) : ℝ :=
  ordinaryRosserWeight side N p (rootLevel (rowTotalLevel N p r) p) (rowCutoff N p r) q

def rowActive (side : Bool) (N p : ℕ) (r : ℝ → ℝ) : Finset ℕ :=
  (rowDivisors N p r).filter (fun q => rowWeight side N p r q ≠ 0)

/-- The two corrections are positive before multiplication by the signed
coefficient. The modulus-prime loss is not silently omitted. -/
def primeCorrection (N m : ℕ) : ℝ :=
  chenPrimeDivisorCount N m / (Nat.totient m : ℝ) + chenCentrePrimeAPCount N N m

def rowCorrection (side : Bool) (N p : ℕ) (r : ℝ → ℝ) : ℝ :=
  ∑ q ∈ rowDivisors N p r, rowWeight side N p r q * primeCorrection N (p * q)

/-- The unestimated terms are the precise sharp primitive discrepancy and
the finite total-prime/li shift under the SAME signed coefficient. -/
def rowSharpError (side : Bool) (N p : ℕ) (r : ℝ → ℝ) : ℝ :=
  ∑ q ∈ rowDivisors N p r, rowWeight side N p r q *
    (finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (p * q) +
      (((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N) /
        (Nat.totient (p * q) : ℝ))

/-- Exact original-receiver recentering. In particular neither signed
correction is replaced by a positive coefficient or deleted on sight. -/
theorem rowError_eq_sharp_sub_correction (side : Bool) (N p : ℕ) (r : ℝ → ℝ) :
    rowError side N p r = rowSharpError side N p r - rowCorrection side N p r := by
  unfold rowError seedError
  rw [← frozenRemainder_eq_coprime_split,
    P5OriginalU5FrozenSource.frozenRemainder_eq_sharp_prime_error]
  unfold rowSharpError rowCorrection rowDivisors rowWeight rowCutoff primeCorrection
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro q _
  ring

theorem primeCorrection_nonneg (N m : ℕ) : 0 ≤ primeCorrection N m :=
  add_nonneg (div_nonneg (chenPrimeDivisorCount_nonneg N m) (Nat.cast_nonneg _))
    (chenCentrePrimeAPCount_nonneg N N m)

/-- No prime-distribution input is needed for either deterministic atom. -/
theorem primeCorrection_le_log {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N) :
    primeCorrection N m ≤ 2 * (Real.log (N : ℝ) / Real.log 2) := by
  let B : ℝ := Real.log (N : ℝ) / Real.log 2
  have hB : 0 ≤ B := div_nonneg (Real.log_natCast_nonneg N)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hphi : (1 : ℝ) ≤ Nat.totient m := by
    exact_mod_cast (show 1 ≤ Nat.totient m from Nat.totient_pos.mpr hm)
  have hphipos : (0 : ℝ) < Nat.totient m := by linarith
  have hdiv : chenPrimeDivisorCount N m / (Nat.totient m : ℝ) ≤ B := by
    apply (div_le_iff₀ hphipos).mpr
    exact (chenPrimeDivisorCount_le_log_center hm hmN).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hphi hB])
  have hcenter : chenCentrePrimeAPCount N N m ≤ B :=
    (chenCentrePrimeAPCount_le_divisorCount N N m).trans
      (chenPrimeDivisorCount_le_log N hN)
  dsimp [primeCorrection]
  change _ ≤ 2 * B
  linarith

/-- Nonzero initial coefficients have a strict rounded level. Positivity
comes from their actual divisor support, not an extra coefficient axiom. -/
theorem rowActive_subset_level (side : Bool) (N p : ℕ) (r : ℝ → ℝ) :
    rowActive side N p r ⊆ Icc 1 ⌊rowTotalLevel N p r / (p : ℝ)⌋₊ := by
  intro q hq
  obtain ⟨hqdiv, hqne⟩ := mem_filter.mp hq
  have hqpos : 0 < q := Nat.pos_of_mem_divisors hqdiv
  have hlevel : q < rootLevel (rowTotalLevel N p r) p := by
    cases side
    · exact lowerRosserWeight_lt_level hqne
    · exact upperRosserWeight_lt_level hqne
  simp only [rootLevel] at hlevel
  exact mem_Icc.mpr ⟨hqpos, by omega⟩

theorem rowActive_card_le {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hrhi : r (primeCoordinate N p) ≤ 1 / 2) (side : Bool) :
    ((rowActive side N p r).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hcard : (rowActive side N p r).card ≤ ⌊rowTotalLevel N p r / (p : ℝ)⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      card_le_card (rowActive_subset_level side N p r)
  have hR0 : 0 ≤ rowTotalLevel N p r / (p : ℝ) := by
    rw [row_residual_identity hN hp r]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    ((rowActive side N p r).card : ℝ) ≤ (⌊rowTotalLevel N p r / (p : ℝ)⌋₊ : ℝ) := by
      exact_mod_cast hcard
    _ ≤ rowTotalLevel N p r / (p : ℝ) := Nat.floor_le hR0
    _ = (N : ℝ) ^ r (primeCoordinate N p) := row_residual_identity hN hp r
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) hrhi

theorem rowCorrection_eq_active (side : Bool) (N p : ℕ) (r : ℝ → ℝ) :
    rowCorrection side N p r =
      ∑ q ∈ rowActive side N p r, rowWeight side N p r q * primeCorrection N (p * q) := by
  unfold rowCorrection
  symm
  apply sum_subset (filter_subset _ _)
  intro q hq hnot
  have hz : rowWeight side N p r q = 0 := by
    by_contra hne
    exact hnot (mem_filter.mpr ⟨hq, hne⟩)
  simp only [hz, zero_mul]

/-- The enhanced root stays below N even though it need not stay below
sqrt N. This pays corrections without asserting BV at the enhanced cap. -/
theorem rowCorrection_abs_le {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hrpos : 0 < r (primeCoordinate N p))
    (hrhi : r (primeCoordinate N p) ≤ 1 / 2)
    (hcap : primeCoordinate N p + r (primeCoordinate N p) ≤ 153 / 256)
    (side : Bool) :
    |rowCorrection side N p r| ≤
      2 * (Real.log (N : ℝ) / Real.log 2) * (N : ℝ) ^ (1 / 2 : ℝ) := by
  let B : ℝ := Real.log (N : ℝ) / Real.log 2
  have hB : 0 ≤ B := div_nonneg (Real.log_natCast_nonneg N)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hpoint : ∀ q ∈ rowActive side N p r,
      |rowWeight side N p r q * primeCorrection N (p * q)| ≤ 2 * B := by
    intro q hq
    obtain ⟨hqdiv, hqne⟩ := mem_filter.mp hq
    have hqpos : 0 < q := Nat.pos_of_mem_divisors hqdiv
    have hs := P2ActualMarkedCountState.root_coefficient_full_Q hp
      (row_residual_gt_one hN hp hrpos) hqne
    have hmN : p * q ≤ N := by exact_mod_cast hs.1.trans (row_level_cap hN hcap).2
    have hc := primeCorrection_le_log (by omega : 0 < N) (Nat.mul_pos hp hqpos) hmN
    rw [abs_mul, abs_of_nonneg (primeCorrection_nonneg N (p * q))]
    exact (mul_le_mul_of_nonneg_right
      (ordinaryRosserWeight_abs_le_one side N p (rootLevel (rowTotalLevel N p r) p)
        q (rowCutoff N p r)) (primeCorrection_nonneg N (p * q))).trans
      (by simpa only [one_mul] using hc)
  rw [rowCorrection_eq_active]
  calc
    _ ≤ ∑ q ∈ rowActive side N p r,
        |rowWeight side N p r q * primeCorrection N (p * q)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ rowActive side N p r, 2 * B := sum_le_sum hpoint
    _ = ((rowActive side N p r).card : ℝ) * (2 * B) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (2 * B) :=
      mul_le_mul_of_nonneg_right (rowActive_card_le hN hp hrhi side) (by positivity)
    _ = _ := by dsimp [B]; ring

theorem selector_card_le_third_power {N : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hU : U ≤ 1 / 3) :
    ((chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U)).card : ℝ) ≤
      (N : ℝ) ^ (1 / 3 : ℝ) := by
  have hsub : chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U) ⊆
      Icc 1 ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
    intro p hp
    have hpp := (mem_chenAdditivePrimeCarrier.mp (mem_filter.mp hp).1).2.1.pos
    have hpu : (p : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
      (mem_filter.mp hp).2.2.le.trans (Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ N by omega)) hU)
    exact mem_Icc.mpr ⟨hpp, Nat.le_floor hpu⟩
  have hc : (chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U)).card ≤
      ⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using card_le_card hsub
  exact (by exact_mod_cast hc :
    ((chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U)).card : ℝ) ≤
      (⌊(N : ℝ) ^ (1 / 3 : ℝ)⌋₊ : ℝ)).trans
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

/-- An actual one-prime band, with its separate multiplicity, pays the
absolute correction by a sublinear power. No cancellation is used. -/
theorem sum_rowCorrection_abs_le {N : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hU : U ≤ 1 / 3) (r : ℝ → ℝ)
    (hr : ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U),
      0 < r (primeCoordinate N p) ∧ r (primeCoordinate N p) ≤ 1 / 2 ∧
        primeCoordinate N p + r (primeCoordinate N p) ≤ 153 / 256)
    (side : Bool) :
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U),
      |rowCorrection side N p r|) ≤
      (2 / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log (N : ℝ) := by
  let B : ℝ := Real.log (N : ℝ) / Real.log 2
  have hB : 0 ≤ B := div_nonneg (Real.log_natCast_nonneg N)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  calc
    _ ≤ ∑ _p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U),
        2 * B * (N : ℝ) ^ (1 / 2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact rowCorrection_abs_le hN
        (mem_chenAdditivePrimeCarrier.mp (mem_filter.mp hp).1).2.1.pos
        (hr p hp).1 (hr p hp).2.1 (hr p hp).2.2 side
    _ = ((chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U)).card : ℝ) *
        (2 * B * (N : ℝ) ^ (1 / 2 : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (2 * B * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (selector_card_le_third_power hN hU) (by positivity)
    _ = _ := by
      rw [show (5 / 6 : ℝ) = 1 / 3 + 1 / 2 by norm_num,
        Real.rpow_add (by exact_mod_cast (show 0 < N by omega) : (0 : ℝ) < N)]
      dsimp [B]
      ring

def groupedRowError (side : Bool) (N : ℕ) (tau : ℝ) : ℝ :=
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
    rowError side N p (U3Residual tau)) +
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
    rowError side N p mainResidual

def groupedSharpError (side : Bool) (N : ℕ) (tau : ℝ) : ℝ :=
  (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
    rowSharpError side N p (U3Residual tau)) +
  ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
    rowSharpError side N p mainResidual

/-- A finite majorant on the complete U3+U4 bands. Their common initial
band is counted twice, exactly as in the original source. -/
theorem grouped_prime_corrections_abs_le {N : ℕ} (hN : 2 ≤ N) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (side : Bool) :
    |groupedRowError side N tau - groupedSharpError side N tau| ≤
      (4 / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log (N : ℝ) := by
  have h3 := sum_rowCorrection_abs_le hN (le_refl (1 / 3 : ℝ)) (U3Residual tau)
    (fun p hp => by
      have ht := primeCoordinate_mem hN hp
      have hr := U3Residual_bounds htau htauhi ⟨ht.1, ht.2.le⟩
      exact ⟨lt_of_lt_of_le (by norm_num) hr.1, hr.2, U3_level_exponent_cap htau⟩) side
  have h4 := sum_rowCorrection_abs_le hN (by norm_num : (59 / 250 : ℝ) ≤ 1 / 3)
    mainResidual (fun p hp => by
      have ht := primeCoordinate_mem hN hp
      have hr := U4_residual_bounds ht
      exact ⟨lt_of_lt_of_le (by norm_num) hr.1, hr.2, U4_level_exponent_cap _⟩) side
  have heq : groupedRowError side N tau - groupedSharpError side N tau =
      -((∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
          rowCorrection side N p (U3Residual tau)) +
        ∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
          rowCorrection side N p mainResidual) := by
    unfold groupedRowError groupedSharpError
    simp_rw [rowError_eq_sharp_sub_correction, sum_sub_distrib]
    ring
  rw [heq, abs_neg]
  have hsum := (abs_add
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (1 / 3 : ℝ)),
      rowCorrection side N p (U3Residual tau))
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ (59 / 250 : ℝ)),
      rowCorrection side N p mainResidual)).trans
    (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _))
  have htotal := hsum.trans (add_le_add h3 h4)
  calc
    _ ≤ (2 / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log (N : ℝ) +
        (2 / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log (N : ℝ) := htotal
    _ = (4 / Real.log 2) * (N : ℝ) ^ (5 / 6 : ℝ) * Real.log (N : ℝ) := by ring

/-- Arbitrary logarithmic accuracy is uniform before tau and the sign. -/
theorem eventually_grouped_prime_corrections_paid (A : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1 / 12 → ∀ side : Bool,
      |groupedRowError side N tau - groupedSharpError side N tau| ≤
        epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  filter_upwards [eventually_powerLog_le_logAccuracy (4 / Real.log 2) (5 / 6) 1 A
    (by norm_num) epsilon hepsilon, eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  intro tau htau htauhi side
  exact (grouped_prime_corrections_abs_le hN htau htauhi side).trans
    (by simpa only [pow_one] using hsmall)

/-- Actual manuscript normalization, using its proved singular-series
lower bound. There is no assumed normalization or prime-count estimate. -/
theorem eventually_grouped_prime_corrections_normalized
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1 / 12 → ∀ side : Bool,
      |groupedRowError side N tau - groupedSharpError side N tau| ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization
    (4 / Real.log 2) (5 / 6) 1 (by norm_num) epsilon hepsilon,
    eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  intro tau htau htauhi side
  exact (grouped_prime_corrections_abs_le hN htau htauhi side).trans
    (by simpa only [pow_one] using hsmall)

end
end ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance
