import ImbalancedChen.P2LowerCapPlanIntegerRetention
import ImbalancedChen.P2LowerFiniteCellRawDensityReserve
import ImbalancedChen.CurrentChenOriginalLowerFiniteP5

/-!
# The actual rounded causal lower coefficient on the original prime source

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The raw-policy source theorem does not identify its coefficient with the
finite-cell compiler output: positive and negative label fibres have been
rounded differently, and the resulting support need not be a retained tree.
This file keeps that distinction.  It proves the original-prime source
inequality directly for the compiler's actual `rho`, retains its exact signed
coprime discrepancy, pays both prime corrections, and then consumes the
already constructed full-policy density reserve with its explicit rounding
loss.  The final specialization uses the actual incoming-cap integer trace.

No selected CapPlan licence, small rounding-loss estimate, sharp original-prime
PP theorem, D12 lower bound, or final transfer theorem is assumed or asserted.
-/

namespace ImbalancedChen.P2CompiledCausalPrimeSourceLower

noncomputable section
open scoped Classical BigOperators
open Filter
open P2LowerFiniteCellRounding P2LowerFiniteCellBetaCompiler

private theorem list_prod_coprime (xs : List ℕ) (N : ℕ)
    (h : ∀ p ∈ xs, p.Coprime N) : xs.prod.Coprime N := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      exact (h p List.mem_cons_self).mul_left
        (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

/-- Even the enlarged common rough carrier is primitive to the target.
This does not require identifying it with the smaller raw retained support. -/
theorem universe_coprime_target (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z) : d.Coprime N := by
  have hprod : (roughProduct N cap w z).Coprime N := by
    apply list_prod_coprime
    intro p hp
    exact (mem_roughPrimeUniverse_prime hp).coprime_iff_not_dvd.mpr
      (mem_roughPrimeUniverse_not_dvd hp)
  exact hprod.of_dvd_left (Nat.mem_divisors.mp hd).1

theorem support_squarefree (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ support N cap w z) : Squarefree q := by
  obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  exact (Nat.squarefree_mul (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
    (universe_rough N cap w z hd))).mpr
      ⟨actualSmallRosserSupport_squarefree N cap w he,
        universe_squarefree N cap w z hd⟩

theorem support_coprime_target (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ support N cap w z) : q.Coprime N := by
  obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  exact (actualSmallRosserSupport_coprime_target N cap w he).mul_left
    (universe_coprime_target N cap w z hd)

/-- The active support of the output, not of the unrounded raw policy. -/
def active (keep : List ℕ → Bool) (N cap : ℕ) (w z tau L : ℝ) : Finset ℕ :=
  (support N cap w z).filter fun q => rho keep N cap w z tau L q ≠ 0

/-- Zero output coefficients contribute neither a count nor a mean/error. -/
theorem sum_eq_active (keep : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) (f : ℕ → ℝ) :
    (∑ q ∈ support N cap w z, rho keep N cap w z tau L q * f q) =
      ∑ q ∈ active keep N cap w z tau L,
        rho keep N cap w z tau L q * f q := by
  simp only [active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : rho keep N cap w z tau L q = 0 <;> simp [hq]

/-- The support gate needed by a later primitive sharp-PP application follows
from this actual compiler output once its physical level has been proved. -/
theorem active_subset_primitive (keep : List ℕ → Bool) (N cap Q : ℕ)
    (w z tau L : ℝ)
    (hQ : ∀ q ∈ active keep N cap w z tau L, q ≤ Q) :
    active keep N cap w z tau L ⊆ chenInitialPrimitiveModuli N Q := by
  intro q hq
  have hs := (Finset.mem_filter.mp hq).1
  exact mem_chenInitialPrimitiveModuli.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (support_squarefree N cap w z hs).ne_zero,
      hQ q hq, support_coprime_target N cap w z hs⟩

/-- Actual source Fubini followed by the compiler's proved signed minorant.
No sign is imposed on rho, beta-minus, or the resulting divisor sum. -/
theorem compiled_sum_le_sifted (keep : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) :
    (∑ q ∈ support N cap w z,
      rho keep N cap w z tau L q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) ≤
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  rw [← P5S1OriginalLower.sum_physicalDivisorSum]
  calc
    _ ≤ ∑ n ∈ chenPrimeReceiverSource N,
        if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      have h := rho_minorant keep N cap w z tau L hL hwL hwz hzcap (n : ℤ)
      have hind : actualSmallRoughIndicator N z (n : ℤ) =
          if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (n : ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
          Nat.coprime_comm]
      simpa only [Int.natAbs_natCast, hind] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact recentering keeps both correction atoms and the same output rho.
In particular the modulus-prime atom is not deleted by primitive support. -/
theorem compiled_main_discrepancy_correction (keep : List ℕ → Bool)
    (N cap : ℕ) (w z tau L : ℝ) (hEven : Even N) :
    (∑ q ∈ support N cap w z,
      rho keep N cap w z tau L q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (support N cap w z) (rho keep N cap w z tau L) +
      (∑ q ∈ active keep N cap w z tau L,
        rho keep N cap w z tau L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) +
      ∑ q ∈ active keep N cap w z tau L,
        rho keep N cap w z tau L q * chenInitialPrimitiveCorrection N q := by
  have hterm (q : ℕ) :
      chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q =
        ((chenAdditivePrimeCarrier N).card : ℝ) / (Nat.totient q : ℝ) +
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q +
        chenInitialPrimitiveCorrection N q := by
    have hr := chenInitialBoundingSieve_rem_sub_primitive_error N z hEven q
    rw [chenInitialBoundingSieve_rem] at hr
    linarith only [hr]
  have hmean :
      (∑ q ∈ support N cap w z,
        rho keep N cap w z tau L q *
          (((chenAdditivePrimeCarrier N).card : ℝ) / (Nat.totient q : ℝ))) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (support N cap w z) (rho keep N cap w z tau L) := by
    simp only [physicalDensitySum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [hterm, mul_add, Finset.sum_add_distrib]
  rw [hmean,
    sum_eq_active keep N cap w z tau L
      (fun q => finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q),
    sum_eq_active keep N cap w z tau L (chenInitialPrimitiveCorrection N)]

/-- Paying the correction uses |rho|≤1, not positivity of signed rho. -/
theorem compiled_correction_abs_le_cost (keep : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) :
    |∑ q ∈ active keep N cap w z tau L,
      rho keep N cap w z tau L q * chenInitialPrimitiveCorrection N q| ≤
        chenInitialCorrectionCost N (active keep N cap w z tau L) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro q _
  rw [abs_mul]
  calc
    _ ≤ |chenInitialPrimitiveCorrection N q| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (rho_abs_le_one keep N cap w z tau L q) (abs_nonneg _)
    _ ≤ _ := abs_chenInitialPrimitiveCorrection_le N q

/-- A finite lower estimate for the actual rounded output on the original
prime source, with its actual signed primitive error left unevaluated. -/
theorem compiled_primitive_lower (keep : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) (hEven : Even N) (hL : 1 < L)
    (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (support N cap w z) (rho keep N cap w z tau L) +
      (∑ q ∈ active keep N cap w z tau L,
        rho keep N cap w z tau L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
      chenInitialCorrectionCost N (active keep N cap w z tau L) ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  have hfinite := compiled_sum_le_sifted keep N cap w z tau L hL hwL hwz hzcap
  rw [compiled_main_discrepancy_correction keep N cap w z tau L hEven] at hfinite
  have hcost := (abs_le.mp (compiled_correction_abs_le_cost keep N cap w z tau L)).1
  linarith

/-- One threshold pays the two actual prime corrections uniformly over
all later causal plans, fine meshes and supports of sublinear physical level.
This statement does not supply the signed distribution estimate. -/
theorem eventually_compiled_primitive_lower_paid
    (theta eta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (keep : List ℕ → Bool) (cap Q : ℕ) (w z tau L : ℝ),
      Even N → 1 < L → w ≤ L → w ≤ z → z ≤ (cap : ℝ) →
      (Q : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ q ∈ active keep N cap w z tau L, q ≤ Q) →
      ((chenAdditivePrimeCarrier N).card : ℝ) *
          physicalDensitySum (support N cap w z) (rho keep N cap w z tau L) +
        (∑ q ∈ active keep N cap w z tau L,
          rho keep N cap w z tau L q *
            finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
        eta * singularNormalization N ≤ ((chenSiftedPrimeSource N z).card : ℝ) := by
  filter_upwards [P5S1OriginalLower.eventually_correctionCost_le_normalized
    theta eta htheta0 htheta1 heta] with N hpaid
  intro keep cap Q w z tau L hEven hL hwL hwz hzcap hQ hsupport
  have hS := (active_subset_primitive keep N cap Q w z tau L hsupport).trans
    (chenInitialPrimitiveModuli_subset N Q)
  have hcost := hpaid Q (active keep N cap w z tau L) hQ hS
  have hfinite := compiled_primitive_lower keep N cap w z tau L hEven hL hwL hwz hzcap
  linarith

/-- The already proved raw full-policy reserve is now consumed by the actual
compiled prime-source inequality. Every loss is a defined quantity of this
same compiler output; no numerical lower constant is supplied as a premise. -/
theorem exists_compiled_full_policy_original_prime_lower :
    ∃ C K : ℝ, 0 < C ∧ 1 < K ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∃ D0 : ℝ, 2 ≤ D0 ∧ ∀ D : ℝ, D0 ≤ D →
      ∀ N cap : ℕ, Even N → ∀ (keep : List ℕ → Bool) (z tau : ℝ),
        D ^ (epsilon ^ 2) ≤ z → z ≤ (cap : ℝ) →
        let w := D ^ (epsilon ^ 2)
        let L := D ^ epsilon
        let V := actualSmallEulerProduct N cap w
        let E := actualSmallRosserDensityError C K D epsilon
        ((chenAdditivePrimeCarrier N).card : ℝ) *
          (reciprocalTotientDensity (fixedEvenRoughSupport keep N cap 0 z)
              (fixedEvenRoughCoefficient keep N cap 0 z) -
            V * roundingLoss keep N cap w z tau -
            (V * E) * reciprocalTotientDensity (universe N cap w z)
              (fun d => |coefficient keep N cap w z tau d|)) +
          (∑ q ∈ active keep N cap w z tau L,
            rho keep N cap w z tau L q *
              finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
          chenInitialCorrectionCost N (active keep N cap w z tau L) ≤
            ((chenSiftedPrimeSource N z).card : ℝ) := by
  obtain ⟨C, K, hC, hK, hsupply⟩ :=
    P2LowerFiniteCellRawDensityReserve.exists_actual_compiled_raw_density_reserve
  refine ⟨C, K, hC, hK, ?_⟩
  intro epsilon hepsilon hepsilon8
  obtain ⟨D0, hD0, hsupply⟩ := hsupply epsilon hepsilon hepsilon8
  refine ⟨D0, hD0, ?_⟩
  intro D hD N cap hEven keep z tau hwz hzcap
  have hD1 : 1 < D := by linarith
  have hepssq : epsilon ^ 2 ≤ epsilon := by nlinarith
  have hL : 1 < D ^ epsilon := Real.one_lt_rpow hD1 hepsilon
  have hwL : D ^ (epsilon ^ 2) ≤ D ^ epsilon :=
    Real.rpow_le_rpow_of_exponent_le hD1.le hepssq
  have hdensity := hsupply D hD N cap hEven keep z tau hwz
  have hmul := mul_le_mul_of_nonneg_left hdensity
    (show (0 : ℝ) ≤ ((chenAdditivePrimeCarrier N).card : ℝ) by positivity)
  have hfinite := compiled_primitive_lower keep N cap
    (D ^ (epsilon ^ 2)) z tau (D ^ epsilon) hEven hL hwL hwz hzcap
  dsimp only at hdensity hmul hfinite ⊢
  linarith


/-- The genuine chronological trace can be used directly in the rounded
compiler's first current Chen row. No equality with an invented retained
policy coefficient is postulated. Selected branch licensing is still separate. -/
theorem current_first_row_integer_trace_lower {depth m : ℕ}
    (P : P2PhysicalIncomingPrefixCells.CapPlan depth m)
    (a b seedCap : ℝ) (N cap : ℕ) (w tau L : ℝ)
    (hEven : Even N) (hL : 1 < L) (hwL : w ≤ L)
    (hwz : w ≤ (N : ℝ) ^ (417 / 5000 : ℝ))
    (hzcap : (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (cap : ℝ)) :
    let keep := P2LowerCapPlanIntegerRetention.retainEven P a b seedCap N
    let z := (N : ℝ) ^ (417 / 5000 : ℝ)
    ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (support N cap w z) (rho keep N cap w z tau L) +
      (∑ q ∈ active keep N cap w z tau L,
        rho keep N cap w z tau L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
      chenInitialCorrectionCost N (active keep N cap w z tau L) ≤
        currentChenUpsilon1 N := by
  dsimp only
  rw [currentChenUpsilon1_eq_actual_sifted_card N hEven]
  exact compiled_primitive_lower _ N cap w _ tau L hEven hL hwL hwz hzcap

end
end ImbalancedChen.P2CompiledCausalPrimeSourceLower
