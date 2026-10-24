import ImbalancedChen.P1HistoricalUpperFourthJointGeometry
import ImbalancedChen.ActualRosserResidualDensity

/-!
# P1: strict physical gates for the historical fourth PLUS residual

The inherited third cube implies the strict PLUS legality gate at rank four.
Both old and new residuals have quotient level above the terminal prime.
For an actually nonzero upper Rosser coefficient its complete physical modulus
is bounded at that same level, with no missing prefix factor.

This module assumes no distribution/factorization license and asserts no fixed
support exponent. The full displayed divisor support is never mistaken for the
active nonzero support.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open Set

/-- At rank four the inherited third cube is stronger than PLUS legality. -/
theorem p1_fourth_plus_gate_of_third (t : Fin 4 → ℝ) (lambda : ℝ)
    (hs : StrictAnti t) (hthird : t 0 + t 1 + 3 * t 2 < lambda) :
    (∑ i, t i) + t 3 < lambda := by
  have hsum : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  have h32 : t 3 < t 2 := hs (by decide : (2 : Fin 4) < 3)
  rw [hsum]
  linarith

namespace HistoricalPrefixCapData

theorem p1_old4_le_cell4 (D : HistoricalPrefixCapData) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) : D.old4 j ≤ D.cell4 j := by
  unfold cell4
  split_ifs with hj
  · exact (D.levelCheck_sound hcheck).2.1 j hj
  · exact le_rfl

end HistoricalPrefixCapData

/-- All displayed residual coordinates come from the same admitted tuple.
In particular the PLUS source condition s>1 is proved at both levels. -/
theorem p1_admittedFourth_plusLegality_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1))
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    0 < actualPrimeTupleLog N p 3 ∧
      (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 < (D.old4 j : ℝ) ∧
      (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 < (D.cell4 j : ℝ) ∧
      (∑ i, actualPrimeTupleLog N p i) < (D.old4 j : ℝ) ∧
      (∑ i, actualPrimeTupleLog N p i) < (D.cell4 j : ℝ) ∧
      1 < ((D.old4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) /
        actualPrimeTupleLog N p 3 ∧
      1 < ((D.cell4 j : ℝ) - ∑ i, actualPrimeTupleLog N p i) /
        actualPrimeTupleLog N p 3 := by
  have hd := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab hcheck N cap hN hcap p j ht).mp hp
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlast : (1 : ℝ) < p 3 := by exact_mod_cast (hd.2.1 3).1.one_lt
  have hpos : 0 < actualPrimeTupleLog N p 3 :=
    div_pos (Real.log_pos hlast) (Real.log_pos hn)
  have hs : StrictAnti (actualPrimeTupleLog N p) :=
    (actualPrimeTupleLog_strictAnti_iff hN p (fun i => (hd.2.1 i).1.pos)).mpr hd.1
  have hold := p1_fourth_plus_gate_of_third (actualPrimeTupleLog N p) (D.old4 j : ℝ)
    hs hd.2.2.2
  have hlevels : (D.old4 j : ℝ) ≤ D.cell4 j := by
    exact_mod_cast D.p1_old4_le_cell4 hcheck j
  have hnew := hold.trans_le hlevels
  refine ⟨hpos, hold, hnew, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · apply (one_lt_div hpos).mpr
    linarith
  · apply (one_lt_div hpos).mpr
    linarith

/-- Exact tuple product recovery, including the original target as base. -/
theorem p1_fourth_rpow_sum {N : ℕ} (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) :
    (N : ℝ) ^ (∑ i, actualPrimeTupleLog N p i) = (∏ i, p i : ℕ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hp i)
  rw [actualPrimeTupleLog_sum_prod p hp]
  exact residual_rpow_log_div _ _ hn hP

/-- The literal quotient is the exponent obtained by subtracting all four
prefix coordinates; no prefix prime is omitted from its denominator. -/
theorem p1_fourth_quotient_rpow {N : ℕ} (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (lambda : ℝ) :
    (N : ℝ) ^ lambda / (∏ i, p i : ℕ) =
      (N : ℝ) ^ (lambda - ∑ i, actualPrimeTupleLog N p i) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_sub (zero_lt_one.trans hn), p1_fourth_rpow_sum hN p hp]

/-- A strict affine PLUS gate is precisely the terminal-prime quotient
condition for these actual integer labels. -/
theorem p1_fourth_plus_gate_iff_quotient {N : ℕ} (hN : 1 < N) (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (lambda : ℝ) :
    (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 < lambda ↔
      (p 3 : ℝ) < (N : ℝ) ^ lambda / (∏ i, p i : ℕ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  rw [p1_fourth_quotient_rpow hN p hp,
    ← actualPrimeTupleLog_rpow hN p hp 3, Real.rpow_lt_rpow_left_iff hn]
  linarith

/-- Both actual quotient levels are legal for the positive upper residual;
the associated strict total-product bounds are also derived. -/
theorem p1_admittedFourth_physical_levels_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1))
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    ((∏ i, p i : ℕ) : ℝ) < (N : ℝ) ^ (D.old4 j : ℝ) ∧
      ((∏ i, p i : ℕ) : ℝ) < (N : ℝ) ^ (D.cell4 j : ℝ) ∧
      (p 3 : ℝ) < (N : ℝ) ^ (D.old4 j : ℝ) / (∏ i, p i : ℕ) ∧
      (p 3 : ℝ) < (N : ℝ) ^ (D.cell4 j : ℝ) / (∏ i, p i : ℕ) := by
  have hd := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab hcheck N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hd.2.1 i).1.pos
  have hl := p1_admittedFourth_plusLegality_on_cell D hab hcheck N cap hN hcap p j hp ht
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← p1_fourth_rpow_sum hN p hpos, Real.rpow_lt_rpow_left_iff hn]
    exact hl.2.2.2.1
  · rw [← p1_fourth_rpow_sum hN p hpos, Real.rpow_lt_rpow_left_iff hn]
    exact hl.2.2.2.2.1
  · exact (p1_fourth_plus_gate_iff_quotient hN p hpos _).mp hl.2.1
  · exact (p1_fourth_plus_gate_iff_quotient hN p hpos _).mp hl.2.2.1

/-- The actual, nonzero upper residual coefficient retains the displayed
prime carrier, rather than selecting arbitrary divisors below a level. -/
def p1_fourthPlusActiveDivisors (N cap : ℕ) (lambda : ℝ) (p : Fin 4 → ℕ) : Finset ℕ :=
  (actualSmallRosserSupport N cap (p 3 : ℝ)).filter fun d =>
    actualSmallRosserPlus N cap (p 3 : ℝ) ((N : ℝ) ^ lambda / (∏ i, p i : ℕ)) d ≠ 0

/-- Full physical moduli include all four selected primes.  The strict
bound comes from this actual coefficient's active support theorem. -/
theorem p1_fourthPlusActive_physical_lt {N cap d : ℕ} {lambda : ℝ}
    {p : Fin 4 → ℕ} (hp : ∀ i, 0 < p i)
    (hd : d ∈ p1_fourthPlusActiveDivisors N cap lambda p) :
    (0 < d) ∧ (((∏ i, p i) * d : ℕ) : ℝ) < (N : ℝ) ^ lambda ∧
      Squarefree d ∧ d.Coprime N ∧ SmallPrimeSupportedAt (p 3 : ℝ) d := by
  have ha := actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hp i)
  have hphysical : (((∏ i, p i) * d : ℕ) : ℝ) < (N : ℝ) ^ lambda := by
    have h := (lt_div_iff₀ hP).mp ha.2.1
    simpa only [Nat.cast_mul, mul_comm] using h
  exact ⟨Nat.pos_of_ne_zero ha.2.2.1, hphysical,
    actualSmallRosserSupport_squarefree N cap _ ha.1,
    actualSmallRosserSupport_coprime_target N cap _ ha.1, ha.2.2⟩

/-- Logarithmic complete-modulus gate, preserving its strict endpoint. -/
theorem p1_fourth_physical_lt_iff_affine {N d : ℕ} (hN : 1 < N)
    (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) (hd : 0 < d) (lambda : ℝ) :
    (((∏ i, p i) * d : ℕ) : ℝ) < (N : ℝ) ^ lambda ↔
      (∑ i, actualPrimeTupleLog N p i) + Real.log (d : ℝ) / Real.log (N : ℝ) < lambda := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hP : (0 : ℝ) < (∏ i, p i : ℕ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => hp i)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : (N : ℝ) ^ (Real.log (d : ℝ) / Real.log (N : ℝ)) = d :=
    residual_rpow_log_div _ _ hn hd'
  have hprod : (N : ℝ) ^ ((∑ i, actualPrimeTupleLog N p i) +
      Real.log (d : ℝ) / Real.log (N : ℝ)) = (((∏ i, p i) * d : ℕ) : ℝ) := by
    rw [Real.rpow_add (zero_lt_one.trans hn), p1_fourth_rpow_sum hN p hp, hr, Nat.cast_mul]
  rw [← hprod, Real.rpow_lt_rpow_left_iff hn]

/-- Active actual residual coefficients satisfy the additional complete
modulus affine gate; it is a conclusion, not a caller-supplied license. -/
theorem p1_fourthPlusActive_affine_gate {N cap d : ℕ} (hN : 1 < N)
    {lambda : ℝ} {p : Fin 4 → ℕ} (hp : ∀ i, 0 < p i)
    (hd : d ∈ p1_fourthPlusActiveDivisors N cap lambda p) :
    (∑ i, actualPrimeTupleLog N p i) + Real.log (d : ℝ) / Real.log (N : ℝ) < lambda := by
  have ha := p1_fourthPlusActive_physical_lt hp hd
  exact (p1_fourth_physical_lt_iff_affine hN p hp ha.1 lambda).mp ha.2.1

/-- The added old/new PLUS and product gates are redundant on the actual
joint-cell dictionary; no actual admitted tuple is discarded. -/
theorem p1_fourth_admitted_cell_filter_plus_gates
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 4 → Fin (D.m + 1)) :
    (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
    (firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
      (fun p => actualPrimeTupleLog N p ∈
        logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∧
        (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 < (D.old4 j : ℝ) ∧
        (∑ i, actualPrimeTupleLog N p i) + actualPrimeTupleLog N p 3 < (D.cell4 j : ℝ) ∧
        (∑ i, actualPrimeTupleLog N p i) < (D.old4 j : ℝ) ∧
        (∑ i, actualPrimeTupleLog N p i) < (D.cell4 j : ℝ)) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, ht⟩
    have hl := p1_admittedFourth_plusLegality_on_cell D hab hcheck N cap hN hcap p j hp ht
    exact ⟨hp, ht, hl.2.1, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2.1⟩
  · rintro ⟨hp, ht, _⟩
    exact ⟨hp, ht⟩

/-- The physical residual parameters are the actual four-coordinate
quotient and the actual terminal cutoff. -/
theorem p1_fourth_quotientParameters_eq (N : ℕ) (p : Fin 4 → ℕ)
    (hp : ∀ i, 0 < p i) (lambda : ℝ) :
    actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 3 : ℝ) lambda =
      (lambda - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p 3) := by
  change (lambda - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ),
    actualPrimeTupleLog N p 3) = _
  rw [actualPrimeTupleLog_sum_prod p hp]

/-- Adding the complete physical-modulus bound removes no nonzero actual
coefficient.  The inactive displayed divisors were already removed. -/
theorem p1_fourthPlusActive_filter_physical (N cap : ℕ) (lambda : ℝ)
    (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    (p1_fourthPlusActiveDivisors N cap lambda p).filter
      (fun d => (((∏ i, p i) * d : ℕ) : ℝ) < (N : ℝ) ^ lambda) =
        p1_fourthPlusActiveDivisors N cap lambda p := by
  apply Finset.filter_eq_self.mpr
  intro d hd
  exact (p1_fourthPlusActive_physical_lt hp hd).2.1

/-- The affine complete-modulus gate is likewise redundant on the same
actual active support, with the original strict level. -/
theorem p1_fourthPlusActive_filter_affine (N cap : ℕ) (hN : 1 < N) (lambda : ℝ)
    (p : Fin 4 → ℕ) (hp : ∀ i, 0 < p i) :
    (p1_fourthPlusActiveDivisors N cap lambda p).filter
      (fun d => (∑ i, actualPrimeTupleLog N p i) +
        Real.log (d : ℝ) / Real.log (N : ℝ) < lambda) =
      p1_fourthPlusActiveDivisors N cap lambda p := by
  apply Finset.filter_eq_self.mpr
  intro d hd
  exact p1_fourthPlusActive_affine_gate hN hp hd

/-- The parent gates and the complete physical-modulus gate hold jointly
for an actual admitted fourth tuple and an actual nonzero PLUS divisor.
Instantiate lambda with old4 j or cell4 j for the two historical residuals. -/
theorem p1_admittedFourthPlusActive_joint_gates
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 4 → ℕ) (j : Fin 4 → Fin (D.m + 1)) (lambda : ℝ) (d : ℕ)
    (hp : p ∈ firstExitAdmittedTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j)
    (hd : d ∈ p1_fourthPlusActiveDivisors N cap lambda p) :
    3 * actualPrimeTupleLog N p 0 < (D.old : ℝ) ∧
      actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
        3 * actualPrimeTupleLog N p 2 < (D.old4 j : ℝ) ∧
      ((∏ i, p i : ℕ) : ℝ) < (N : ℝ) ^ (D.old4 j : ℝ) ∧
      ((∏ i, p i : ℕ) : ℝ) < (N : ℝ) ^ (D.cell4 j : ℝ) ∧
      (((∏ i, p i) * d : ℕ) : ℝ) < (N : ℝ) ^ lambda ∧
      (∑ i, actualPrimeTupleLog N p i) +
        Real.log (d : ℝ) / Real.log (N : ℝ) < lambda := by
  have hdict := (p1_mem_historicalUpperFourthAdmittedTuples_iff_log_on_cell
    D hab hcheck N cap hN hcap p j ht).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (hdict.2.1 i).1.pos
  have hlevels := p1_admittedFourth_physical_levels_on_cell
    D hab hcheck N cap hN hcap p j hp ht
  exact ⟨hdict.2.2.1, hdict.2.2.2, hlevels.1, hlevels.2.1,
    (p1_fourthPlusActive_physical_lt hpos hd).2.1,
    p1_fourthPlusActive_affine_gate hN hpos hd⟩

end
end ImbalancedChen
