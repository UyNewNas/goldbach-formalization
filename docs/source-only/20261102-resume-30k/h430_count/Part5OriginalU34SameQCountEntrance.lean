import ImbalancedChen.Part5OriginalU34PhysicalCutoffSource
import ImbalancedChen.P5OriginalU5FrozenSource
import ImbalancedChen.P2SameQPhysicalRosserSeed
import ImbalancedChen.P2AllW2ImmutableCountRecursion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original U3/U4 rows enter the immutable all70-W1/all36-W2 arithmetic
recursion with their original Q and the actual prime receiver. This is
not a soundness assertion for the adopted H430 integers. The raw switched
counts and both signed seed errors remain literal arithmetic quantities.
The companion file pays the two deterministic prime-source corrections.
-/
namespace ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance

noncomputable section
open Set Finset Filter Wu2008DoubleSieve
open Part5OriginalUpsilon5CausalDictionary (a)
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState (Query rootLevel)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalU5FrozenSource (receiver)
open P2SameQPhysicalRosserSeed (seedMain seedError)
open scoped Classical BigOperators

def rowCutoff (N p : ℕ) (r : ℝ → ℝ) : ℝ :=
  cutoff (rowTotalLevel N p r) p (rootArgument r (primeCoordinate N p))

def rowSeed (side : Bool) (N p : ℕ) (r : ℝ → ℝ) (eta : ℝ) : ℝ :=
  seedMain side N p (rowTotalLevel N p r)
    (rootArgument r (primeCoordinate N p)) eta

def rowError (side : Bool) (N p : ℕ) (r : ℝ → ℝ) : ℝ :=
  seedError side N p (rowTotalLevel N p r)
    (rootArgument r (primeCoordinate N p)) (receiver N)

def rowState (N p : ℕ) (r : ℝ → ℝ) (bank : List Query) (rounds : ℕ) :=
  P2AllW2ImmutableCountRecursion.iterate N (rowTotalLevel N p r) (receiver N) bank rounds

/-- Q/p is recovered from the actual prime logarithm, before rounding the
residual level. In particular no descendant replaces Q by a new root. -/
theorem row_residual_identity {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    (r : ℝ → ℝ) :
    rowTotalLevel N p r / (p : ℝ) = (N : ℝ) ^ r (primeCoordinate N p) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hrecover : (N : ℝ) ^ primeCoordinate N p = (p : ℝ) := by
    rw [primeCoordinate, Real.rpow_def_of_pos hNp]
    rw [mul_div_cancel₀ _ (Real.log_pos hNr).ne', Real.exp_log hpp]
  unfold rowTotalLevel
  rw [Real.rpow_add hNp, hrecover]
  field_simp [hpp.ne'] <;> ring

theorem rowCutoff_eq_physical {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    rowCutoff N p r = (N : ℝ) ^ physicalExponent r (primeCoordinate N p) :=
  row_sameQ_cutoff hN hp hr

/-- Both true bands have the same residual lower and upper bounds needed
below. These bounds include the entire finite-reserve U3 clamp. -/
theorem U4_residual_bounds {t : ℝ} (ht : t ∈ Set.Ico a (59 / 250 : ℝ)) :
    (1 / 12 : ℝ) ≤ mainResidual t ∧ mainResidual t ≤ 1 / 2 := by
  have hlo := mainResidual_gt_two_a (ht.2.trans (by norm_num [tailCutoff]))
  exact ⟨by norm_num [a] at hlo ⊢; linarith,
    (mainResidual_bounds ⟨ht.1, ht.2.le.trans (by norm_num)⟩).2⟩

theorem U3_level_exponent_cap {tau t : ℝ} (htau : 0 ≤ tau) :
    t + U3Residual tau t ≤ (153 / 256 : ℝ) := by
  by_cases ht : t < tailCutoff
  · simp only [U3Residual, if_pos ht, mainResidual]
    have hv := VariableEnvelope.v_le_cap t
    dsimp [VariableEnvelope.cap] at hv
    linarith
  · simp only [U3Residual, if_neg ht, tailResidual]
    linarith

theorem U4_level_exponent_cap (t : ℝ) :
    t + mainResidual t ≤ (153 / 256 : ℝ) := by
  have hv := VariableEnvelope.v_le_cap t
  dsimp [mainResidual, VariableEnvelope.cap] at *
  linarith

/-- A reusable exact cap on the original row Q. This is not a distribution
licence at the enhanced exponent 153/256. -/
theorem row_level_cap {N p : ℕ} (hN : 2 ≤ N) {r : ℝ → ℝ}
    (hc : primeCoordinate N p + r (primeCoordinate N p) ≤ 153 / 256) :
    rowTotalLevel N p r ≤ (N : ℝ) ^ (153 / 256 : ℝ) ∧
      rowTotalLevel N p r ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hq : rowTotalLevel N p r ≤ (N : ℝ) ^ (153 / 256 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hc
  refine ⟨hq, hq.trans ?_⟩
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (153 / 256 : ℝ) ≤ 1)

theorem row_residual_gt_one {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p)
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    1 < rowTotalLevel N p r / (p : ℝ) := by
  rw [row_residual_identity hN hp r]
  exact Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) hr

/-- The selected prime itself is rough at the physical clamped cutoff.
This proves the premise of J's exact masked/unmasked source dictionary. -/
theorem row_prefix_rough {N p : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U))
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    ChenPrimeRough (rowCutoff N p r) p := by
  have hprime := (mem_chenAdditivePrimeCarrier.mp (mem_filter.mp hp).1).2.1
  intro q hq hqp
  have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hprime).mp hqp
  subst q
  exact row_sameQ_cutoff_le_selected_prime hN hp hr

theorem row_frozenCount_eq_original {N p : ℕ} (hN : 2 ≤ N) {U : ℝ}
    (hp : p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U))
    {r : ℝ → ℝ} (hr : 0 < r (primeCoordinate N p)) :
    (frozenCount N p (receiver N) (rowCutoff N p r) : ℝ) =
      ((chenSiftedQuotientPrimeSource N p (rowCutoff N p r)).card : ℝ) :=
  P5OriginalU5FrozenSource.frozenCount_eq_original_count N p _ (row_prefix_rough hN hp hr)

/-- Retention for the JOINT arithmetic recursion, including all36 W2
actions. No assumption about a sound seed or a previous count is supplied. -/
theorem joint_retains_initial (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (z : ℝ) :
    frozenPolynomial false N d (rootLevel Q d) E z ≤
      (P2AllW2ImmutableCountRecursion.iterate N Q E bank rounds).lower d z ∧
    (P2AllW2ImmutableCountRecursion.iterate N Q E bank rounds).upper d z ≤
      frozenPolynomial true N d (rootLevel Q d) E z := by
  induction rounds with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have h := P2AllW2ImmutableCountRecursion.iterate_retains_previous N Q E bank n d z
    exact ⟨ih.1.trans h.1, h.2.trans ih.2⟩

/-- One common threshold precedes the actual rows, their level functions,
every bank and every finite number of immutable actions. Signed errors
are retained; no positive H430 defect is smuggled into this statement. -/
theorem row_seed_and_joint_count {eta : ℝ} (heta : 0 < eta) :
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ U : ℝ, ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a) ((N : ℝ) ^ U),
      ∀ r : ℝ → ℝ,
      (1 / 12 : ℝ) ≤ r (primeCoordinate N p) → r (primeCoordinate N p) ≤ 1 / 2 →
      ∀ bank : List Query, ∀ rounds : ℕ,
        rowSeed false N p r eta + rowError false N p r ≤
          (rowState N p r bank rounds).lower p (rowCutoff N p r) ∧
        (rowState N p r bank rounds).lower p (rowCutoff N p r) ≤
          ((chenSiftedQuotientPrimeSource N p (rowCutoff N p r)).card : ℝ) ∧
        ((chenSiftedQuotientPrimeSource N p (rowCutoff N p r)).card : ℝ) ≤
          (rowState N p r bank rounds).upper p (rowCutoff N p r) ∧
        (rowState N p r bank rounds).upper p (rowCutoff N p r) ≤
          rowSeed true N p r eta + rowError true N p r := by
  obtain ⟨N0, hN0, hseed⟩ := P2SameQPhysicalRosserSeed.sameQ_polynomial_seed
    (by norm_num : (0 : ℝ) < 1 / 12) heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN he U p hp r hrlo hrhi bank rounds
  have hN2 : 2 ≤ N := by omega
  have hpp := (mem_chenAdditivePrimeCarrier.mp (mem_filter.mp hp).1).2.1.pos
  have hrpos : 0 < r (primeCoordinate N p) := lt_of_lt_of_le (by norm_num) hrlo
  have hR := row_residual_gt_one hN2 hpp hrpos
  have hres : (N : ℝ) ^ (1 / 12 : ℝ) ≤ rowTotalLevel N p r / (p : ℝ) := by
    rw [row_residual_identity hN2 hpp r]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) hrlo
  have hs : 2 ≤ rootArgument r (primeCoordinate N p) := le_max_left _ _
  have hs10 : rootArgument r (primeCoordinate N p) ≤ 10 := by
    apply max_le (by norm_num)
    apply (div_le_iff₀ (by norm_num [a] : 0 < a)).mpr
    norm_num [a] at *
    linarith
  have hb := hseed N hN he (rowTotalLevel N p r) p
    (rootArgument r (primeCoordinate N p)) (receiver N) hres hs hs10
  have ht := joint_retains_initial N (rowTotalLevel N p r) (receiver N)
    bank rounds p (rowCutoff N p r)
  have hc := P2AllW2ImmutableCountRecursion.iterate_encloses N (rowTotalLevel N p r)
    (receiver N) bank rounds p (rowCutoff N p r)
    (P2AllW1SameQRawCountInduction.cutoff_query hpp hR (by linarith))
  rw [row_frozenCount_eq_original hN2 hp hrpos] at hc
  exact ⟨hb.1.trans ht.1, hc.1, hc.2, ht.2.trans hb.2⟩

end
end ImbalancedChen.Part5UpperTables.OriginalU34.CountEntrance
