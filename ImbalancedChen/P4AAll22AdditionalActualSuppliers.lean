import ImbalancedChen.P4AAll22OriginalKLedger
import ImbalancedChen.P2FirstIntegralSeries
import ImbalancedChen.ActualSelectedPrefixOwnCubeIntegral

/-!
SOURCEONLY / UNCOMPILED. Proposed import P4AAll22OriginalKLedger is the
preceding draft in this directory; it must be staged before a future build.

An additional actual positive term is substituted: the complete original first
integral, using its proved rational coarse bound. The selected sharp endpoint
is not proved by that supplier. Its full extra cost is retained explicitly;
there is NO claim that the resulting actual ledger fits the original K.

For the remaining savings, this file supplies an exact dictionary from the
actual selected fifth-prefix normalized sum to its actual owned-cell sums,
and from the integral endpoint to integrals of the two gated profiles. Neither
this dictionary nor its genuine limit identifies a selected all22 slot or
proves the frozen rational lower endpoint. Those are separate missing inputs.
No A5 or third-tail bound is proved again here.
-/
namespace ImbalancedChen.P4AAll22AdditionalActualSuppliers20261024zSourceOnly

noncomputable section
open Filter Topology MeasureTheory
open scoped Classical BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly

def actualFirstIntegral : ℝ :=
  P2FirstIntegralSeriesSourceOnly.originalFirstIntegral

def firstIntegralCoarseAllowance : ℝ :=
  (2000 / 299 : ℝ) * (51 / 2375) * (51 / 4750)

/-- This excess is explicitly charged, not silently paid from the original u. -/
def firstIntegralCoarseExcess : ℝ :=
  firstIntegralCoarseAllowance - 7179974843999672947 / 2^73

/-- A third genuine analytic term, replacing the quoted first-integral entry. -/
def threeSupplierLedger : ℝ :=
  twoSupplierLedger - 7179974843999672947 / 2^73 + actualFirstIntegral

theorem actualFirstIntegral_nonneg_and_le_coarse :
    0 ≤ actualFirstIntegral ∧ actualFirstIntegral ≤ firstIntegralCoarseAllowance := by
  exact P2FirstIntegralSeriesSourceOnly.originalFirstIntegral_rational_coarse

theorem actualFirstIntegral_literal_dictionary :
    actualFirstIntegral =
      (4 / (299 / 500 : ℝ)) *
        ∫ s in (2 : ℝ)..((299 / 500 : ℝ) / (19 / 96 : ℝ) - 1),
          Real.log (s - 1) / s := by
  exact P2FirstIntegralSeriesSourceOnly.originalFirstIntegral_semantics

theorem threeSupplierLedger_exact_replacement :
    threeSupplierLedger = twoSupplierLedger +
      (actualFirstIntegral - 7179974843999672947 / 2^73) := by
  unfold threeSupplierLedger
  ring

theorem threeSupplierLedger_le_original_plus_explicit_excess :
    threeSupplierLedger ≤ quotedAll22Raw + firstIntegralCoarseExcess := by
  unfold threeSupplierLedger firstIntegralCoarseExcess
  linarith only [twoSupplierLedger_le_quotedAll22Raw,
    actualFirstIntegral_nonneg_and_le_coarse.2]

/-- The extra coarse cost survives on the right: this is not a K density bound. -/
theorem threeSupplierLedger_reserved_le_K_plus_explicit_excess :
    threeSupplierLedger + densityReserve + compilerReserve + exactSlack ≤
      currentK + firstIntegralCoarseExcess := by
  linarith only [threeSupplierLedger_le_original_plus_explicit_excess,
    exact_original_budget_identity]

/-- A finite positive-series enclosure can refine the coarse supplier without
assuming the selected endpoint or running its rational comparison. -/
theorem threeSupplierLedger_le_series_endpoint (n : ℕ) :
    threeSupplierLedger ≤ quotedAll22Raw +
      (P2FirstIntegralSeriesSourceOnly.partialIntegral n +
        P2FirstIntegralSeriesSourceOnly.integralTail n -
          7179974843999672947 / 2^73) := by
  have h := (P2FirstIntegralSeriesSourceOnly.originalFirstIntegral_series_enclosure n).2
  change actualFirstIntegral ≤ _ at h
  unfold threeSupplierLedger
  linarith only [twoSupplierLedger_le_quotedAll22Raw, h]

/-- Actual fifth-prefix cell saving, on the ordinary parent's inherited gates.
Each of the two strict own-cube tests remains inside its profile. -/
def actualSelectedSavingCell (I : Finset (Fin 5)) (old nu a b : ℚ)
    (m : ℕ) (j : Fin 5 → Fin (m + 1)) : ℝ :=
  ∫ t in logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
      primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old),
    (primeOwnCubeGatedProfile (selectedPrefixCellCap I old nu a b m j : ℝ) t -
      primeOwnCubeGatedProfile (old : ℝ) t) * ∏ i, 1 / t i

def actualSelectedSavingCellSum (I : Finset (Fin 5)) (old nu a b : ℚ)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) : ℝ :=
  ∑ j ∈ J, actualSelectedSavingCell I old nu a b m j

/-- A proved integral-of-difference identity, with real integrability supplied
by the existing actual own-cube API rather than an enclosure hypothesis. -/
theorem actualSelectedSavingCell_eq_residual_integral_difference
    (I : Finset (Fin 5)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (j : Fin 5 → Fin (m + 1)) :
    actualSelectedSavingCell I old nu a b m j =
      primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ)
        (selectedPrefixCellCap I old nu a b m j : ℝ) m j
        ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old) -
      primeOwnCubeIcoIntegral (a : ℝ) (b : ℝ) (old : ℝ) m j
        ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old) := by
  symm
  exact primeOwnCubeIcoIntegral_sub_eq_integral
    (by exact_mod_cast ha) (by exact_mod_cast hab) (old : ℝ)
    (selectedPrefixCellCap I old nu a b m j : ℝ) m j
    ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)

theorem selectedPrefixUpperSavingIntegral_eq_actual_cell_sum
    (I : Finset (Fin 5)) (old nu a b : ℚ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) :
    selectedPrefixUpperSavingIntegral I old nu a b m J =
      actualSelectedSavingCellSum I old nu a b m J := by
  unfold selectedPrefixUpperSavingIntegral actualSelectedSavingCellSum
  apply Finset.sum_congr rfl
  intro j _hj
  exact (actualSelectedSavingCell_eq_residual_integral_difference
    I old nu a b ha hab m j).symm

/-- Inserting an owned cell changes the endpoint exactly once. This is only
an accounting identity and assumes no sign for the new cell. -/
theorem actualSelectedSavingCellSum_insert
    (I : Finset (Fin 5)) (old nu a b : ℚ) (m : ℕ)
    (J : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∉ J) :
    actualSelectedSavingCellSum I old nu a b m (insert j J) =
      actualSelectedSavingCell I old nu a b m j + actualSelectedSavingCellSum I old nu a b m J := by
  exact Finset.sum_insert hj

/-- This arithmetic cell sum contains the actual residual coefficients. -/
def actualArithmeticSavingCell (N cap : ℕ) (I : Finset (Fin 5))
    (old nu a b : ℚ) (m : ℕ) (j : Fin 5 → Fin (m + 1)) : ℝ :=
  actualPrimeBoxOwnCubeMinusSum 4 N cap (a : ℝ) (b : ℝ)
    (selectedPrefixCellCap I old nu a b m j : ℝ)
    (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
      primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old)) -
  actualPrimeBoxOwnCubeMinusSum 4 N cap (a : ℝ) (b : ℝ) (old : ℝ)
    (logPrimeMeshCell (a : ℝ) (b : ℝ) m j ∩
      primeAffineGateRegion ordinaryUpperFiveGateForms (ordinaryUpperFiveGateBounds old))

/-- Exact finite dictionary; its premises are geometric/cutoff conditions,
not a proposed saving endpoint, density bound, or asymptotic assumption. -/
theorem normalized_selected_saving_eq_actual_arithmetic_cells
    (N cap : ℕ) (I : Finset (Fin 5)) (old nu a b : ℚ)
    (hab : a < b) (hN : 1 < N) (hold : 0 < old)
    (hcap : (N : ℝ) ^ (b : ℝ) ≤ (cap : ℝ))
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) :
    actualSelectedPrefixOwnCubeSum false N cap ((N : ℝ) ^ (b : ℝ)) I old nu a b m J *
        Real.log (N : ℝ) / singularSeries N =
      ∑ j ∈ J, actualArithmeticSavingCell N cap I old nu a b m j := by
  exact actualSelectedPrefixUpperOwnCubeSum_eq_cells N cap I old nu a b hab hN hold hcap m J

/-- The same actual saving converges to the displayed cell integrals. The
only eventual premise is enumeration-cap coverage, not any analytic bound. -/
theorem tendsto_normalized_selected_saving_actual_cell_sum
    (I : Finset (Fin 5)) (old nu a b : ℚ)
    (ha : 0 < a) (hab : a < b) (hold : 0 < old)
    (m : ℕ) (J : Finset (Fin 5 → Fin (m + 1))) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualSelectedPrefixOwnCubeSum false N (cap N) ((N : ℝ) ^ (b : ℝ))
        I old nu a b m J * Real.log (N : ℝ) / singularSeries N)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (actualSelectedSavingCellSum I old nu a b m J)) := by
  rw [← selectedPrefixUpperSavingIntegral_eq_actual_cell_sum I old nu a b ha hab m J]
  exact tendsto_actualSelectedPrefixUpperOwnCubeSum I old nu a b ha hab hold m J cap hcap

end
end ImbalancedChen.P4AAll22AdditionalActualSuppliers20261024zSourceOnly
