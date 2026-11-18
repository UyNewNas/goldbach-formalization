import ImbalancedChen.P3HBRestoredSixCoordinateD
import Mathlib.Tactic

/-!
P3.6 / pinned paper 9731290e8f53cffda44129906cde6a965eaa869b
paper/source/modules/distribution-prime-product-completion-20261010.txt,
sections 2 and 4 (F).

Pay the genuine finite six-coordinate 2S SUM, not only a separate bound
for each 2S word. This produces a single coefficient independent of
the actual number g of HB group occurrences and their positive scales.
In particular it gives an explicit (g+1)^12 budget and, CONDITIONAL on
g+1 <= log(T)^E, an explicit log(T)^(12*E) budget.

The mathematical input is the preceding actual restored 729-child
integrated source candidate, with precisely the original adjacent
doubled S.toList words, and not an assumption of the desired D bound.
No statement identifies this six-position family with all physical
W_T sources, or proves the same-rho arithmetic PP estimate.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBRestoredSixPolynomialD
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBRestoredSixCoordinateD
open ImbalancedChen.P3HBOriginalRestoredTensorL1
open ImbalancedChen.P3U5ChartMixedL1Budget

/-- The finite true six-axis 2S ledger has a single uniform polynomial
upper bound of degree 12 in the original group count. The new constant
is chosen BEFORE g, group incidence, scales, and all integration points.
No new smoothness or target-integral bound is hypothesized. -/
theorem sixRestoredMixedD_poly12
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1) :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          (∀ S : Finset (Fin 6),
            Integrable (fun u : Fin 6 → ℝ =>
              ‖originalRestoredWholeDerivative chi eta c J s
                (fun _ => 0)
                (fun i : Fin (doubled S).length => (doubled S)[i]) u‖)) ∧
          sixRestoredMixedD chi eta c J s ≤
            Cpoly * (((g : ℝ) + 1) ^ 12) := by
  classical
  obtain ⟨B, Ceta, C, hB, hCeta, hC, hbase⟩ :=
    sixRestoredMixedD_integrable_budget chi eta hchi heta
      hsmall hlarge hpsi hetaSmall hetaLarge
  let mass : ℝ :=
    (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6
  have hlog : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    positivity
  let Cpoly : ℝ :=
    ∑ S : Finset (Fin 6),
      (4 * B) ^ (doubled S).length * Ceta * mass
  have hCpoly : 0 ≤ Cpoly := by
    dsimp [Cpoly]
    apply Finset.sum_nonneg
    intro S _
    have h4B : 0 ≤ (4 : ℝ) * B := by positivity
    positivity
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro g c J hc s hs
  obtain ⟨hint, hbound⟩ := hbase g c J hc s hs
  have hg : (1 : ℝ) ≤ (g : ℝ) + 1 := by
    have hgn : 0 ≤ (g : ℝ) := Nat.cast_nonneg g
    linarith
  have hterm (S : Finset (Fin 6)) :
      (2 : ℝ) ^ (doubled S).length *
        (((2 : ℝ) ^ (doubled S).length *
            (((g : ℝ) + 1) * B) ^ (doubled S).length * Ceta) *
          mass) ≤
      (((g : ℝ) + 1) ^ 12) *
        ((4 * B) ^ (doubled S).length * Ceta * mass) := by
    let k := (doubled S).length
    have hk : k ≤ 12 := doubled_six_length_le_twelve S
    have hfour : (2 : ℝ) ^ k * (2 : ℝ) ^ k = (4 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num
    have hmonom :
        (2 : ℝ) ^ k *
          ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k) =
        ((g : ℝ) + 1) ^ k * (4 * B) ^ k := by
      calc
        _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ k) *
              (((g : ℝ) + 1) * B) ^ k := by ring
        _ = (4 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k := by rw [hfour]
        _ = ((g : ℝ) + 1) ^ k * (4 * B) ^ k := by
          rw [mul_pow, mul_pow]
          ring
    have hpower : ((g : ℝ) + 1) ^ k ≤ ((g : ℝ) + 1) ^ 12 :=
      pow_le_pow_right₀ hg hk
    have hfactor : 0 ≤ (4 * B) ^ k * Ceta * mass := by
      have h4B : 0 ≤ (4 : ℝ) * B := by positivity
      positivity
    change (2 : ℝ) ^ k *
      (((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta) *
        mass) ≤
      (((g : ℝ) + 1) ^ 12) * ((4 * B) ^ k * Ceta * mass)
    calc
      _ = ((2 : ℝ) ^ k *
            ((2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k)) *
              (Ceta * mass) := by ring
      _ = (((g : ℝ) + 1) ^ k * (4 * B) ^ k) *
            (Ceta * mass) := by rw [hmonom]
      _ = ((g : ℝ) + 1) ^ k *
            ((4 * B) ^ k * Ceta * mass) := by ring
      _ ≤ ((g : ℝ) + 1) ^ 12 *
            ((4 * B) ^ k * Ceta * mass) :=
          mul_le_mul_of_nonneg_right hpower hfactor
  refine ⟨hint, ?_⟩
  calc
    sixRestoredMixedD chi eta c J s ≤
        ∑ S : Finset (Fin 6),
          (2 : ℝ) ^ (doubled S).length *
            (((2 : ℝ) ^ (doubled S).length *
                (((g : ℝ) + 1) * B) ^ (doubled S).length * Ceta) *
              mass) := by
        simpa only [mass] using hbound
    _ ≤ ∑ S : Finset (Fin 6),
          (((g : ℝ) + 1) ^ 12) *
            ((4 * B) ^ (doubled S).length * Ceta * mass) := by
        apply Finset.sum_le_sum
        intro S _
        exact hterm S
    _ = Cpoly * (((g : ℝ) + 1) ^ 12) := by
        dsimp [Cpoly]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S _
        ring

/-- The same bound on a specific admissible logarithmic range.
The growth condition on the number of groups is an EXPLICIT, ordinary
geometric size condition, not an assumption of PP or of an L1 estimate.
It still does not prove that every growing-rank original W_T is this
fixed-six-position geometry. -/
theorem sixRestoredMixedD_polylog_of_group_growth
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (E : ℕ) :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ N : ℕ, 1 ≤ Real.log (N : ℝ) →
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ((g : ℝ) + 1) ≤ (Real.log (N : ℝ)) ^ E →
          (∀ S : Finset (Fin 6),
            Integrable (fun u : Fin 6 → ℝ =>
              ‖originalRestoredWholeDerivative chi eta c J s
                (fun _ => 0)
                (fun i : Fin (doubled S).length => (doubled S)[i]) u‖)) ∧
          sixRestoredMixedD chi eta c J s ≤
            Cpoly * (Real.log (N : ℝ)) ^ (E * 12) := by
  obtain ⟨Cpoly, hCpoly, hpoly⟩ :=
    sixRestoredMixedD_poly12 chi eta hchi heta
      hsmall hlarge hpsi hetaSmall hetaLarge
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro N hN g c J hc s hs hgrowth
  obtain ⟨hint, hbound⟩ := hpoly g c J hc s hs
  have hgnonneg : (0 : ℝ) ≤ (g : ℝ) + 1 := by positivity
  have hpow :
      (((g : ℝ) + 1) ^ 12) ≤
        ((Real.log (N : ℝ)) ^ E) ^ 12 :=
    pow_le_pow_left₀ hgnonneg hgrowth 12
  refine ⟨hint, ?_⟩
  calc
    sixRestoredMixedD chi eta c J s ≤
        Cpoly * (((g : ℝ) + 1) ^ 12) := hbound
    _ ≤ Cpoly * ((Real.log (N : ℝ)) ^ E) ^ 12 :=
      mul_le_mul_of_nonneg_left hpow hCpoly
    _ = Cpoly * (Real.log (N : ℝ)) ^ (E * 12) := by
      rw [pow_mul]

end
end ImbalancedChen.P3HBRestoredSixPolynomialD
