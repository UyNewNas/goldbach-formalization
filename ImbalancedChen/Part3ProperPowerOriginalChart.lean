import ImbalancedChen.Part3OriginalDyadicChartPartition
import ImbalancedChen.Part3ProperPowerDyadicBudget

/-!
# The proper-power budget on an actual original dyadic chart

The 2026-11-06 manuscript, Appendix D.3, retains the original smooth
coordinate windows before replacing the prime indicators by normalized
von Mangoldt coefficients. This file supplies the geometric input to the
existing proper-power payment from those exact windows.

The source has the original integer dyadic shift L. We therefore take the
integer upper endpoint ceil(2 * 2^(L+j_i)), without assuming L+j_i >= 0.
A nonzero window gives n_i <= U_i and U_i+1 <= 5*n_i. One effective
nonzero tuple supplies the complete padded-box volume; an empty effective
chart has zero residual and is treated separately.

Only the original coefficient's geometric support is assumed. No box
volume bound or proper-power error estimate is taken as an input. The
remaining divisor and modulus masses are the existing explicit budgets.
This is a source candidate pending compilation in the original environment.
-/

namespace ImbalancedChen.Part3.ProperPowerOriginalChart

noncomputable section
open Classical
open scoped BigOperators

/-- The integer box is fixed by the original chart, before the modulus sum. -/
def originalChartUpper {k : ℕ} (L : ℤ) (j : Fin k → ℕ) (i : Fin k) : ℕ :=
  Nat.ceil (2 * (2 : ℝ) ^ (L + (j i : ℤ)))

def originalChartMaxUpper {k : ℕ} (L : ℤ) (j : Fin k → ℕ) : ℕ :=
  Finset.univ.sup (originalChartUpper L j)

/-- The ceiling costs no extra scale assumption: a supported positive
integer controls its chart endpoint and the padded endpoint. -/
theorem originalDyadicWindow_nat_bounds (χ : ℝ → ℝ) (e : ℤ) (n : ℕ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hn : originalDyadicWindow χ e (n : ℝ) ≠ 0) :
    n ≤ Nat.ceil (2 * (2 : ℝ) ^ e) ∧
      ((Nat.ceil (2 * (2 : ℝ) ^ e) + 1 : ℕ) : ℝ) ≤ 5 * (n : ℝ) := by
  let R : ℝ := (2 : ℝ) ^ e
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨hlo, hhi⟩ := originalDyadicWindow_support χ e (n : ℝ) χlo χhi hn
  have hlo' : (1 / 2 : ℝ) * R < (n : ℝ) :=
    (lt_div_iff₀ hR).mp hlo
  have hhi' : (n : ℝ) < 2 * R := (div_lt_iff₀ hR).mp hhi
  have hnpos : 0 < (n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hR).trans hlo'
  have hnOne : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.cast_pos.mp hnpos)
  have hcap : Nat.ceil (2 * R) ≤ 4 * n := by
    apply Nat.ceil_le.mpr
    push_cast
    linarith
  change n ≤ Nat.ceil (2 * R) ∧
    ((Nat.ceil (2 * R) + 1 : ℕ) : ℝ) ≤ 5 * (n : ℝ)
  constructor
  · exact Nat.cast_le.mp (hhi'.le.trans (Nat.le_ceil (2 * R)))
  · exact_mod_cast (show Nat.ceil (2 * R) + 1 ≤ 5 * n by omega)

/-- A nonzero original chart preserves the support of every labelled window. -/
theorem originalChart_window_ne_zero {k P : ℕ}
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ) (t : Fin k → Fin (P + 1))
    (ht : originalDyadicChartWeight χ L j t ≠ 0) (i : Fin k) :
    originalDyadicWindow χ (L + (j i : ℤ)) ((t i).val : ℝ) ≠ 0 := by
  unfold originalDyadicChartWeight at ht
  exact (Finset.prod_ne_zero_iff.mp ht) i (Finset.mem_univ i)

/-- The real source coefficient, not a prime-only restriction, supplies
the effective support needed after the von Mangoldt replacement. -/
private theorem effective_chart_nonzero {k P : ℕ}
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ) (t : Fin k → Fin (P + 1))
    (ht : (W t * originalDyadicChartWeight χ L j t) * labelledVonMangoldtWeight t ≠ 0) :
    originalDyadicChartWeight χ L j t ≠ 0 ∧
      W t * labelledVonMangoldtWeight t ≠ 0 := by
  obtain ⟨hwc, hv⟩ := mul_ne_zero_iff.mp ht
  obtain ⟨hw, hc⟩ := mul_ne_zero_iff.mp hwc
  exact ⟨hc, mul_ne_zero hw hv⟩

theorem originalChart_effective_support {k P : ℕ}
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (t : Fin k → Fin (P + 1))
    (ht : (W t * originalDyadicChartWeight χ L j t) * labelledVonMangoldtWeight t ≠ 0) :
    ∀ i, (t i).val ≤ originalChartUpper L j i := by
  intro i
  exact (originalDyadicWindow_nat_bounds χ (L + (j i : ℤ)) (t i).val χlo χhi
    (originalChart_window_ne_zero χ L j t (effective_chart_nonzero W χ L j t ht).1 i)).1

/-- One actual support point supplies both the coordinate lower scale and
the complete padded-box volume. This theorem is not applied to empty charts. -/
theorem originalChart_geometry_of_witness {k P : ℕ}
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ) (t : Fin k → Fin (P + 1))
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (ht : originalDyadicChartWeight χ L j t ≠ 0)
    {r X : ℝ} (hLower : ∀ i, r ≤ ((t i).val : ℝ))
    (hProduct : (labelledProduct t : ℝ) ≤ X) :
    (∀ i, r ≤ (originalChartUpper L j i : ℝ)) ∧
      (∏ i : Fin k, ((originalChartUpper L j i + 1 : ℕ) : ℝ)) ≤ (5 : ℝ) ^ k * X := by
  have hb (i : Fin k) := originalDyadicWindow_nat_bounds χ
    (L + (j i : ℤ)) (t i).val χlo χhi
    (originalChart_window_ne_zero χ L j t ht i)
  constructor
  · intro i
    exact (hLower i).trans (Nat.cast_le.mpr (hb i).1)
  · calc
      _ ≤ ∏ i : Fin k, (5 : ℝ) * ((t i).val : ℝ) :=
        Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => (hb i).2)
      _ = (5 : ℝ) ^ k * (labelledProduct t : ℝ) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, labelledProduct, Nat.cast_prod]
      _ ≤ _ := mul_le_mul_of_nonneg_left hProduct (pow_nonneg (by norm_num) _)

/-- The logarithmic coordinate cap is bounded by the physical complete
product, uniformly over every occupied chart. -/
theorem originalChartMaxUpper_le_of_witness {k P : ℕ}
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ) (t : Fin k → Fin (P + 1))
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (ht : originalDyadicChartWeight χ L j t ≠ 0)
    {X : ℝ} (hProduct : (labelledProduct t : ℝ) ≤ X) :
    originalChartMaxUpper L j ≤ Nat.ceil (5 * X) := by
  have hb (i : Fin k) := originalDyadicWindow_nat_bounds χ
    (L + (j i : ℤ)) (t i).val χlo χhi
    (originalChart_window_ne_zero χ L j t ht i)
  have hn (i : Fin k) : 0 < (t i).val := by
    have hp : (0 : ℝ) < ((originalChartUpper L j i + 1 : ℕ) : ℝ) := by positivity
    have hh := (hb i).2
    have hn' : (0 : ℝ) < ((t i).val : ℝ) := by
      change ((originalChartUpper L j i + 1 : ℕ) : ℝ) ≤ 5 * ((t i).val : ℝ) at hh
      linarith
    exact_mod_cast hn'
  have hprod : 0 < labelledProduct t := Finset.prod_pos (fun i _ => hn i)
  apply Finset.sup_le
  intro i _
  have hdiv : (t i).val ∣ labelledProduct t :=
    Finset.dvd_prod_of_mem (fun i => (t i).val) (Finset.mem_univ i)
  have hi : ((t i).val : ℝ) ≤ (labelledProduct t : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hprod hdiv
  have hu : (originalChartUpper L j i : ℝ) ≤ 5 * X := by
    calc
      _ ≤ ((originalChartUpper L j i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ _
      _ ≤ 5 * ((t i).val : ℝ) := (hb i).2
      _ ≤ 5 * (labelledProduct t : ℝ) := mul_le_mul_of_nonneg_left hi (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left hProduct (by norm_num)
  exact Nat.cast_le.mp (hu.trans (Nat.le_ceil (5 * X)))

/-- The original cutoff range gives an amplitude bound for each window,
without inserting a new modulus-dependent coefficient. -/
theorem originalDyadicWindow_abs_le_one
    (χ : ℝ → ℝ) (χrange : ∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) (e : ℤ) (x : ℝ) :
    |originalDyadicWindow χ e x| ≤ 1 := by
  obtain ⟨h0, h1⟩ := χrange (x / (2 : ℝ) ^ e)
  obtain ⟨h0', h1'⟩ := χrange (2 * x / (2 : ℝ) ^ e)
  unfold originalDyadicWindow
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem originalDyadicChartWeight_abs_le_one {k P : ℕ}
    (χ : ℝ → ℝ) (χrange : ∀ s, χ s ∈ Set.Icc (0 : ℝ) 1)
    (L : ℤ) (j : Fin k → ℕ) (t : Fin k → Fin (P + 1)) :
    |originalDyadicChartWeight χ L j t| ≤ 1 := by
  unfold originalDyadicChartWeight
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
    (fun i _ => originalDyadicWindow_abs_le_one χ χrange (L + (j i : ℤ)) _)

/-- Empty effective charts have zero actual residual, even when their
formal coordinate box has a very large volume. -/
theorem labelledProperPowerResidual_originalChart_eq_zero {k P : ℕ}
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ)
    (hEmpty : ¬∃ t, (W t * originalDyadicChartWeight χ L j t) * labelledVonMangoldtWeight t ≠ 0)
    (b : ℕ) :
    labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ L j t) b = 0 := by
  have hz (t : Fin k → Fin (P + 1)) :
      (W t * originalDyadicChartWeight χ L j t) * labelledVonMangoldtWeight t = 0 := by
    by_contra h
    exact hEmpty ⟨t, h⟩
  simp [labelledProperPowerResidual, finiteProductMass, hz]

/-- The actual original-chart residual is paid from the source's effective
geometric support. The lower scale and padded volume are derived from a
support witness, and the empty case is settled by zero residual.

For a positive exponent a, the displayed x^(1-a/2) is the fixed power
reserve. Divisor and modulus masses remain explicit for the later uniform
asymptotic assembly. -/
theorem labelledProperPowerResidual_originalChart_norm_le
    (k P N J D : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℂ)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (χ : ℝ → ℝ) (L : ℤ) (j : Fin k → ℕ)
    {M Cρ x c C a : ℝ} (hM : 0 ≤ M) (hCρ : 0 ≤ Cρ)
    (hx : 0 < x) (hc : 0 < c) (hC : 0 ≤ C)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (χrange : ∀ s, χ s ∈ Set.Icc (0 : ℝ) 1)
    (hW : ∀ t, |W t| ≤ M)
    (hGeometry : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
      (∀ i, c * x ^ a ≤ ((t i).val : ℝ)) ∧ (labelledProduct t : ℝ) ≤ C * x)
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J)
    (hD : ∀ b ∈ B, b ≠ N → (Nat.dist b N).divisors.card ≤ D) :
    ‖finiteProductSignedError B Q N ρ
      (labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ L j t))‖ ≤
      (M * (((k : ℝ) * (Nat.log 2 (Nat.ceil (5 * (C * x))) : ℝ) *
          ((5 : ℝ) ^ k * C) / Real.sqrt c) * x ^ (1 - a / 2))) *
        (Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q ρ) +
      (M * (properPowerDiagonalBudget k N : ℝ)) * SignedModulusPayment.modulusMass Q ρ := by
  let F : (Fin k → Fin (P + 1)) → ℝ :=
    fun t => W t * originalDyadicChartWeight χ L j t
  by_cases hActive : ∃ t, F t * labelledVonMangoldtWeight t ≠ 0
  · obtain ⟨t, ht⟩ := hActive
    have hparts := effective_chart_nonzero W χ L j t ht
    obtain ⟨hLowerT, hProductT⟩ := hGeometry t hparts.2
    obtain ⟨hLowerU, hVolumeU⟩ :=
      originalChart_geometry_of_witness χ L j t χlo χhi hparts.1 hLowerT hProductT
    have hAmplitude (s : Fin k → Fin (P + 1)) : |F s| ≤ M := by
      dsimp [F]
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _)
        (originalDyadicChartWeight_abs_le_one χ χrange L j s)).trans (hW s)
    have hVolume :
        (∏ i : Fin k, ((originalChartUpper L j i + 1 : ℕ) : ℝ)) ≤
          ((5 : ℝ) ^ k * C) * x := by
      simpa only [mul_assoc] using hVolumeU
    have hUpper := originalChartMaxUpper_le_of_witness χ L j t χlo χhi hparts.1 hProductT
    exact ProperPowerDyadicBudget.labelledProperPowerResidual_signedError_norm_le_power_scale
      k P N J D (Nat.ceil (5 * (C * x))) B Q ρ F (originalChartUpper L j)
      hM hCρ hx hc hAmplitude
      (fun s hs => originalChart_effective_support W χ L j χlo χhi s hs)
      hLowerU
      (fun i => (Finset.le_sup (f := originalChartUpper L j) (Finset.mem_univ i)).trans hUpper)
      hVolume hρ hD
  · have hz : labelledProperPowerResidual k P F = fun _ => 0 := by
      funext b
      exact labelledProperPowerResidual_originalChart_eq_zero W χ L j hActive b
    change ‖finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P F)‖ ≤ _
    rw [hz]
    simp only [finiteProductSignedError, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero]
    have hMean := SignedModulusPayment.meanMass_nonneg Q ρ
    have hModuli := SignedModulusPayment.modulusMass_nonneg Q ρ
    positivity

end
end ImbalancedChen.Part3.ProperPowerOriginalChart
