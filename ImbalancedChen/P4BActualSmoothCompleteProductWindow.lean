import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BActualSmoothFamilyWitness

/-!
# The genuine complete-product window of the actual smooth family

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The lower-product wall has normalized-log width w: its complete-product
exponent is relaxed by w. The upper-product wall has physical width w:
its endpoint is exp(w) N. The two scales are kept distinct. A caller with
kappa < kappaZero can choose the existing mass-selected family below the
additional positive cap kappaZero-kappa, preserving the required complete
product lower window. No geometric policy license or PP estimate is proved.
-/

namespace ImbalancedChen.P4BActualSmoothCompleteProductWindow

noncomputable section
open P4B P4BOuterRampRoughness P4BActualSmoothFamilyWitness
open P4BSmoothProfileCommonCompactSupport P4BLabelledLogGeometry

/-- The actual normalized lower wall gives the correct relaxed exponent
for genuine positive prime variables, with no product truncation at N. -/
theorem nonzero_smoothPrimeProfile_complete_product_lower
    {b kappa width : ℝ} {N : ℕ} (hN : 2 ≤ N) (hwidth : 0 < width)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (hnonzero : smoothPrimeVariableProfile b N
      (manuscriptHalfProductCutoff kappa N) width p ≠ 0) :
    (N : ℝ) ^ (1 - kappa - width) < p 0 * p 1 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlower := smoothPhysicalProfile_nonzero_margin_support hwidth hnonzero (2 : Fin 4)
  rw [smoothPhysicalProfileMargin_eq_original_of_ne_upper b _ N
    (primeVariableLogPoint N p) (by decide : (2 : Fin 4) ≠ 3)] at hlower
  change -width < Real.log (p 0) / Real.log (N : ℝ) +
    Real.log (p 1) / Real.log (N : ℝ) -
      Real.log (manuscriptHalfProductCutoff kappa N) / Real.log (N : ℝ) at hlower
  have hcutoff := manuscript_log_cutoff_ratio_ge (kappa := kappa) hN
  have hnormalized : 1 - kappa - width <
      (Real.log (p 0) + Real.log (p 1)) / Real.log (N : ℝ) := by
    rw [add_div]
    linarith only [hlower, hcutoff]
  have hscaled := (lt_div_iff₀ hlog).mp hnormalized
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNpos _)
    (mul_pos (hp 0) (hp 1))).mp
  rw [Real.log_rpow hNpos (1 - kappa - width),
    Real.log_mul (hp 0).ne' (hp 1).ne']
  nlinarith only [hscaled]

/-- Both physical product endpoints follow from the actual nonzero source.
An additional caller cap on w preserves its chosen lower trim exponent. -/
theorem nonzero_smoothPrimeProfile_complete_product_window
    {b kappa kappaZero width : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hwidth : 0 < width) (hwidthCap : width ≤ kappaZero - kappa)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (hnonzero : smoothPrimeVariableProfile b N
      (manuscriptHalfProductCutoff kappa N) width p ≠ 0) :
    (N : ℝ) ^ (1 - kappaZero) < p 0 * p 1 ∧
      p 0 * p 1 < Real.exp width * (N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hpow : (N : ℝ) ^ (1 - kappaZero) ≤ (N : ℝ) ^ (1 - kappa - width) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith only [hwidthCap])
  exact ⟨hpow.trans_lt (nonzero_smoothPrimeProfile_complete_product_lower
    hN hwidth hp hnonzero),
    smoothPrimeVariableProfile_nonzero_product_lt_exp_mul_N hN1 hwidth hp hnonzero⟩

/-- The real arithmetic mass-selected family can obey the additional local
trim cap before any target, prime variable or discrepancy constant is chosen. -/
theorem exists_actualSmoothFamily_with_complete_product_window
    {b kappa kappaZero theta eta : ℝ}
    (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hkappaTrim : kappa < kappaZero) (htheta : 0 < theta) (heta : 0 < eta)
    (hgap : theta < baseline b kappa) :
    ∃ F : ActualSmoothFamilyWitness b kappa theta eta (kappaZero - kappa),
      ∀ N : ℕ, 2 ≤ N → ∀ p : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
        smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
          F.width p ≠ 0 →
        (N : ℝ) ^ (1 - kappaZero) < p 0 * p 1 ∧
          p 0 * p 1 < Real.exp F.width * (N : ℝ) := by
  obtain ⟨F⟩ := nonempty_actualSmoothFamilyWitness
    hbLower hbUpper hkappa hkappaOne htheta heta (sub_pos.mpr hkappaTrim) hgap
  refine ⟨F, ?_⟩
  intro N hN p hp hn
  exact nonzero_smoothPrimeProfile_complete_product_window
    hN F.width_pos F.width_le hp hn

end
end ImbalancedChen.P4BActualSmoothCompleteProductWindow
