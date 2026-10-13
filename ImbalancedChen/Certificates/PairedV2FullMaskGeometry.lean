import ImbalancedChen.Certificates.PairedV2FullMask

namespace ImbalancedChen.Certificates.PairedV2.FullMask

theorem row_endpoint_bounds (r : Row) :
    a < cutoff r ∧ cutoff r ≤ uLower (indices r).2 ∧
      uLower (indices r).2 < uUpper (indices r).2 ∧
      uUpper (indices r).2 ≤ h ∧ h < tLower (indices r).1 ∧
      tLower (indices r).1 < tUpper (indices r).1 ∧
      tUpper (indices r).1 ≤ d ∧
      (13 / 3 : ℚ) * cutoff r ≤
        1 - tUpper (indices r).1 - uUpper (indices r).2 := by
  obtain ⟨hi, hj0, hj⟩ := indices_bounds r
  have hiR : ((indices r).1 : ℚ) < 512 := by exact_mod_cast hi
  have hjR : ((indices r).2 : ℚ) < 512 := by exact_mod_cast hj
  have hiS : ((indices r).1 : ℚ) + 1 ≤ 512 := by exact_mod_cast hi
  have hjS : ((indices r).2 : ℚ) + 1 ≤ 512 := by exact_mod_cast hj
  have hi0 : (0 : ℚ) ≤ (indices r).1 := by positivity
  have hj0R : (0 : ℚ) < (indices r).2 := by exact_mod_cast hj0
  have htl : h < tLower (indices r).1 := by
    norm_num [h, tLower, mu, d]
    linarith
  have htr : tUpper (indices r).1 ≤ d := by
    norm_num [tUpper, mu, d]
    linarith
  have htu : tLower (indices r).1 < tUpper (indices r).1 := by
    norm_num [tLower, tUpper, mu, d]
    linarith
  have hul : a < uLower (indices r).2 := by
    norm_num [uLower, a, h]
    linarith
  have hur : uUpper (indices r).2 ≤ h := by
    norm_num [uUpper, a, h]
    linarith
  have huu : uLower (indices r).2 < uUpper (indices r).2 := by
    norm_num [uLower, uUpper, a, h]
    linarith
  have hcut : a < 3 * (1 - tUpper (indices r).1 - uUpper (indices r).2) / 13 := by
    norm_num [a, d, h] at *
    linarith
  have hZ1 : cutoff r ≤ uLower (indices r).2 := min_le_left _ _
  have hZ2 : cutoff r ≤ 3 * (1 - tUpper (indices r).1 - uUpper (indices r).2) / 13 :=
    min_le_right _ _
  exact ⟨lt_min hul hcut, hZ1, huu, hur, htl, htu, htr, by linarith⟩

/-- Every point in every adopted E0 or E1 fibre obeys the exact ordering
and the adopted 7/3 Buchstab-argument cutoff. -/
theorem row_fibre_argument (r : Row) {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    (a : ℝ) < w ∧ w < z ∧ z < u ∧ u < (h : ℝ) ∧
      (h : ℝ) < t ∧ t < (d : ℝ) ∧
      (7 / 3 : ℝ) ≤ (1 - t - u - z - w) / z := by
  obtain ⟨_, hzul, _, hurh, hhtl, _, htrd, hcut⟩ := row_endpoint_bounds r
  rcases hs with ⟨htl, htr, hul, hur, hw, hwz, hz⟩
  have haR : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hzulR : (cutoff r : ℝ) ≤ (uLower (indices r).2 : ℝ) := by exact_mod_cast hzul
  have hurhR : (uUpper (indices r).2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hurh
  have hhtlR : (h : ℝ) < (tLower (indices r).1 : ℝ) := by exact_mod_cast hhtl
  have htrdR : (tUpper (indices r).1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast htrd
  have hcutR : (13 / 3 : ℝ) * (cutoff r : ℝ) ≤
      1 - (tUpper (indices r).1 : ℝ) - (uUpper (indices r).2 : ℝ) := by
    have hc : ((((13 / 3 : ℚ) * cutoff r) : ℚ) : ℝ) ≤
        ((1 - tUpper (indices r).1 - uUpper (indices r).2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hcut
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one] using hc
  have hzpos : 0 < z := haR.trans (hw.trans hwz)
  refine ⟨hw, hwz, (hz.trans_le hzulR).trans hul, hur.trans_le hurhR,
    hhtlR.trans htl, htr.trans_le htrdR, ?_⟩
  apply (le_div_iff₀ hzpos).2
  linarith

theorem row_fibre_nonempty (r : Row) :
    ∃ t u z w : ℝ,
      openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w := by
  obtain ⟨haZ, _, huu, _, _, htu, _, _⟩ := row_endpoint_bounds r
  have haZR : (a : ℝ) < (cutoff r : ℝ) := by exact_mod_cast haZ
  have huuR : (uLower (indices r).2 : ℝ) < (uUpper (indices r).2 : ℝ) := by exact_mod_cast huu
  have htuR : (tLower (indices r).1 : ℝ) < (tUpper (indices r).1 : ℝ) := by exact_mod_cast htu
  refine ⟨((tLower (indices r).1 : ℝ) + (tUpper (indices r).1 : ℝ)) / 2,
    ((uLower (indices r).2 : ℝ) + (uUpper (indices r).2 : ℝ)) / 2,
    ((a : ℝ) + (cutoff r : ℝ)) / 2,
    (3 * (a : ℝ) + (cutoff r : ℝ)) / 4, ?_⟩
  dsimp only [openFibreSupport]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end ImbalancedChen.Certificates.PairedV2.FullMask
