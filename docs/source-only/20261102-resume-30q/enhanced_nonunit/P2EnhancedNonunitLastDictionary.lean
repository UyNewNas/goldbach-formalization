import ImbalancedChen.P2EnhancedNonunitMarkedMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact identification of the two high-word nonunit integrals with native
K20/K21. The already supplied unit20/unit21 masses are separate and are
not folded into either nonunit integral or into a full-dimensional face.
-/

namespace ImbalancedChen.P2EnhancedNonunitLastDictionary
noncomputable section
open Real Finset Set MeasureTheory Wu2008DoubleSieve
open P2SeedOmegaLiteralFibre (a2 a3 b)
open P2EnhancedNonunitPhysicalQuadrature P2EnhancedNonunitLabelGeometry
open P2EnhancedNonunitWordMass P2EnhancedNonunitMarkedMass
open P2EnhancedSwitchedTrueNormalization
open scoped Classical BigOperators

theorem last20_rows (t : Fin 5 → ℝ) :
    (∀ q, (∑ i, rows 4 q i * t i) ≤ wordIntercept 4 [2,3,3,3,3] q) ↔
      (∀ q, (∑ i, HighNonunitLegal.C20 q i * t i) ≤
        HighNonunitLegal.gamma20 a2 a3 b q) := by
  rw [rows_iff, ← Fin.monotone_iff_le_succ]
  simp only [HighNonunitLegal.C20, HighNonunitLegal.gamma20, HighNonunitLegal.affine_iff]
  constructor
  · rintro ⟨hm, hb⟩
    have h0 := hb 0
    have h1 := hb 1
    have h4 := hb 4
    norm_num [bandLo, bandHi] at h0 h1 h4
    exact ⟨h0.1, h0.2, h1.1, hm, h4.2⟩
  · rintro ⟨h0, h0u, h1, hm, h4⟩
    refine ⟨hm, ?_⟩
    intro i
    fin_cases i
    · simpa [bandLo, bandHi] using And.intro h0 h0u
    · simpa [bandLo, bandHi] using And.intro h1 ((hm (by decide : (1 : Fin 5) ≤ 4)).trans h4)
    · simpa [bandLo, bandHi] using And.intro
        (h1.trans (hm (by decide : (1 : Fin 5) ≤ 2))) ((hm (by decide : (2 : Fin 5) ≤ 4)).trans h4)
    · simpa [bandLo, bandHi] using And.intro
        (h1.trans (hm (by decide : (1 : Fin 5) ≤ 3))) ((hm (by decide : (3 : Fin 5) ≤ 4)).trans h4)
    · simpa [bandLo, bandHi] using And.intro
        (h1.trans (hm (by decide : (1 : Fin 5) ≤ 4))) h4

theorem last21_rows (t : Fin 6 → ℝ) :
    (∀ q, (∑ i, rows 5 q i * t i) ≤ wordIntercept 5 [3,3,3,3,3,3] q) ↔
      (∀ q, (∑ i, HighNonunitLegal.C21 q i * t i) ≤
        HighNonunitLegal.gamma21 a3 b q) := by
  rw [rows_iff, ← Fin.monotone_iff_le_succ]
  simp only [HighNonunitLegal.C21, HighNonunitLegal.gamma21, HighNonunitLegal.affine_iff]
  constructor
  · rintro ⟨hm, hb⟩
    have h0 := hb 0
    have h1 := hb 1
    have h5 := hb 5
    norm_num [bandLo, bandHi] at h0 h1 h5
    exact ⟨h0.1, h0.2, h1.1, hm, h5.2⟩
  · rintro ⟨h0, _, _, hm, h5⟩
    refine ⟨hm, ?_⟩
    intro i
    have hlo := h0.trans (hm (Fin.zero_le i))
    have hhi := (hm (Fin.le_last i)).trans h5
    fin_cases i <;> simpa [bandLo, bandHi] using And.intro hlo hhi

/-- Native full-dimensional nonunit kernels, at the unchanged alpha.
The identifications are exact, not envelope inequalities. -/
theorem nonunitIntegral20_eq_K20 (alpha : ℝ) :
    nonunitIntegral [2,3,3,3,3] alpha = HighNonunitLegal.K20 a2 a3 b alpha := by
  rw [HighNonunitLegal.K20_closed_mask_literal (by norm_num [a2]) (by norm_num [b])]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  have he := last20_rows t
  change (if _ then HighNonunitLegal.G 3 alpha t else 0)*continuousDensity t = _
  simp only [he]

theorem nonunitIntegral21_eq_K21 (alpha : ℝ) :
    nonunitIntegral [3,3,3,3,3,3] alpha = HighNonunitLegal.K21 a3 b alpha := by
  rw [HighNonunitLegal.K21_closed_mask_literal (by norm_num [a3]) (by norm_num [b])]
  unfold nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  have he := last21_rows t
  change (if _ then HighNonunitLegal.G 4 alpha t else 0)*continuousDensity t = _
  simp only [he]

end
end ImbalancedChen.P2EnhancedNonunitLastDictionary
