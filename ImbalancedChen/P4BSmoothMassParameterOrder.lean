import ImbalancedChen.P4BPhysicalBoundaryQuantifiers

/-!
# Parameter order and compact endpoint control for the actual smooth mass

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Only the badness gate varies with b. On positive prime tuples its margin,
the smooth weight, and the normalized mass are antitone. The final result
uses the proved mass precision at TWO fixed endpoints to control every
intermediate b, at one width and one threshold. The explicit endpoint
coefficient oscillation is retained; no uniform PNT is assumed.
-/

namespace ImbalancedChen.P4B

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry

theorem physicalPairMargins_antitone_parameter
    {N : ℕ} {T : ℝ} (hN : (1 : ℝ) < N)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (i : Fin 4) : Antitone (fun b : ℝ => physicalPairMargins b N T t i) := by
  have hp : Nat.Prime (t 1).val := (Finset.mem_filter.mp ht).2 1
  have hq : (1 : ℝ) ≤ ((t 1).val : ℝ) := by
    exact_mod_cast (show 1 ≤ (t 1).val by have hh := hp.two_le; omega)
  have hy : 0 ≤ logPoint N t 1 :=
    div_nonneg (Real.log_nonneg hq) (Real.log_pos hN).le
  intro bLo bHi hb
  fin_cases i
  · exact le_rfl
  · rw [physicalPairMargins_eq_original_of_ne_upper bHi T N t
      (by decide : (1 : Fin 4) ≠ 3),
      physicalPairMargins_eq_original_of_ne_upper bLo T N t
        (by decide : (1 : Fin 4) ≠ 3)]
    change logPoint N t 0 - bHi * logPoint N t 1 ≤
      logPoint N t 0 - bLo * logPoint N t 1
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right hb hy) _
  · exact le_rfl
  · exact le_rfl

/-- Pointwise order for the literal four-factor smooth weight. -/
theorem smoothPhysicalPairOuterRamp_antitone_parameter
    {N : ℕ} {T width : ℝ} (hN : (1 : ℝ) < N) (hwidth : 0 < width)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    Antitone (fun b : ℝ => smoothPhysicalPairOuterRamp b N T width t) := by
  intro bLo bHi hb
  unfold smoothPhysicalPairOuterRamp
  apply Finset.prod_le_prod (fun i _ => (smoothGateUpperStep_bounds width _).1)
  intro i _hi
  exact monotone_smoothGateUpperStep hwidth
    (physicalPairMargins_antitone_parameter hN ht i hb)

/-- Literal smooth tuple mass on the unchanged original source scale. -/
def normalizedSmoothPhysicalMass (b kappa width : ℝ) (N : ℕ) : ℝ :=
  (∑ t ∈ labelledPrimeTuples 2 N,
    smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width t) /
      ((N : ℝ) / Real.log (N : ℝ))

theorem normalizedSmoothPhysicalMass_antitone_parameter
    {N : ℕ} {kappa width : ℝ} (hN : (1 : ℝ) < N) (hwidth : 0 < width) :
    Antitone (fun b : ℝ => normalizedSmoothPhysicalMass b kappa width N) := by
  intro bLo bHi hb
  unfold normalizedSmoothPhysicalMass
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum (fun t ht =>
      smoothPhysicalPairOuterRamp_antitone_parameter hN hwidth ht hb)
  · exact (div_pos (zero_lt_one.trans hN) (Real.log_pos hN)).le

theorem normalizedSmoothPhysicalMass_endpoint_sandwich
    {N : ℕ} {bLo b bHi kappa width : ℝ}
    (hN : (1 : ℝ) < N) (hwidth : 0 < width) (hLo : bLo ≤ b) (hHi : b ≤ bHi) :
    normalizedSmoothPhysicalMass bHi kappa width N ≤
        normalizedSmoothPhysicalMass b kappa width N ∧
      normalizedSmoothPhysicalMass b kappa width N ≤
        normalizedSmoothPhysicalMass bLo kappa width N :=
  ⟨normalizedSmoothPhysicalMass_antitone_parameter hN hwidth hHi,
    normalizedSmoothPhysicalMass_antitone_parameter hN hwidth hLo⟩

/-- The exact source coefficient is antitone on positive b. -/
theorem smoothMass_logCoefficient_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (1 / b) ≤ Real.log (1 / a) := by
  have hb : 0 < b := ha.trans_le hab
  apply Real.log_le_log (one_div_pos.mpr hb)
  exact (div_le_div_iff₀ hb ha).mpr (by simpa only [one_mul] using hab)

/-- Compact interval endpoint control from two fixed-parameter limits.
One common positive width cap and threshold cover every intermediate b
and every smaller positive width. The endpoint coefficient oscillation
is displayed explicitly, so this is not a disguised uniform PNT input. -/
theorem exists_compact_endpoint_smooth_mass_control
    {bLo bHi kappa : ℝ} (hLoHalf : (1 / 2 : ℝ) < bLo)
    (horder : bLo ≤ bHi) (hHiOne : bHi < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (epsilon widthMax : ℝ) (hepsilon : 0 < epsilon) (hwidthMax : 0 < widthMax) :
    ∃ width0 : ℝ, 0 < width0 ∧ width0 ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ width : ℝ, 0 < width → width ≤ width0 →
        ∀ N : ℕ, N0 ≤ N → Even N → ∀ b : ℝ, bLo ≤ b → b ≤ bHi →
          |normalizedSmoothPhysicalMass b kappa width N - Real.log (1 / b)| <
            epsilon + (Real.log (1 / bLo) - Real.log (1 / bHi)) := by
  obtain ⟨widthLo, hwidthLo, hmaxLo, NLo, hNLo, hmassLo⟩ :=
    exists_uniform_smooth_physical_mass_precision hLoHalf (horder.trans_lt hHiOne)
      hkappa hkappaOne epsilon widthMax hepsilon hwidthMax
  obtain ⟨widthHi, hwidthHi, _hmaxHi, NHi, hNHi, hmassHi⟩ :=
    exists_uniform_smooth_physical_mass_precision (hLoHalf.trans_le horder) hHiOne
      hkappa hkappaOne epsilon widthMax hepsilon hwidthMax
  let width0 := min widthLo widthHi
  let N0 := max NLo NHi
  refine ⟨width0, lt_min hwidthLo hwidthHi,
    (min_le_left _ _).trans hmaxLo, N0, hNLo.trans (le_max_left _ _), ?_⟩
  intro width hwidth hwidth0 N hN hEven b hbLo hbHi
  have hwLo : width ≤ widthLo := hwidth0.trans (min_le_left _ _)
  have hwHi : width ≤ widthHi := hwidth0.trans (min_le_right _ _)
  have hNL : NLo ≤ N := (le_max_left NLo NHi).trans hN
  have hNH : NHi ≤ N := (le_max_right NLo NHi).trans hN
  have hN2 : 2 ≤ N := hNLo.trans hNL
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hmassL : |normalizedSmoothPhysicalMass bLo kappa width N -
      Real.log (1 / bLo)| < epsilon :=
    hmassLo width hwidth hwLo N hNL hEven
  have hmassH : |normalizedSmoothPhysicalMass bHi kappa width N -
      Real.log (1 / bHi)| < epsilon :=
    hmassHi width hwidth hwHi N hNH hEven
  have hsand := normalizedSmoothPhysicalMass_endpoint_sandwich hN1 hwidth hbLo hbHi
  have hbLoPos : 0 < bLo := by linarith only [hLoHalf]
  have hbPos : 0 < b := hbLoPos.trans_le hbLo
  have hcoeffLo := smoothMass_logCoefficient_le hbLoPos hbLo
  have hcoeffHi := smoothMass_logCoefficient_le hbPos hbHi
  obtain ⟨hLow, _⟩ := abs_lt.mp hmassH
  obtain ⟨_, hHigh⟩ := abs_lt.mp hmassL
  apply abs_lt.mpr
  constructor <;> linarith only [hsand.1, hsand.2, hcoeffLo, hcoeffHi, hLow, hHigh]

end
end ImbalancedChen.P4B
