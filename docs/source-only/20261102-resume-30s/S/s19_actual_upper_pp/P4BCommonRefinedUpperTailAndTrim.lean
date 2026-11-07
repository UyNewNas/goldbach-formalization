import ImbalancedChen.P5ActualCommonRefinedRange
import ImbalancedChen.P4BOriginalUpperFourierTailPaid
import ImbalancedChen.P4BActualUpperTrimPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independently specified original common-refined policy already has
a proved .599 active support range.  Apply it to K's EXISTING whole-source
Fourier tail and the actual upper trim.  There is no new support estimate,
Fourier-tail reconstruction or generic final PP consumer here.

OriginalData is the existing structural constructor, not a field carrying
PP or density.  Its identification with the final full87 buffered policy
has NOT been proved by this file and is not inferred from the range bound.
-/
namespace ImbalancedChen.P4BCommonRefinedUpperTailAndTrim
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness P4BArbitraryWidthUpperPairProfile
open P4BArbitraryWidthUpperBlockGeometry P4BArbitraryWidthUpperPostModulusTail
open P4BOriginalUpperFourierTailPaid P4BActualUpperTrimPayment
open P5Z.ActualCommonRefinedRange P5Z.CompleteProductTailDivisorBudgets
open P5Z.OriginalPrimeAllGroupHBDiscrepancy

abbrev commonRetain (d : P5OriginalCommonRefinedConstructor.OriginalData) :
    ℕ → List ℕ → Bool :=
  fun N => P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ) false

/-- The physical coefficient is literally the existing policy8 coefficient;
the finite enumeration cap remains arbitrary and does not replace q. -/
theorem common_supported (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (he : 0 ≤ d.e) (N : ℕ) (r epsilon : ℝ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (hepsilon : epsilon ≤ 1/1000) :
    Supported 1 r epsilon (commonRetain d) cap N
      (Nat.floor ((N : ℝ)^(599/1000 : ℝ))) := by
  intro q hq hactive
  exact (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr
    (actualAttachedCoefficient_lt_inflatedTheta d he N r epsilon cap hN
      hepsilon hactive).le

theorem common_natural_cap_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ Nat.floor ((N : ℝ)^(599/1000 : ℝ)) ∧
      (Nat.floor ((N : ℝ)^(599/1000 : ℝ)) : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) := by
  have hp : (1 : ℝ) ≤ (N : ℝ)^(599/1000 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  exact ⟨(Nat.le_floor_iff (zero_le_one.trans hp)).mpr (by simpa using hp),
    Nat.floor_le (zero_le_one.trans hp)⟩

/-- Actual use of the existing full two-group Fourier-tail theorem.  The
polynomial active-support premise is discharged for this independently
specified concrete policy.  Width loss and all original reserves remain
displayed exactly as in K; no retained-mode estimate is inferred. -/
theorem exists_common_original_upper_fourier_tail_paid :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b kappa r : ℝ,
      ∀ hb : 0 < b, b ≤ 1 → 0 < kappa → ∀ hr : 0 < r,
      ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa-r,
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (K accuracy : ℕ) (kappa0 epsilon : ℝ) (cap : ℕ → ℕ),
      epsilon ≤ 1/1000 →
      ‖(Part3.primeProductSignedError 2 N N
          (attachedUpperModuli 1 r epsilon (commonRetain d) cap N)
          (attachedUpperCoefficient 1 r epsilon (commonRetain d) cap N)
          (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width) : ℂ) -
        retainedUpperAtlas hb (by norm_num : (0 : ℝ) < 1) hr hw
          (by simpa only [one_mul] using hgap) N K kappa0 epsilon
          (commonRetain d) cap accuracy‖ ≤
        (C/width^24)*(N : ℝ)/logScale (countingScale N)^(accuracy+3) := by
  obtain ⟨C, hC, htail⟩ := exists_eventual_original_upper_fourier_tail_paid
    (599/1000 : ℝ) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro b kappa r hb hbOne hkappa hr
  filter_upwards [htail b kappa 1 r hb hbOne hkappa (by norm_num) hr,
    eventually_ge_atTop (2 : ℕ)] with N htailN hN
  intro width hw hgap d he K accuracy kappa0 epsilon cap hepsilon
  have hD := common_natural_cap_bounds (show 1 ≤ N by omega)
  exact htailN width hw (by simpa only [one_mul] using hgap) K
    (Nat.floor ((N : ℝ)^(599/1000 : ℝ))) accuracy kappa0 epsilon
    (commonRetain d) cap hD.1 hD.2
    (common_supported d he N r epsilon cap hN hepsilon)

/-- The new actual trim estimate is fully supplied on the same concrete
common-refined coefficient, with no active-cap hypothesis left.  The
threshold precedes all original row data and all legal fixed widths. -/
theorem eventually_common_original_upper_trim_paid
    (kappa0 : ℝ) (hkappa0 : 0 < kappa0) (hkappa01 : kappa0 < 1)
    (A : ℕ) (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, ∀ b kappa r width : ℝ,
      ∀ hb : 0 < b, ∀ hr : 0 < r, ∀ hw : 0 < width,
      ∀ hgap : 2*width ≤ baseline b kappa-r,
      ∀ (d : P5OriginalCommonRefinedConstructor.OriginalData), 0 ≤ d.e →
      ∀ (epsilon : ℝ) (cap : ℕ → ℕ), epsilon ≤ 1/1000 →
      ‖trimReserve (licence hb (by norm_num : (0 : ℝ) < 1) hr hw
          (by simpa only [one_mul] using hgap) N) N N kappa0
          (attachedUpperModuli 1 r epsilon (commonRetain d) cap N)
          (fun q => (attachedUpperCoefficient 1 r epsilon (commonRetain d) cap N q : ℂ))‖ ≤
        tolerance*(N : ℝ)/Real.log (N : ℝ)^A := by
  filter_upwards [eventually_actual_upper_trim_logAccuracy kappa0 hkappa0 hkappa01
    (599/1000 : ℝ) (by norm_num) A tolerance htolerance,
    eventually_ge_atTop (2 : ℕ)] with N htrim hN
  intro b kappa r width hb hr hw hgap d he epsilon cap hepsilon
  exact htrim b kappa 1 r width hb (by norm_num) hr hw
    (by simpa only [one_mul] using hgap) epsilon (commonRetain d) cap
    (actualActiveCap_le_inflatedTheta d he N r epsilon cap hN hepsilon)

end
end ImbalancedChen.P4BCommonRefinedUpperTailAndTrim
