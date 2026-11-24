import ImbalancedChen.P5OriginalCommonRefinedSource
import ImbalancedChen.ActualFirstExitDensityProjection

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original common constructor is kept literally. The positive presieve
is applied to one complete policy, never to a difference of signed
densities. The exact projection loss is nonnegative. The actual beta
attachment error includes BOTH signs on this same retained support.

The existing proved absolute rough-mass/fundamental-lemma supplier chooses
one epsilon and one threshold before OriginalData and Stage. Thus no
desired common-density or beta-error estimate is an input hypothesis.
The outer compiler and its coefficient perturbation remain separate.
-/
namespace ImbalancedChen.P5OriginalCommonPositivePresieve
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P4AOriginalVariableFifthPhysicalLedger

def normalize (N : ℕ) (x : ℝ) : ℝ := x * Real.log (N : ℝ) / singularSeries N

theorem normalize_add (N : ℕ) (x y : ℝ) :
    normalize N (x + y) = normalize N x + normalize N y := by
  unfold normalize
  ring

theorem normalize_sub (N : ℕ) (x y : ℝ) :
    normalize N (x - y) = normalize N x - normalize N y := by
  unfold normalize
  ring

theorem normalize_mono (N : ℕ) (hN : 2 ≤ N) {x y : ℝ} (hxy : x ≤ y) :
    normalize N x ≤ normalize N y := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hxy (Real.log_pos hN1).le) (singularSeries_pos N).le

theorem normalize_reserve (N : ℕ) (hN : 2 ≤ N) (eta : ℝ) :
    normalize N (eta * singularSeries N / Real.log (N : ℝ)) = eta := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  unfold normalize
  field_simp [(Real.log_pos hN1).ne', (singularSeries_pos N).ne'] <;> ring

/-- This is the actual, signed beta error on the common stage's support. -/
def attachmentError (d : OriginalData) (s : Stage) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physical (stagePolicy d (N : ℝ) s) N cap w z L -
    actualSmallEulerProduct N cap w * raw (stagePolicy d (N : ℝ) s) N cap w z

/-- The unsigned negative mass is that of the SAME common stage. In
particular its beta width cannot be dropped or borrowed from the old tree. -/
theorem attachmentError_eq_signed (d : OriginalData) (s : Stage)
    (N cap : ℕ) (w z L : ℝ) :
    attachmentError d s N cap w z L =
      raw (stagePolicy d (N : ℝ) s) N cap w z *
          (smallPlus N cap w L - actualSmallEulerProduct N cap w) +
        negative (stagePolicy d (N : ℝ) s) N cap w z *
          (smallPlus N cap w L - smallMinus N cap w L) := by
  rw [attachmentError, physical_eq_signed_raw]
  ring

/-- This nonnegative loss is the actual full-policy presieve correction,
not the difference of two unrelated sieve bounds. -/
def projectionLoss (d : OriginalData) (s : Stage) (N cap : ℕ) (w z : ℝ) : ℝ :=
  raw (stagePolicy d (N : ℝ) s) N cap 0 z -
    actualSmallEulerProduct N cap w * raw (stagePolicy d (N : ℝ) s) N cap w z

theorem projectionLoss_nonneg (d : OriginalData) (s : Stage)
    (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) :
    0 ≤ projectionLoss d s N cap w z := by
  exact sub_nonneg.mpr (fixedRoughDensity_presieveProjection
    ((stagePolicy d (N : ℝ) s) false) N cap w z hwz)

theorem physical_eq_full_sub_projection_add_attachment (d : OriginalData) (s : Stage)
    (N cap : ℕ) (w z L : ℝ) :
    physical (stagePolicy d (N : ℝ) s) N cap w z L =
      raw (stagePolicy d (N : ℝ) s) N cap 0 z - projectionLoss d s N cap w z +
        attachmentError d s N cap w z L := by
  unfold projectionLoss attachmentError
  ring

theorem normalized_physical_le_full_add_attachment (d : OriginalData) (s : Stage)
    (N cap : ℕ) (hN : 2 ≤ N) (w z L : ℝ) (hwz : w ≤ z) :
    normalize N (physical (stagePolicy d (N : ℝ) s) N cap w z L) ≤
      normalize N (raw (stagePolicy d (N : ℝ) s) N cap 0 z) +
        normalize N (attachmentError d s N cap w z L) := by
  rw [← normalize_add]
  apply normalize_mono N hN
  rw [physical_eq_full_sub_projection_add_attachment]
  linarith [projectionLoss_nonneg d s N cap w z hwz]

/-- One actual beta choice works for every common stage and every original
finite input. Its error is PAID by the existing absolute-mass theorem.
There is no assumed error/mean bound and no equality of old/common policy. -/
theorem exists_common_positive_presieve_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (d : OriginalData) (s : Stage),
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            1 < w ∧ w ≤ z ∧
              0 ≤ attachmentError d s N cap w z L ∧
              normalize N (attachmentError d s N cap w z L) ≤ eta ∧
              normalize N (physical (stagePolicy d (N : ℝ) s) N cap w z L) ≤
                normalize N (raw (stagePolicy d (N : ℝ) s) N cap 0 z) + eta := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hsupply⟩ := exists_actualSmallRoughRho_density_error_le_target_reserve
    nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap d s
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hw : 1 < (N : ℝ) ^ (nu * epsilon ^ 2) :=
    Real.one_lt_rpow hN1 (mul_pos hnu (sq_pos_of_pos hepsilon))
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  have he := hsupply N hN hEven cap hcap ((stagePolicy d (N : ℝ) s) false)
  change 0 ≤ attachmentError d s N cap _ _ _ ∧
    attachmentError d s N cap _ _ _ ≤ eta * singularSeries N / Real.log (N : ℝ) at he
  have hen := normalize_mono N hN2 he.2
  rw [normalize_reserve N hN2 eta] at hen
  dsimp only
  refine ⟨hw, hwz, he.1, hen, ?_⟩
  exact (normalized_physical_le_full_add_attachment d s N cap hN2 _ _ _ hwz).trans
    (add_le_add_left hen _)

end
end ImbalancedChen.P5OriginalCommonPositivePresieve
