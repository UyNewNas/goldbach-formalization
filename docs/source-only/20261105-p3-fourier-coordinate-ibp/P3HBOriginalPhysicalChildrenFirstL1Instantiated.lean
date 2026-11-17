import ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
import ImbalancedChen.P3HBOriginalGroupTrimPointwiseBudget
import Mathlib.Tactic

/-!
P3.6, pinned 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2,4(F): instantiate the actual physical
M0/M1 envelope in the FIRST six-coordinate, 729-positional-child L1
estimate. These are not free geometric derivative constants anymore.

The physical group occurrences, their separate positive dyadic scales,
and the single complete-product trim retain their literal definitions.
The constants Cchi, Ceta are selected BEFORE g, c, J, s, orders, i and u.
The remaining ordinary measurability premises on W and its actual first
coordinate derivative are explicit; they are NOT integrated or Fourier
error bounds and still need discharge from actual smooth geometry.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. No PP, Fourier, full U5,
HB-hat, 2S, arbitrary m(T)-uniform conclusion, or arithmetic input.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
-/

namespace ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1Instantiated
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBOriginalGroupTrimPointwiseBudget
open ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1
open ImbalancedChen.P3HBSmoothLogTensorRestoration

/-- The previous first-axis six-dimensional 729-child integral estimate,
with BOTH zeroth- and first-axis geometric envelopes derived from the
actual original grouped product times its ONE physical product trim.

The only remaining per-geometry hypotheses are measurability of the
literal weight and its literal coordinate derivative, not arbitrary
size envelopes, integrability, Fourier norms or a target PP error.
The common Cchi and Ceta are chosen once, before the original group
count and ALL physical scales. Explicit exponential-in-g dependence is
NOT promoted to a fixed polylogarithmic budget for growing g. -/
theorem physicalChildrenFirstMass_integrable_actual_bounds
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hchiSmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hchiLarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C) :
    ∃ Cchi Ceta : ℝ, 0 ≤ Cchi ∧ 1 ≤ Ceta ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)),
        (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (orders : Fin 6 → ℕ) (i : Fin 6),
          (∀ j, orders j + 1 ≤ K) →
          Measurable (originalGroupPhysicalTrim chi eta c J s) →
          Measurable
            (actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i) →
          Integrable (physicalChildrenFirstMass chi eta c J s orders i) ∧
          (∫ u : Fin 6 → ℝ,
              physicalChildrenFirstMass chi eta c J s orders i u) ≤
            ((2 * ((g : ℝ) + 1) + 1) *
              ((3 * Cchi) ^ g * Ceta)) *
              ((smoothChildren.card : ℝ) *
                ((2 * Real.log 2) * C) ^ 6) := by
  obtain ⟨Cchi, Ceta, hCchi, hCeta, hgeom⟩ :=
    originalGroupPhysicalTrim_ordered_uniform_finite_order
      chi eta hchi heta
      hchiSmall hchiLarge hetaSmall hetaLarge 1
  refine ⟨Cchi, Ceta, hCchi, hCeta, ?_⟩
  intro g c J hc s hs orders i hk hWmeas hDWmeas
  let A : ℝ := (3 * Cchi) ^ g * Ceta
  let M0 : ℝ := A
  let M1 : ℝ := (2 * ((g : ℝ) + 1)) * A
  have hCeta0 : (0 : ℝ) ≤ Ceta := (by norm_num : (0 : ℝ) ≤ 1).trans hCeta
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) hCchi) _) hCeta0
  have hM0 : 0 ≤ M0 := hA
  have hM1 : 0 ≤ M1 := by
    dsimp [M1]
    apply mul_nonneg
    · positivity
    · exact hA
  have hW0 (u : Fin 6 → ℝ) :
      ‖originalGroupPhysicalTrim chi eta c J s u‖ ≤ M0 := by
    let emptyAxes : Fin 0 → Fin 6 := Fin.elim0
    have h := hgeom g 0 c J hc s hs emptyAxes (by omega) u
    simpa [M0, A, emptyAxes, originalOrderedAxisDeriv] using h
  have hW1 (u : Fin 6 → ℝ) :
      ‖actualAxisDeriv (originalGroupPhysicalTrim chi eta c J s) i u‖ ≤ M1 := by
    let oneAxis : Fin 1 → Fin 6 := fun _ => i
    have h := hgeom g 1 c J hc s hs oneAxis (by omega) u
    simpa [M1, A, oneAxis, originalOrderedAxisDeriv] using h
  obtain ⟨hInt, hL1⟩ :=
    physicalChildrenFirstMass_integrable_and_L1_le
      chi eta hchi heta hchiSmall hchiLarge K C hC
      c J s orders i hk hWmeas hDWmeas
      M0 M1 hM0 hM1 hW0 hW1
  refine ⟨hInt, ?_⟩
  calc
    (∫ u : Fin 6 → ℝ,
        physicalChildrenFirstMass chi eta c J s orders i u) ≤
        (M1 + M0) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := hL1
    _ = ((2 * ((g : ℝ) + 1) + 1) *
          ((3 * Cchi) ^ g * Ceta)) *
          ((smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6) := by
      dsimp [M0, M1, A]
      ring

end
end ImbalancedChen.P3HBOriginalPhysicalChildrenFirstL1Instantiated
