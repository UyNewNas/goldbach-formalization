import ImbalancedChen.P3HBUnsplitChildSliceSmooth
import ImbalancedChen.P3HBExplicitSmoothCutoffs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

/-!
P3.6, manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion sections 2 and 4 (F).

The literal six-slot UNSPLIT geometric HB source was previously represented
as a complex function, while the actual Point/Fourier chart takes real weights.
Here the same fixed chosen nonnegative real C-infinity dyadic partition and
complete-product trim give an explicitly real weight. We prove literal
complex-of-real identification and a pointwise [0,1] amplitude bound.

All original group occurrences, incidences, independent positive scales and
ONE complete-product trim are retained. No analytic derivative/Fourier
integrability or PP discrepancy assumption enters these statements.
The complex ordered-derivative vs real ordered-derivative bridge and complete
physical W_T/U5 source admission are still open.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitRealProfile
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.P3HBExplicitSmoothCutoffs
open ImbalancedChen.P3HBNonnegativeDyadicContraction
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBOriginalGroupProductFirstDerivative
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBRestoredSixCoordinateD
open ImbalancedChen.P3HBUnsplitDirectRestoration

/-- An ORIGINAL group occurrence, using the chosen real dyadic cutoff. -/
def realGroupFactor (c : ℝ) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) : ℝ :=
  let z := c * Real.exp (originalGroupSum J u)
  chosenRealChi z - chosenRealChi (2 * z)

/-- An ORIGINAL positional HB dyadic factor, without a new indicator. -/
def realSlotFactor (i : Fin 6) (u : Fin 6 → ℝ) : ℝ :=
  let z := Real.exp (u i)
  chosenRealChi z - chosenRealChi (2 * z)

/-- The SAME single complete physical-product trim, as a real function. -/
def realFullTrim (s : ℝ) (u : Fin 6 → ℝ) : ℝ :=
  chosenRealEta (s * Real.exp (originalGroupSum Finset.univ u))

/-- The genuine unsplit six-position profile on the real Point 6 chart.
No source label or occurrence is cancelled in this expression. -/
def realSixUnsplitWeight {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (u : Fin 6 → ℝ) : ℝ :=
  (∏ j : Fin g, realGroupFactor (c j) (J j) u) *
    realFullTrim s u *
    (∏ i : Fin 6, realSlotFactor i u)

/-- Literal dyadic group factors are real, with no imaginary phase. -/
theorem groupFactor_ofReal (c : ℝ) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) :
    originalGroupDyadicFactor chosenChi c J u =
      (realGroupFactor c J u : ℂ) := by
  unfold originalGroupDyadicFactor groupDyadicLogProfile realGroupFactor
  dsimp
  rw [chosenChi_real, chosenChi_real]
  push_cast
  rfl

/-- The chosen physical trim is exactly the real trim embedded in C. -/
theorem fullTrim_ofReal (s : ℝ) (u : Fin 6 → ℝ) :
    physicalTrim chosenEta s u = (realFullTrim s u : ℂ) := by
  unfold physicalTrim realFullTrim
  exact chosenEta_real _

/-- The six original positional pieces, before the 729 signed
refinement, form an exact real-valued tensor. -/
theorem sixTensor_ofReal (u : Fin 6 → ℝ) :
    unsplitSixLogTensor chosenChi u =
      ((∏ i : Fin 6, realSlotFactor i u) : ℂ) := by
  unfold unsplitSixLogTensor
  have hterm (i : Fin 6) :
      iteratedDeriv 0
        (fun v : ℝ => chosenChi (Real.exp v) -
          chosenChi (2 * Real.exp v)) (u i) =
      (realSlotFactor i u : ℂ) := by
    simp only [iteratedDeriv_zero]
    unfold realSlotFactor
    dsimp
    rw [chosenChi_real, chosenChi_real]
    push_cast
    rfl
  calc
    (∏ i : Fin 6, iteratedDeriv 0
      (fun v : ℝ => chosenChi (Real.exp v) -
        chosenChi (2 * Real.exp v)) (u i)) =
        ∏ i : Fin 6, (realSlotFactor i u : ℂ) := by
          apply Finset.prod_congr rfl
          intro i _
          exact hterm i
    _ = ((∏ i : Fin 6, realSlotFactor i u) : ℂ) := by
      norm_cast

/-- Crucial coefficient-domain bridge: the previously constructed literal
complex original W is EXACTLY the complex embedding of this real W.
The original six positions and complete physical scale s are unchanged. -/
theorem unsplit_chosen_ofReal {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    originalSixUnsplitWeight chosenChi chosenEta c J s u =
      (realSixUnsplitWeight c J s u : ℂ) := by
  have hgroups :
      originalGroupProduct chosenChi c J u =
        ((∏ j : Fin g, realGroupFactor (c j) (J j) u) : ℂ) := by
    unfold originalGroupProduct
    calc
      (∏ j : Fin g, originalGroupDyadicFactor chosenChi
        (c j) (J j) u) =
          ∏ j : Fin g, (realGroupFactor (c j) (J j) u : ℂ) := by
            apply Finset.prod_congr rfl
            intro j _
            exact groupFactor_ofReal (c j) (J j) u
      _ = ((∏ j : Fin g, realGroupFactor (c j) (J j) u) : ℂ) := by
        norm_cast
  unfold originalSixUnsplitWeight originalGroupPhysicalTrim
  rw [hgroups, fullTrim_ofReal s u, sixTensor_ofReal u]
  unfold realSixUnsplitWeight
  push_cast
  rfl

/-- Every original group dyadic factor is in [0,1], uniformly in its
physical scale. -/
theorem realGroupFactor_between (c : ℝ)
    (J : Finset (Fin 6)) (u : Fin 6 → ℝ) :
    0 ≤ realGroupFactor c J u ∧ realGroupFactor c J u ≤ 1 := by
  change 0 ≤ chosenRealChi
        (c * Real.exp (originalGroupSum J u)) -
        chosenRealChi (2 * (c * Real.exp (originalGroupSum J u))) ∧
      chosenRealChi (c * Real.exp (originalGroupSum J u)) -
        chosenRealChi (2 * (c * Real.exp (originalGroupSum J u))) ≤ 1
  exact chosenRealChi_dyadic_between _

theorem realSlotFactor_between (i : Fin 6) (u : Fin 6 → ℝ) :
    0 ≤ realSlotFactor i u ∧ realSlotFactor i u ≤ 1 := by
  change 0 ≤ chosenRealChi (Real.exp (u i)) -
        chosenRealChi (2 * Real.exp (u i)) ∧
      chosenRealChi (Real.exp (u i)) -
        chosenRealChi (2 * Real.exp (u i)) ≤ 1
  exact chosenRealChi_dyadic_between _

theorem realFullTrim_between (s : ℝ) (u : Fin 6 → ℝ) :
    0 ≤ realFullTrim s u ∧ realFullTrim s u ≤ 1 := by
  unfold realFullTrim chosenRealEta
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- All multiplicities remain literal, but the chosen geometric
amplitude is bounded independently of their NUMBER (not just scales).
This pointwise fact is not an integrated derivative bound. -/
theorem realSixUnsplitWeight_between {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    0 ≤ realSixUnsplitWeight c J s u ∧
      realSixUnsplitWeight c J s u ≤ 1 := by
  let G : ℝ := ∏ j : Fin g, realGroupFactor (c j) (J j) u
  let H : ℝ := ∏ i : Fin 6, realSlotFactor i u
  let B : ℝ := realFullTrim s u
  have hG0 : 0 ≤ G := Finset.prod_nonneg (fun j _ =>
    (realGroupFactor_between (c j) (J j) u).1)
  have hG1 : G ≤ 1 := Finset.prod_le_one
    (fun j _ => (realGroupFactor_between (c j) (J j) u).1)
    (fun j _ => (realGroupFactor_between (c j) (J j) u).2)
  have hH0 : 0 ≤ H := Finset.prod_nonneg (fun i _ =>
    (realSlotFactor_between i u).1)
  have hH1 : H ≤ 1 := Finset.prod_le_one
    (fun i _ => (realSlotFactor_between i u).1)
    (fun i _ => (realSlotFactor_between i u).2)
  obtain ⟨hB0, hB1⟩ := realFullTrim_between s u
  have hGB0 : 0 ≤ G * B := mul_nonneg hG0 hB0
  have hGB1 : G * B ≤ 1 := by
    calc
      G * B ≤ (1 : ℝ) * 1 :=
        mul_le_mul hG1 hB1 hB0 (by norm_num)
      _ = 1 := by ring
  change 0 ≤ (G * B) * H ∧ (G * B) * H ≤ 1
  refine ⟨mul_nonneg hGB0 hH0, ?_⟩
  calc
    (G * B) * H ≤ (1 : ℝ) * 1 :=
      mul_le_mul hGB1 hH1 hH0 (by norm_num)
    _ = 1 := by ring

/-- In particular, no imaginary-valued geometric phase can slip into
the real Fourier W coefficient from the chosen dyadic chart. -/
theorem chosen_unsplit_im_zero {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    (originalSixUnsplitWeight chosenChi chosenEta c J s u).im = 0 := by
  rw [unsplit_chosen_ofReal]
  simp


/-- Pointwise the actual chosen original geometric coefficient has the
same real value as the explicit real Point 6 function. -/
theorem chosen_unsplit_re_eq_real {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    (originalSixUnsplitWeight chosenChi chosenEta c J s u).re =
      realSixUnsplitWeight c J s u := by
  rw [unsplit_chosen_ofReal]
  simp

/-- The original selected complex amplitude is bounded by one without
any g-dependent factor, directly from the REAL nonnegative dyadic split.
No derivative or integrated bound is inferred from this pointwise fact. -/
theorem chosen_unsplit_norm_le_one {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    ‖originalSixUnsplitWeight chosenChi chosenEta c J s u‖ ≤ 1 := by
  rw [unsplit_chosen_ofReal]
  obtain ⟨h0, h1⟩ := realSixUnsplitWeight_between c J s u
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using h1

end
end ImbalancedChen.P3HBUnsplitRealProfile
