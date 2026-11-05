import ImbalancedChen.P4AOriginalFull87PopulationVariation

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED.

Extract the two ACTUAL finite population factors from the same
changed-owner/ordinary-continuation variation. This is plain finite
linearity in the nonnegative majorizing test; it does NOT prove either
factor times its normalized variation tends to zero.

The full modulus and leaf-dependent plus/minus beta remain untouched.
-/

namespace ImbalancedChen.P4AOriginalFull87PopulationScaling
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87EighthPrimeMeanLedger
open P4AOriginalFull87ChangedFrontierBudget
open P4AOriginalFull87PopulationVariation

/-- Exact scalar homogeneity of the original beta-weighted positive leaf
envelope. A scalar is pulled out only AFTER the sign choice is made. -/
theorem absoluteAttached_scale (N cap : ℕ) (w L : ℝ)
    (H : ℕ → ℝ) (a : ℝ) (positive : Bool) (pre : List ℕ) :
    absoluteAttached N cap w L (fun d => a * H d) positive pre =
      a * absoluteAttached N cap w L H positive pre := by
  unfold absoluteAttached
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem absoluteSignedTest_scale {α : Type*}
    (R : Bool → List α → Bool) (h : α → ℝ)
    (V : Bool → List α → ℝ) (a : ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    absoluteSignedTest R h (fun b hist => a * V b hist)
      pre positive mass remaining =
      a * absoluteSignedTest R h V pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [absoluteSignedTest]
      ring
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [absoluteSignedTest, if_pos hr]
        rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]
        ring
      · simp only [absoluteSignedTest, if_neg hr, add_zero]
        exact ih pre positive mass

theorem continuationVariation_scale (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w L : ℝ) (H : ℕ → ℝ) (a : ℝ)
    (s : FirstExitDepthState ℕ) :
    continuationVariation R N cap w L (fun d => a * H d) s =
      a * continuationVariation R N cap w L H s := by
  have ht : absoluteAttached N cap w L (fun d => a * H d) =
      fun b hist => a * absoluteAttached N cap w L H b hist := by
    funext b hist
    exact absoluteAttached_scale N cap w L H a b hist
  unfold continuationVariation
  rw [ht]
  exact absoluteSignedTest_scale R (fun _ => 1)
    (absoluteAttached N cap w L H) a
    s.selectedPrefix s.remaining s.positive s.mass

private theorem sum_map_scale {α : Type*} (xs : List α) (f : α → ℝ)
    (a : ℝ) :
    (xs.map (fun x => a * f x)).sum = a * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- A handy name for the sum of the two REAL ordinary variations on one
state. No additional owner is introduced. -/
private def pairVariation
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (H : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  continuationVariation
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    N cap w L H s +
  continuationVariation
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    N cap w L H s

private theorem pairVariation_scale
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (H : ℕ → ℝ) (a : ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ) :
    pairVariation n e q om N cap w L (fun d => a * H d) c s =
      a * pairVariation n e q om N cap w L H c s := by
  unfold pairVariation
  rw [continuationVariation_scale, continuationVariation_scale]
  ring

/-- The N-dependent prime population factors out through EVERY genuine
changed original87 occurrence. No extra multiplicity factor is added. -/
theorem changedVariationBudget_scale
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (H : ℕ → ℝ) (a : ℝ) :
    changedVariationBudget delta n e q om N cap w z L
        (fun d => a * H d) =
      a * changedVariationBudget delta n e q om N cap w z L H := by
  unfold changedVariationBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  let xs := changedStates delta n e q om N cap w z c
  change (xs.map (pairVariation n e q om N cap w L
    (fun d => a * H d) c)).sum =
    a * (xs.map (pairVariation n e q om N cap w L H c)).sum
  calc
    (xs.map (pairVariation n e q om N cap w L
      (fun d => a * H d) c)).sum =
      (xs.map (fun s => a * pairVariation n e q om N cap w L H c s)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro s _
        exact pairVariation_scale n e q om N cap w L H a c s
    _ = a * (xs.map (pairVariation n e q om N cap w L H c)).sum :=
      sum_map_scale xs (pairVariation n e q om N cap w L H c) a

theorem changedVariationBudget_const
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (a : ℝ) :
    changedVariationBudget delta n e q om N cap w z L (fun _ => a) =
      a * changedVariationBudget delta n e q om N cap w z L (fun _ => 1) := by
  have hf : (fun _ : ℕ => a) = (fun d : ℕ => a * (1 : ℝ)) := by
    funext d
    ring
  rw [hf]
  exact changedVariationBudget_scale delta n e q om N cap w z L
    (fun _ => 1) a

/-- Population factors are now explicit, not hidden inside the test:
the primitive discrepancy remains the EXACT same full-modulus signed
source. This is still only a finite inequality; the two reserve payments
require independent uniform asymptotic estimates on the displayed terms. -/
theorem receiver_density_factored_population_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
      primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      changedAbsBudget delta n e q om N cap w z L (primitiveError N) +
      primeMass N * changedVariationBudget delta n e q om N cap w z L densityTest +
      chenPrimeDivisorCount N N *
        changedVariationBudget delta n e q om N cap w z L (fun _ => 1) := by
  have h := receiver_density_changed_population_bound
    delta n e q om N cap w z L
  have hmod := changedVariationBudget_scale
    delta n e q om N cap w z L densityTest (primeMass N)
  have hcent := changedVariationBudget_const
    delta n e q om N cap w z L (chenPrimeDivisorCount N N)
  rw [hmod, hcent] at h
  exact h

end
end ImbalancedChen.P4AOriginalFull87PopulationScaling
