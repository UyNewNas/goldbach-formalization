import ImbalancedChen.P5OriginalTaylorWeightDerivatives

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The complete signed weighted affine extension of the original Taylor
integrand, with its actual first and second coordinate derivatives.
The extension agrees with the original raw kernel on the closed box by
the already supplied BranchFacts theorem. It is the extension, not a
raw max continued across a branch seam, that is differentiated here.
-/
namespace ImbalancedChen.P5OriginalTaylorWeightedAxisCalculus
noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OldFifthPointwiseQ P5OldFifthFirstFConcavity
open P5OriginalTaylorActualSignedKernel P5OriginalTaylorAffineBranchBinding
open P5OriginalTaylorAffineRatioDerivatives P5OriginalTaylorWeightDerivatives

def axisDifference (new old : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  firstF (axisArgument new t i x) - firstF (axisArgument old t i x)

def axisDifferenceSlope (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) : ℝ :=
  firstSlope (axisArgument new t i x) * axisSlope new t i x -
    firstSlope (axisArgument old t i x) * axisSlope old t i x

def axisDifferenceCurvature (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) : ℝ :=
  (firstCurvature (axisArgument new t i x) * (axisSlope new t i x) ^ 2 +
    firstSlope (axisArgument new t i x) * axisCurvature new t i x) -
  (firstCurvature (axisArgument old t i x) * (axisSlope old t i x) ^ 2 +
    firstSlope (axisArgument old t i x) * axisCurvature old t i x)

def axisKernel (new old : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  axisWeight t i x * axisDifference new old t i x

def axisKernelSlope (new old : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  axisWeightSlope t i x * axisDifference new old t i x +
    axisWeight t i x * axisDifferenceSlope new old t i x

def axisKernelCurvature (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) : ℝ :=
  axisWeightCurvature t i x * axisDifference new old t i x +
    2 * axisWeightSlope t i x * axisDifferenceSlope new old t i x +
    axisWeight t i x * axisDifferenceCurvature new old t i x

theorem original_affine_kernel_on_axis (new old : Affine5)
    (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) :
    affineTaylorSignedKernel new old (Function.update t i x) =
      axisKernel new old t i x := by
  change originalTaylorWeight (Function.update t i x) *
      (firstF (affineArgument new (Function.update t i x)) -
        firstF (affineArgument old (Function.update t i x))) = _
  rw [original_weight_on_axis, original_argument_on_axis, original_argument_on_axis]
  rfl

theorem axisKernel_at_base (new old : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) :
    axisKernel new old t i (t i) = affineTaylorSignedKernel new old t := by
  simpa using (original_affine_kernel_on_axis new old t i (t i)).symm

theorem hasDerivAt_axisDifference (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    HasDerivAt (axisDifference new old t i) (axisDifferenceSlope new old t i x) x := by
  exact ((hasDerivAt_firstF hn).comp x
    (hasDerivAt_axisArgument new t i x h4 (fun _ => hx))).sub
      ((hasDerivAt_firstF ho).comp x
        (hasDerivAt_axisArgument old t i x h4 (fun _ => hx)))

theorem hasDerivAt_axisDifferenceSlope (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    HasDerivAt (axisDifferenceSlope new old t i)
      (axisDifferenceCurvature new old t i x) x := by
  have hnA := hasDerivAt_axisArgument new t i x h4 (fun _ => hx)
  have hoA := hasDerivAt_axisArgument old t i x h4 (fun _ => hx)
  have hnS := hasDerivAt_axisSlope new t i x h4 (fun _ => hx)
  have hoS := hasDerivAt_axisSlope old t i x h4 (fun _ => hx)
  have hd := (((hasDerivAt_firstSlope hn).comp x hnA).mul hnS).sub
    (((hasDerivAt_firstSlope ho).comp x hoA).mul hoS)
  convert hd using 1
  · rfl
  · dsimp [axisDifferenceCurvature]
    ring

/-- This derivative includes the derivative of the full reciprocal-prime weight. -/
theorem hasDerivAt_axisKernel (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    HasDerivAt (axisKernel new old t i) (axisKernelSlope new old t i x) x := by
  exact (hasDerivAt_axisWeight t i x h4 hx).mul
    (hasDerivAt_axisDifference new old t i x h4 hx hn ho)

/-- The literal product rule w'' d + 2 w' d' + w d''. -/
theorem hasDerivAt_axisKernelSlope (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    HasDerivAt (axisKernelSlope new old t i) (axisKernelCurvature new old t i x) x := by
  have hw := hasDerivAt_axisWeight t i x h4 hx
  have hw' := hasDerivAt_axisWeightSlope t i x h4 hx
  have hd := hasDerivAt_axisDifference new old t i x h4 hx hn ho
  have hd' := hasDerivAt_axisDifferenceSlope new old t i x h4 hx hn ho
  have hh := (hw'.mul hd).add (hw.mul hd')
  convert hh using 1
  · rfl
  · dsimp [axisKernelCurvature]
    ring

theorem continuousAt_firstCurvature {s : ℝ} (hs : 1 < s) :
    ContinuousAt firstCurvature s := by
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  have hid : ContinuousAt (fun y : ℝ => y) s := continuousAt_id
  have hm : ContinuousAt (fun y : ℝ => y - 1) s := hid.sub continuousAt_const
  have hlog := hm.log hs1
  exact ((((continuousAt_const.mul (hm.pow 2)).mul hlog).sub
    ((continuousAt_const.mul hid).mul hm)).sub (hid.pow 2)).div
      ((hid.pow 3).mul (hm.pow 2)) (mul_ne_zero (pow_ne_zero 3 hs0) (pow_ne_zero 2 hs1))

theorem continuousAt_axisCurvature (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0) :
    ContinuousAt (axisCurvature a t i) x := by
  by_cases hi : i = 4
  · have hc := (hasDerivAt_axisSlope a t i x h4 (fun _ => hx)).continuousAt
    have hconst : ContinuousAt (fun _ : ℝ => (-2 : ℝ)) x := continuousAt_const
    simpa only [axisCurvature, if_pos hi] using
      (hconst.mul hc).div continuousAt_id hx
  · simpa only [axisCurvature, if_neg hi] using
      (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)

theorem continuousAt_axisWeightCurvature (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0) :
    ContinuousAt (axisWeightCurvature t i) x := by
  exact (continuousAt_const.mul
    (hasDerivAt_axisWeight t i x h4 hx).continuousAt).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hx)

theorem continuousAt_axisDifferenceCurvature (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    ContinuousAt (axisDifferenceCurvature new old t i) x := by
  have hnA := (hasDerivAt_axisArgument new t i x h4 (fun _ => hx)).continuousAt
  have hoA := (hasDerivAt_axisArgument old t i x h4 (fun _ => hx)).continuousAt
  have hnS := (hasDerivAt_axisSlope new t i x h4 (fun _ => hx)).continuousAt
  have hoS := (hasDerivAt_axisSlope old t i x h4 (fun _ => hx)).continuousAt
  have hnC := (continuousAt_firstCurvature hn).comp x hnA
  have hoC := (continuousAt_firstCurvature ho).comp x hoA
  have hnF := (hasDerivAt_firstSlope hn).continuousAt.comp x hnA
  have hoF := (hasDerivAt_firstSlope ho).continuousAt.comp x hoA
  exact ((hnC.mul (hnS.pow 2)).add
    (hnF.mul (continuousAt_axisCurvature new t i x h4 hx))).sub
      ((hoC.mul (hoS.pow 2)).add
        (hoF.mul (continuousAt_axisCurvature old t i x h4 hx)))

theorem continuousAt_axisKernelCurvature (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : x ≠ 0)
    (hn : 1 < axisArgument new t i x) (ho : 1 < axisArgument old t i x) :
    ContinuousAt (axisKernelCurvature new old t i) x := by
  have hw := (hasDerivAt_axisWeight t i x h4 hx).continuousAt
  have hw' := (hasDerivAt_axisWeightSlope t i x h4 hx).continuousAt
  have hd := (hasDerivAt_axisDifference new old t i x h4 hx hn ho).continuousAt
  have hd' := (hasDerivAt_axisDifferenceSlope new old t i x h4 hx hn ho).continuousAt
  exact (((continuousAt_axisWeightCurvature t i x h4 hx).mul hd).add
    ((continuousAt_const.mul hw').mul hd')).add
      (hw.mul (continuousAt_axisDifferenceCurvature new old t i x h4 hx hn ho))

theorem continuousOn_axisKernelCurvature (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (l r : ℝ) (h4 : t 4 ≠ 0)
    (hrange : ∀ x ∈ Icc l r, x ≠ 0 ∧
      1 < axisArgument new t i x ∧ 1 < axisArgument old t i x) :
    ContinuousOn (axisKernelCurvature new old t i) (Icc l r) := by
  intro x hx
  exact (continuousAt_axisKernelCurvature new old t i x h4
    (hrange x hx).1 (hrange x hx).2.1 (hrange x hx).2.2).continuousWithinAt

theorem continuousAt_affineArgument (a : Affine5) (t : Fin 5 → ℝ) (ht : t 4 ≠ 0) :
    ContinuousAt (affineArgument a) t := by
  have heval : Continuous (fun u : Fin 5 → ℝ => a.eval u) := by
    unfold Affine5.eval
    fun_prop
  have hsum : Continuous (fun u : Fin 5 → ℝ => sum5 u) := by
    unfold sum5
    fun_prop
  exact (heval.continuousAt.sub hsum.continuousAt).div
    (continuous_apply 4).continuousAt ht

theorem continuousAt_originalTaylorWeight (t : Fin 5 → ℝ) (ht : ∀ i, 0 < t i) :
    ContinuousAt originalTaylorWeight t := by
  unfold originalTaylorWeight
  fun_prop (disch := exact (ht _).ne')

theorem continuousOn_affineTaylorSignedKernel (raw : FifthWireRow)
    (new old : Affine5) (hl : ∀ i, 0 < (raw.lower i : ℝ))
    (hrange : ∀ t ∈ rawClosedBox raw,
      1 < affineArgument new t ∧ 1 < affineArgument old t) :
    ContinuousOn (affineTaylorSignedKernel new old) (rawClosedBox raw) := by
  intro t ht
  have hp : ∀ i, 0 < t i := fun i => (hl i).trans_le (ht i).1
  have hnA := continuousAt_affineArgument new t (hp 4).ne'
  have hoA := continuousAt_affineArgument old t (hp 4).ne'
  have hnF := (hasDerivAt_firstF (hrange t ht).1).continuousAt.comp t hnA
  have hoF := (hasDerivAt_firstF (hrange t ht).2).continuousAt.comp t hoA
  exact ((continuousAt_originalTaylorWeight t hp).mul (hnF.sub hoF)).continuousWithinAt

theorem axisArgument_rebase (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x y : ℝ) :
    axisArgument a (Function.update t i x) i y = axisArgument a t i y := by
  rw [← original_argument_on_axis, Function.update_update, original_argument_on_axis]

theorem axisSlope_rebase (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x y : ℝ) :
    axisSlope a (Function.update t i x) i y = axisSlope a t i y := by
  by_cases hi : i = 4
  · simp only [axisSlope, if_pos hi, axisArgument_rebase]
  · simp [axisSlope, hi, Function.update, Ne.symm hi]

theorem axisCurvature_rebase (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x y : ℝ) :
    axisCurvature a (Function.update t i x) i y = axisCurvature a t i y := by
  simp only [axisCurvature, axisSlope_rebase]

theorem axisWeight_rebase (t : Fin 5 → ℝ) (i : Fin 5) (x y : ℝ) :
    axisWeight (Function.update t i x) i y = axisWeight t i y := by
  rw [← original_weight_on_axis, Function.update_update, original_weight_on_axis]

theorem axisKernelCurvature_rebase (new old : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x y : ℝ) :
    axisKernelCurvature new old (Function.update t i x) i y =
      axisKernelCurvature new old t i y := by
  simp only [axisKernelCurvature, axisDifference, axisDifferenceSlope,
    axisDifferenceCurvature, axisWeightSlope, axisWeightCurvature,
    axisArgument_rebase, axisSlope_rebase, axisCurvature_rebase, axisWeight_rebase]

end
end ImbalancedChen.P5OriginalTaylorWeightedAxisCalculus
