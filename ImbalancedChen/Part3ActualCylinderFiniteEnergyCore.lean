import ImbalancedChen.Part3CuspModeNativeClosedForm
import ImbalancedChen.Part3ActualZeroMeanCylinderFourierUnitary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite nonzero Fourier core of the WHOLE period-one cylinder.
The last two coordinates below are y*partial_y and y*partial_x, in the
literal L2(dx dy/y^2). Their representatives are proved from actual real
derivatives. The finite Dirichlet pairing is then computed from actual
circle orthogonality, not supplied as a form-isometry hypothesis.
-/

namespace ImbalancedChen.Part3.ActualCylinderFiniteEnergyCore20261026b
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
open CuspCylinderMeasure20261024z CuspCylinderBesselMode20261024z
open CuspModePhysicalCoreForm20261026a CuspModeNativeClosedForm20261026a
open RadialSchrodingerL2Form20261025a
open ActualCylinderModeEmbeddings20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)

abbrev ModeEnergy (n : NonzeroMode) :=
  physicalClosedEnergyDomain (frequencyScale n) (frequencyScale_pos n.property)

def modeCorePoint (n : NonzeroMode) (T : RadialTest) : ModeEnergy n :=
  physicalCoreEnergyPoint _ _ T

def horizontalPhase (n : ℤ) : ℂ :=
  if 0 ≤ (n : ℝ) then Complex.I else -Complex.I

theorem horizontalPhase_unit (n : ℤ) :
    star (horizontalPhase n) * horizontalPhase n = 1 := by
  unfold horizontalPhase
  split_ifs <;> simp [Complex.star_def]

theorem horizontalPhase_frequency (n : ℤ) :
    horizontalPhase n * (frequencyScale n : ℂ) =
      (2 * Real.pi * Complex.I * n : ℂ) := by
  unfold horizontalPhase frequencyScale
  split_ifs with h
  · rw [abs_of_nonneg h]
    push_cast
    ring
  · rw [abs_of_neg (lt_of_not_ge h)]
    push_cast
    ring

def modeValue (n : NonzeroMode) : ModeEnergy n →L[ℂ] HeightL2 :=
  physicalClosedEmbedding _ _

def modeVertical (n : NonzeroMode) : ModeEnergy n →L[ℂ] HeightL2 :=
  physicalClosedVertical _ _

def modeHorizontal (n : NonzeroMode) : ModeEnergy n →L[ℂ] HeightL2 :=
  horizontalPhase n • physicalClosedPotential _ _

theorem modeHorizontal_inner (n : NonzeroMode) (d e : ModeEnergy n) :
    inner ℂ (modeHorizontal n d) (modeHorizontal n e) =
      inner ℂ (physicalClosedPotential _ _ d) (physicalClosedPotential _ _ e) := by
  simp only [modeHorizontal, ContinuousLinearMap.smul_apply,
    inner_smul_left, inner_smul_right]
  rw [← mul_assoc, horizontalPhase_unit, one_mul]

abbrev CylinderEnergyHilbert := PiLp 2 (fun _ : Fin 3 => CylinderL2)

/-- Coordinates are (value, y*partial_y, y*partial_x), in that order. -/
def modeEnergyVector (n : NonzeroMode) (d : ModeEnergy n) : CylinderEnergyHilbert :=
  WithLp.toLp 2 ![modeEmbedding n (modeValue n d),
    modeEmbedding n (modeVertical n d), modeEmbedding n (modeHorizontal n d)]

theorem modeEnergyVector_inner (n m : NonzeroMode)
    (d : ModeEnergy n) (e : ModeEnergy m) :
    inner ℂ (modeEnergyVector n d) (modeEnergyVector m e) =
      (if n = m then (1 : ℂ) else 0) *
        (inner ℂ (modeValue n d) (modeValue m e) +
          inner ℂ (modeVertical n d) (modeVertical m e) +
          inner ℂ (modeHorizontal n d) (modeHorizontal m e)) := by
  rw [PiLp.inner_apply]
  simp only [modeEnergyVector, Fin.sum_univ_three, modeEmbedding_inner]
  have heq : ((n : ℤ) = (m : ℤ)) ↔ n = m := Subtype.val_injective.eq_iff
  simp only [heq]
  ring

theorem modeEnergyVector_inner_self_mode (n : NonzeroMode) (d e : ModeEnergy n) :
    inner ℂ (modeEnergyVector n d) (modeEnergyVector n e) = inner ℂ d e := by
  rw [modeEnergyVector_inner, if_pos rfl, one_mul, modeHorizontal_inner]
  change _ = inner ℂ (d : PhysicalEnergyHilbert) (e : PhysicalEnergyHilbert)
  rw [PiLp.inner_apply]
  simp [modeValue, modeVertical, physicalClosedEmbedding, physicalClosedVertical,
    physicalClosedPotential, Fin.sum_univ_three]

def finiteEnergyVector (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) :
    CylinderEnergyHilbert := ∑ n ∈ s, modeEnergyVector n (modeCorePoint n (T n))

def finiteValue (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) : CylinderL2 :=
  (finiteEnergyVector s T) 0

def finiteVertical (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) : CylinderL2 :=
  (finiteEnergyVector s T) 1

def finiteHorizontal (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) : CylinderL2 :=
  (finiteEnergyVector s T) 2

def finiteFunction (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest)
    (z : CuspCylinder) : ℂ := ∑ n ∈ s, physicalMode n (T n).function z

/-- This is the ordinary real horizontal derivative, before passing to L2. -/
theorem finite_horizontal_hasDerivAt (s : Finset NonzeroMode)
    (T : NonzeroMode → RadialTest) (y : PositiveHeight) (x : ℝ) :
    HasDerivAt (fun x : ℝ => finiteFunction s T ((x : UnitAddCircle), y))
      (∑ n ∈ s, (2 * Real.pi * Complex.I * (n : ℤ) : ℂ) *
        physicalMode n (T n).function ((x : UnitAddCircle), y)) x := by
  exact HasDerivAt.sum (fun n _ => physicalMode_horizontal_hasDerivAt n (T n).function y x)

theorem finite_vertical_hasDerivAt (s : Finset NonzeroMode)
    (T : NonzeroMode → RadialTest) (x : UnitAddCircle) (y : PositiveHeight) :
    HasDerivAt (fun v : ℝ => ∑ n ∈ s,
      AddCircle.fourier (n : ℤ) x * physicalLift (frequencyScale n) (T n).function v)
      (∑ n ∈ s, AddCircle.fourier (n : ℤ) x *
        deriv (physicalLift (frequencyScale n) (T n).function) y) y := by
  apply HasDerivAt.sum
  intro n hn
  have h := physicalLift_hasDerivAt (frequencyScale_pos n.property) y.property
    (T n).function ((T n).smooth.differentiable (by simp) _)
  simpa only [h.deriv] using h.const_mul (AddCircle.fourier (n : ℤ) x)

private theorem sum_ae (s : Finset NonzeroMode) (F : NonzeroMode → CylinderL2)
    (f : NonzeroMode → CuspCylinder → ℂ)
    (h : ∀ n, (F n : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] f n) :
    ((∑ n ∈ s, F n : CylinderL2) : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => ∑ n ∈ s, f n z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 cylinderMeasure
  | @insert n s hn ih =>
    simp only [Finset.sum_insert hn]
    filter_upwards [Lp.coeFn_add (F n) (∑ m ∈ s, F m), h n, ih] with z hz hn hs
    simpa only [Pi.add_apply, hn, hs] using hz

theorem finiteValue_ae (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) :
    (finiteValue s T : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] finiteFunction s T := by
  change ((∑ n ∈ s, modeEmbedding n (modeValue n (modeCorePoint n (T n))) : CylinderL2)
    : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] _
  apply sum_ae
  intro n
  rw [modeValue, modeCorePoint, physicalClosedEmbedding_on_core]
  have hy := (quasiMeasurePreserving_snd
    (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (physicalLift_memLp (frequencyScale_pos n.property) (T n)).coeFn_toLp
  filter_upwards [modeEmbedding_ae n (physicalCoreL2 _ _ (T n)), hy] with z hz hy
  simpa [physicalMode, physicalCoreL2, hy] using hz

theorem finiteVertical_ae (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) :
    (finiteVertical s T : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => ∑ n ∈ s, AddCircle.fourier (n : ℤ) z.1 *
        (z.2 : ℂ) * deriv (physicalLift (frequencyScale n) (T n).function) z.2) := by
  change ((∑ n ∈ s, modeEmbedding n (modeVertical n (modeCorePoint n (T n))))
    : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] _
  apply sum_ae
  intro n
  have hy := (quasiMeasurePreserving_snd
    (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (physicalClosedVertical_on_core_ae _ (frequencyScale_pos n.property) (T n))
  filter_upwards [modeEmbedding_ae n (modeVertical n (modeCorePoint n (T n))), hy]
    with z hz hy
  rw [hz, show modeVertical n (modeCorePoint n (T n)) z.2 = _ from hy]
  ring

theorem finiteHorizontal_ae (s : Finset NonzeroMode) (T : NonzeroMode → RadialTest) :
    (finiteHorizontal s T : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => ∑ n ∈ s, (z.2 : ℂ) *
        (2 * Real.pi * Complex.I * (n : ℤ) : ℂ) * physicalMode n (T n).function z) := by
  change ((∑ n ∈ s, modeEmbedding n (modeHorizontal n (modeCorePoint n (T n))))
    : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] _
  apply sum_ae
  intro n
  have hy := (quasiMeasurePreserving_snd
    (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (physicalClosedPotential_on_core_ae _ (frequencyScale_pos n.property) (T n))
  have hs := (quasiMeasurePreserving_snd
    (μ := AddCircle.haarAddCircle) (ν := heightMeasure)).ae
      (Lp.coeFn_smul (horizontalPhase n)
        (physicalClosedPotential _ _ (modeCorePoint n (T n))))
  filter_upwards [modeEmbedding_ae n (modeHorizontal n (modeCorePoint n (T n))),
    hy, hs] with z hz hy hs
  rw [hz]
  change AddCircle.fourier (n : ℤ) z.1 *
    ((horizontalPhase n • physicalClosedPotential _ _ (modeCorePoint n (T n))) z.2) = _
  rw [hs, hy]
  simp only [Pi.smul_apply, smul_eq_mul, physicalMode]
  calc
    _ = (z.2 : ℂ) * (horizontalPhase n * (frequencyScale n : ℂ)) *
      (AddCircle.fourier (n : ℤ) z.1 * physicalLift (frequencyScale n) (T n).function z.2) := by ring
    _ = _ := by rw [horizontalPhase_frequency]

theorem finite_modes_inner (s : Finset NonzeroMode) (f g : NonzeroMode → HeightL2) :
    inner ℂ (∑ n ∈ s, modeEmbedding n (f n)) (∑ n ∈ s, modeEmbedding n (g n)) =
      ∑ n ∈ s, inner ℂ (f n) (g n) := by
  classical
  simp only [sum_inner, inner_sum, modeEmbedding_inner,
    Subtype.val_injective.eq_iff]
  simp

def finiteDirichletPairing (s : Finset NonzeroMode)
    (T U : NonzeroMode → RadialTest) : ℂ :=
  inner ℂ (finiteVertical s T) (finiteVertical s U) +
    inner ℂ (finiteHorizontal s T) (finiteHorizontal s U)

/-- Exact finite-mode Dirichlet Parseval, with the actual physical closed
forms on the right. The preceding derivative lemmas identify the left
side with the literal hyperbolic gradient energy. -/
theorem finiteDirichletPairing_eq_sum_closed_forms (s : Finset NonzeroMode)
    (T U : NonzeroMode → RadialTest) :
    finiteDirichletPairing s T U = ∑ n ∈ s,
      physicalClosedForm (frequencyScale n) (frequencyScale_pos n.property)
        (modeCorePoint n (T n)) (modeCorePoint n (U n)) := by
  change inner ℂ (∑ n ∈ s, modeEmbedding n (modeVertical n (modeCorePoint n (T n))))
      (∑ n ∈ s, modeEmbedding n (modeVertical n (modeCorePoint n (U n)))) +
    inner ℂ (∑ n ∈ s, modeEmbedding n (modeHorizontal n (modeCorePoint n (T n))))
      (∑ n ∈ s, modeEmbedding n (modeHorizontal n (modeCorePoint n (U n)))) = _
  rw [finite_modes_inner, finite_modes_inner, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [modeHorizontal_inner]
  rfl

theorem finiteDirichletPairing_eq_sum_literal_mode_energy (s : Finset NonzeroMode)
    (T U : NonzeroMode → RadialTest) :
    finiteDirichletPairing s T U = ∑ n ∈ s, physicalCoreEnergy n (T n) (U n) := by
  rw [finiteDirichletPairing_eq_sum_closed_forms]
  apply Finset.sum_congr rfl
  intro n hn
  exact physicalClosedForm_on_actual_mode_core n.property (T n) (U n)

end
end ImbalancedChen.Part3.ActualCylinderFiniteEnergyCore20261026b
