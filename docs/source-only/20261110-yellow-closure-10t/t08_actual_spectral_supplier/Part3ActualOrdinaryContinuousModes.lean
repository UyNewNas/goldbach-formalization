import ImbalancedChen.Part3ActualYoungCriticalProjection
import ImbalancedChen.Part3OriginalCharacterTraceRow

/-! The actual two physical rows of every ordinary Eisenstein oldform,
with the full-level principal function carried through the same two
original frames at each permitted dilation. -/
namespace ImbalancedChen.Part3.ActualOrdinaryContinuousModes20261110

noncomputable section
open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualYoungCriticalD20261110 ActualCriticalCuspEvaluation20261110
open ActualCharacterCriticalFamily20261110 ActualCharacterOriginalCuspFourier20261110
open OriginalCharacterTraceRow20261110 ActualPrincipalOldformRemoval20261102r
open ActualPrincipalCuspOneRemoval20261102r ActualFrickeCuspPhase20261025a
open ActualCuspFourierSectionSourceOnly ComplexOrderKBridgeSourceOnly
open FiniteLevelEisensteinOldforms20261025a LevelOldformFricke20261026a
open CompletedActualEisensteinIdentity20261025a CompletedEisensteinIntegerMean20261026a
open FrickeNormalizer Gamma0DegeneracyMapSourceOnly
open ActualEisensteinFourierInterchange20261025a PowerSeedFourierLaplaceFubini
open CompletedKWeightedIntegral20261026b

def principalFactor (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s/Complex.Gamma s*reciprocalL (1 : DirichletCharacter ℂ 1) (2*s)

def incoming {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+) (t : ℝ) (z : ℍ) : ℂ :=
  ordinary χ (criticalPoint t) (degeneracyDiagonal d d.pos • z)

def infR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+) (n : ℤ) (t : ℝ) : ℂ :=
  if q = 1 then principalFactor (criticalPoint t) * principalDilationAmplitude d n.natAbs (criticalPoint t)
  else infinityK χ d n (criticalPoint t)/2

def radial (n : ℤ) (t y : ℝ) : ℂ :=
  2*(Real.sqrt y : ℂ)*complexOrderK (criticalPoint t-1/2) (2*Real.pi*|(n : ℝ)|*y)

def cuspR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (e : ℕ+) (n : ℤ) (t : ℝ) : ℂ :=
  sourceCuspPhase N n*(χ (-1 : ZMod q)*infR χ e n t)

private theorem t_ne (t : ℝ) : criticalPoint t ≠ 0 ∧ criticalPoint t ≠ 1 := by
  constructor <;> intro he <;> have h := congrArg Complex.re he <;> norm_num [criticalPoint,Complex.mul_re] at h

private theorem phase_eq (n : ℤ) (x : ℝ) : fourierPhase n x = integerPhase (-n) x := by
  unfold fourierPhase integerPhase
  congr 1
  push_cast
  ring

private theorem same_horizontal (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontal y hy x = horizontalPoint y hy x := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [horizontal,horizontalPoint]

theorem incoming_invariant {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (N : ℕ) (hN : 0 < N) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N) (t : ℝ)
    (γ : SL(2,ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    incoming χ d t (γ • z) = incoming χ d t z := by
  by_cases h : q = 1
  · subst q
    simpa only [incoming,ordinary,if_pos rfl,principalOrdinary,← pnatDilate_eq_degeneracy] using
      congrArg (fun c : ℂ => principalFactor (criticalPoint t)*c)
        (principal_dilation_Gamma0_invariant N hN d (by simpa using hle) _ (t_ne t).1 (t_ne t).2 γ hγ z)
  · simpa only [incoming,ordinary,if_neg h,oldform] using
      oldform_invariant (NeZero.pos q) h χ hχ N d hle (criticalPoint t) γ hγ z

theorem incoming_fricke {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (N : ℕ) (hN : 0 < N) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N) (t : ℝ) (z : ℍ) :
    incoming χ d t (frickeSL N hN • z) =
      χ (-1 : ZMod q)*incoming χ (complement N q hN (NeZero.pos q) d hle) t z := by
  by_cases h : q = 1
  · subst q
    have hd : (d : ℕ) ∣ N := by simpa using hle
    have he : complement N 1 hN (NeZero.pos 1) d hle = complementaryIndex N hN d hd := by
      apply Subtype.ext
      simp [complement,complementaryIndex]
    have H := completed_levelOne_fricke_integer N hN d hd (criticalPoint t) (t_ne t).1 (t_ne t).2 z
    simp only [incoming,ordinary,if_pos rfl,principalOrdinary,he,← pnatDilate_eq_degeneracy,H,
      Subsingleton.elim (-1 : ZMod 1) 1,map_one,one_mul]
  · simpa only [incoming,ordinary,if_neg h,oldform] using
      oldform_fricke (NeZero.pos q) h χ hχ N hN d hle (criticalPoint t) z

/-- Continuity of the actual section, including both full-level constant
terms and the complete signed nonprincipal Fourier series. -/
theorem incoming_horizontal_continuous {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (t y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => incoming χ d t (horizontalPoint y hy x)) := by
  by_cases h : q = 1
  · subst q
    simpa only [incoming,ordinary,if_pos rfl,principalOrdinary,← pnatDilate_eq_degeneracy] using
      continuous_const.mul (completed_integer_dilation_continuous (criticalPoint t) d y hy)
  · let Y := (d : ℝ)*y
    have hY : 0 < Y := mul_pos (by exact_mod_cast d.pos) hy
    let X := fun x : ℝ => (d : ℝ)*x
    have hp (x : ℝ) : degeneracyDiagonal d d.pos • horizontalPoint y hy x = horizontalPoint Y hY (X x) := by
      apply UpperHalfPlane.ext
      rw [degeneracyDiagonal_smul_coe]
      apply Complex.ext <;> simp [X,Y,horizontalPoint,Complex.mul_re,Complex.mul_im]
    simp only [incoming,ordinary,if_neg h,primitiveFamily,hp]
    apply continuous_const.mul
    change Continuous (fun x : ℝ => ∑' n : ℤ, ActualCharacterCompletedFourier20261110.continuedCoefficient χ n Y (criticalPoint t)*
      fourier n ((X x : ℝ) : UnitAddCircle))
    apply continuous_tsum (fun n => continuous_const.mul ((fourier n).continuous.comp
      (show Continuous (fun x : ℝ => ((X x : ℝ) : UnitAddCircle)) by unfold X; fun_prop)))
      (coefficient_norm_summable χ Y hY (criticalPoint t))
    intro n x
    rw [norm_mul,show ‖fourier n ((X x : ℝ) : UnitAddCircle)‖ = 1 from Circle.norm_coe _,mul_one]

private theorem principal_signed_integral (d : ℕ+) (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x*completedActualEisenstein (criticalPoint t)
      (pnatDilate d (horizontalPoint y hy x))) =
        radial n t y*principalDilationAmplitude d n.natAbs (criticalPoint t) := by
  let ε : ℤ := if n < 0 then 1 else -1
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : n < 0 <;> simp [ε,h]
  have he : ε*(n.natAbs : ℤ) = -n := by
    by_cases h : n < 0
    · simp [ε,h,Int.natCast_natAbs,abs_of_neg h]
    · simp [ε,h,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt h)]
  have hnR : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have H := completed_integer_fourier_eq_principalAmplitude d n.natAbs (Int.natAbs_pos.mpr hn)
    (criticalPoint t) y hy ε hε
  rw [he,hnR] at H
  calc
    _ = ∫ x in (0 : ℝ)..1, completedActualEisenstein (criticalPoint t)
          (pnatDilate d (horizontalPoint y hy x))*integerPhase (-n) x := by
      apply intervalIntegral.integral_congr
      intro x _
      rw [phase_eq,mul_comm]
    _ = _ := by rw [H,radial]; ring

theorem incoming_infinity_mode {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x*incoming χ d t (horizontalPoint y hy x)) =
      radial n t y*infR χ d n t := by
  by_cases h : q = 1
  · subst q
    have H (x : ℝ) : fourierPhase n x*incoming χ d t (horizontalPoint y hy x) =
      principalFactor (criticalPoint t)*(fourierPhase n x*completedActualEisenstein (criticalPoint t)
        (pnatDilate d (horizontalPoint y hy x))) := by
      simp only [incoming,ordinary,if_pos rfl,principalOrdinary,principalFactor,pnatDilate_eq_degeneracy]
      ring
    simp_rw [H]
    rw [intervalIntegral.integral_const_mul,principal_signed_integral d n hn t y hy,infR,if_pos rfl]
    ring
  · simp only [incoming,ordinary,if_neg h,infR]
    change (∫ x in (0 : ℝ)..1,fourierPhase n x*oldform χ d (criticalPoint t) (horizontalPoint y hy x)) = _
    rw [infinity_fourier χ d (criticalPoint t) y hy n hn,radial]
    ring

def sectionMode (N : ℕ) (hN : 0 < N) (one : Bool) (F : ℍ → ℂ)
    (n : ℤ) (y : ℝ) (hy : 0 < y) : ℂ :=
  if one then sourceCuspPhase N n*∫ x in (0 : ℝ)..1, fourierPhase n x*
    F (frickeSL N hN • horizontalPoint y hy x)
  else ∫ x in (0 : ℝ)..1, fourierPhase n x*F (horizontalPoint y hy x)

theorem sectionMode_cuspOne (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ)
    (hF : ∀ g : SL(2,ℤ), g ∈ CongruenceSubgroup.Gamma0 N → ∀ z : ℍ,F (g • z) = F z)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    sectionMode N hN true F n y hy = fourierCoeff (sigmaOneSection N hN F hF y hy) n := by
  rw [sigmaOne_fourierCoeff_fricke_phase,frickeFourierCoeff,fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
  simp only [sectionMode,if_true,sourceCuspPhase,div_one,one_smul,zero_add,smul_eq_mul,
    PowerSeedPeriodization.native_fourier_phase]
  apply congrArg (fun c : ℂ => Complex.exp (2*Real.pi*I*(n : ℂ)/(N : ℂ))*c)
  apply intervalIntegral.integral_congr
  intro x _
  change _ = fourierPhase n x*F (frickeSL N hN • horizontal y hy x)
  rw [same_horizontal]

def dilationR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) (hN : 0 < N)
    (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N) (one : Bool) (n : ℤ) (t : ℝ) : ℂ :=
  if one then cuspR χ N (complement N q hN (NeZero.pos q) d hle) n t else infR χ d n t

theorem incoming_mode {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (N : ℕ) (hN : 0 < N) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N) (one : Bool)
    (n : ℤ) (hn : n ≠ 0) (t y : ℝ) (hy : 0 < y) :
    sectionMode N hN one (incoming χ d t) n y hy = radial n t y*dilationR χ N hN d hle one n t := by
  cases one
  · exact incoming_infinity_mode χ d n hn t y hy
  · simp only [sectionMode,dilationR,if_true,cuspR,incoming_fricke χ hχ N hN d hle]
    simp_rw [mul_left_comm (fourierPhase n _) (χ (-1 : ZMod q))]
    rw [intervalIntegral.integral_const_mul,incoming_infinity_mode χ _ n hn t y hy]
    ring

end
end ImbalancedChen.Part3.ActualOrdinaryContinuousModes20261110

