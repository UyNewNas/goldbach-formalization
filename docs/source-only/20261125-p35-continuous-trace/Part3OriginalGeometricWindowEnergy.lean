import ImbalancedChen.Part3ContinuousTraceCauchy
import ImbalancedChen.Part3OriginalPrintedContinuousTrace
import ImbalancedChen.Part3OriginalExceptionalPostRemovalPair
import ImbalancedChen.Part3OriginalClassicalSpectralSupports

/-! Cumulative printed continuous energy on the two physical Fourier rows.
The source side pays the actual continuous ABL invoice before the uniform
regular large sieve. The common m interval is the original clipped interval. -/
namespace ImbalancedChen.Part3.OriginalGeometricWindowEnergy20261123

noncomputable section
open Finset Set MeasureTheory Complex
open scoped BigOperators
open OriginalPrintedContinuousTrace20261123 GeometricCriticalEisenstein20261123
open ActualCuspDenominatorClasses20261110 OriginalRegularPacketTest20261113
open OriginalContinuousClassRemoval20261110 OriginalClassicalSpectralSupports20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalSignedTraceInput20261102 OriginalTwoZFourierAssembly20261102
open OriginalPrincipalTraceRow20261102r ActualPrincipalCuspOneRemoval20261102r
open OriginalCumulativeContinuousRemoval20261110 ActualContinuousClassFourier20261110
open OriginalExceptionalPostRemovalPair20261113 (rowLength rowMass)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale)
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def leftMass (q : ℕ+) (J j : ℕ) (ell : D4 → ℤ) (t : ℝ) : ℝ :=
  printedMass (fun a : Parameters q.val => M J j ell (fun n => printedR a false n t))

def sourceMass (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (q : ℕ+) (hq : q.val ∈ levelCarrier D k) (upper negativeM : Bool)
    (ell : D4 → ℤ) (t : ℝ) : ℝ :=
  printedMass (fun a : Parameters q.val =>
    source D r k ⟨q.val,hq⟩ upper negativeM ell (fun n => printedR a true n t))

def reducedMass (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (q : ℕ+) (hq : q.val ∈ levelCarrier D k) (upper negativeM : Bool)
    (ell : D4 → ℤ) (t : ℝ) : ℝ :=
  printedMass (fun a : Parameters q.val =>
    reduced D r k ⟨q.val,hq⟩ upper negativeM ell (fun n => printedR a true n t))

private theorem printedR_cont {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool) (n : ℤ) :
    Continuous (printedR a one n) := by
  by_cases hn : n = 0
  · subst n
    simp [printedR]
  let G (t : ℝ) := gammaScale (ActualCriticalCuspEvaluation20261110.criticalPoint t)
  have hne (t : ℝ) : G t ≠ 0 := by
    intro he
    have H := gammaScale_norm_sq t
    change ‖G t‖^2 = _ at H
    rw [he] at H
    have hzero : Real.cosh (Real.pi*t) = 0 := by simpa using H.symm
    exact (Real.cosh_pos _).ne' hzero
  have hπ : Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ)^s) := fun _ =>
    differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : Continuous G := by
    have h := (hπ.mul Complex.differentiable_one_div_Gamma).continuous.comp
      (show Continuous ActualCriticalCuspEvaluation20261110.criticalPoint by
        unfold ActualCriticalCuspEvaluation20261110.criticalPoint
        fun_prop)
    simpa only [G,gammaScale,Function.comp_apply,div_eq_mul_inv,one_mul] using h
  have he : printedR a one n = fun t => nativeR a one n t / G t := by
    funext t
    apply (eq_div_iff (hne t)).mpr
    exact (mul_comm _ _).trans (nativeR_eq_geometric a one n hn t).symm
  rw [he]
  exact (nativeR_cont a one n).div hG hne

private theorem mass_cont {N : ℕ} [NeZero N] (one : Bool) (S : Finset ℕ)
    (w : ℕ → ℂ) (idx : ℕ → ℤ) :
    Continuous (fun t => printedMass (fun a : Parameters N =>
      markedRow S w idx (fun n => printedR a one n t))) := by
  apply continuous_finsetSum
  intro a _
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  exact continuous_finsetSum _ (fun n _ => continuous_const.mul (printedR_cont a one (idx n)))

/-- A single epsilon constant works for both physical rows. The cost on the
unremoved signed n row is the square of the actual divisor count of |a|ν. -/
theorem original_two_cumulative_windows (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key))
      (k : BlockKey) (q : ℕ+) (hq : q.val ∈ levelCarrier D k),
      D.block.atom.residue ≠ 0 → ∀ (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
      (T : ℝ), 1 ≤ T →
        (∫ t in Icc (-T) T, leftMass q J j ell t) ≤
          C * (T^2 + (classicalMScale j)^(1+e)/(q.val : ℝ)) *
            ((commonMBlock J j).card : ℝ) ∧
        (∫ t in Icc (-T) T, reducedMass D r k q hq upper negativeM ell t) ≤
          C * (T^2 + (rowLength k)^(1+e)/(q.val : ℝ)) * rowMass D r k q ∧
        (∫ t in Icc (-T) T, sourceMass D r k q hq upper negativeM ell t) ≤
          ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2 *
            (C * (T^2 + (rowLength k)^(1+e)/(q.val : ℝ)) * rowMass D r k q) := by
  obtain ⟨C,hC,H⟩ := printed_continuous_large_sieve e he
  refine ⟨C,hC,?_⟩
  intro D r k q hq ha upper negativeM J j ell T hT
  classical
  let wM := fun m : ℕ => star ((commonPoissonCompleted J j (ell 1)).weight m)
  let sg := principalTraceSign D k negativeM
  let wN := fun n : ℕ => modulatedBeta D r k upper ell q.val n * sourceCuspPhase q.val (-(sg*(n : ℤ)))
  let neg := traceNegative D k negativeM
  let U := Icc (-T) T
  have hmr : leftMass q J j ell = printedLine q.val false false (commonMBlock J j) wM := by
    funext t
    rfl
  have hnr : reducedMass D r k q hq upper negativeM ell =
      printedLine q.val true neg (nCarrier D k q.val) wN := by
    funext t
    cases Hsign : traceNegative D k negativeM <;>
      simp [reducedMass, reduced, printedLine, markedRow, wN, sg, neg,
        principalTraceSign, mark, Hsign]
  have hbandM : Dyadic (classicalMScale j) (commonMBlock J j) :=
    fun m hm => commonMBlock_classical_support J j hm
  have hmassM : energy (commonMBlock J j) wM = ((commonMBlock J j).card : ℝ) := by
    unfold energy
    calc
      _ = ∑ _m ∈ commonMBlock J j, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro m hm
        change ‖star ((commonPoissonCompleted J j (ell 1)).weight m)‖^2 = 1
        rw [norm_star, commonPoissonCompleted_weight J j (ell 1) m hm, Complex.norm_exp]
        simp [Complex.mul_re,Complex.mul_im]
      _ = _ := by simp
  have hmassN : energy (nCarrier D k q.val) wN = rowMass D r k q := by
    simp only [energy,wN,norm_mul,sourceCuspPhase_norm,mul_one,norm_modulatedBeta,rowMass]
  obtain ⟨n₀,h₀⟩ := levelCarrier_has_n D k hq
  have hν : 0 < (k.1 : ℝ) := by exact_mod_cast (nCarrier_positive_coprime D k q.val h₀).1
  have hbandN : Dyadic (rowLength k) (nCarrier D k q.val) := by
    intro n hn
    obtain ⟨lo,hi⟩ := nCarrier_dyadic D k q.val hn
    rw [Nat.cast_mul] at lo hi
    constructor
    · change dyadicScale k.2.1/(k.1 : ℝ) < (n : ℝ)
      exact (div_lt_iff₀ hν).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using lo)
    change (n : ℝ) ≤ 2*(dyadicScale k.2.1/(k.1 : ℝ))
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hν).mpr (by simpa only [mul_comm (k.1 : ℝ) (n : ℝ)] using hi)
  have h₁ : 1 ≤ (n₀ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (nCarrier_positive_coprime D k q.val h₀).2.1
  have hL : 1/2 ≤ rowLength k := by linarith only [h₁, (hbandN n₀ h₀).2]
  have hm := (H q.val false false hT (classicalMScale_bounds j).1 _ wM hbandM).2
  have hn := (H q.val true neg hT hL _ wN hbandN).2
  rw [← hmr,hmassM] at hm
  rw [← hnr,hmassN] at hn
  refine ⟨hm,hn,?_⟩
  let price : ℝ := ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2
  have hj : ∀ t, sourceMass D r k q hq upper negativeM ell t ≤
      price * reducedMass D r k q hq upper negativeM ell t :=
    fun t => original_printed_removal D r k ⟨q.val,hq⟩ ha upper negativeM ell t
  have hsrc : Continuous (sourceMass D r k q hq upper negativeM ell) :=
    mass_cont true _ _ _
  have hred : Continuous (reducedMass D r k q hq upper negativeM ell) :=
    mass_cont true _ _ _
  have isrc : IntegrableOn (sourceMass D r k q hq upper negativeM ell) U :=
    hsrc.continuousOn.integrableOn_compact isCompact_Icc
  have ired : IntegrableOn (fun t => price * reducedMass D r k q hq upper negativeM ell t) U :=
    (hred.const_mul price).continuousOn.integrableOn_compact isCompact_Icc
  have hcomp := integral_mono_ae (μ := volume.restrict U) isrc ired
    (Filter.Eventually.of_forall hj)
  rw [integral_const_mul] at hcomp
  exact hcomp.trans (mul_le_mul_of_nonneg_left hn (sq_nonneg _))

/-- SOURCE_ONLY_DEPENDENCY_CLOSURE_UNAVAILABLE.
The tested, unremoved continuous trace on one original height window.
The same sieve constant works for every level, sign, interval and test. -/
theorem original_tested_continuous_window (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : OriginalData) (r : ZMod (prefixPeriod D.key))
      (k : BlockKey) (q : ℕ+) (hq : q.val ∈ levelCarrier D k),
      D.block.atom.residue ≠ 0 → ∀ (upper negativeM : Bool) (J j : ℕ)
      (ell : D4 → ℤ) (T : ℝ), 1 ≤ T → ∀ (test : ℝ → ℂ), Continuous test →
      ∀ (B : ℝ), 0 ≤ B → (∀ t ∈ Icc (-T) T, ‖test t‖ ≤ B) →
      ‖∫ t in Icc (-T) T, test t * (∑ a : Parameters q.val,
        star (M J j ell (fun n => printedR a false n t)) *
          source D r k ⟨q.val,hq⟩ upper negativeM ell (fun n => printedR a true n t) /
            (Real.pi : ℂ))‖ ≤
        B * ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ) * C *
          (Real.sqrt ((T^2 + (classicalMScale j)^(1+e)/(q.val : ℝ)) *
             ((commonMBlock J j).card : ℝ)) *
           Real.sqrt ((T^2 + (rowLength k)^(1+e)/(q.val : ℝ)) * rowMass D r k q)) := by
  obtain ⟨C,hC,hWindows⟩ := original_two_cumulative_windows e he
  refine ⟨C,hC,?_⟩
  intro D r k q hq ha upper negativeM J j ell T hT test htest B hB hbound
  classical
  obtain ⟨hm,_,hs⟩ := hWindows D r k q hq ha upper negativeM J j ell T hT
  have row_cont (a : Parameters q.val) (one : Bool) (S : Finset ℕ)
      (w : ℕ → ℂ) (idx : ℕ → ℤ) :
      Continuous (fun t => markedRow S w idx (fun n => printedR a one n t)) := by
    exact continuous_finsetSum _ (fun n _ => continuous_const.mul (printedR_cont a one (idx n)))
  refine ContinuousTraceCauchy.norm_integral_test_mul_printed_trace_le_of_energy_bounds
    (fun (a : Parameters q.val) t => M J j ell (fun n => printedR a false n t))
    (fun (a : Parameters q.val) t =>
      source D r k ⟨q.val,hq⟩ upper negativeM ell (fun n => printedR a true n t))
    (fun a => row_cont a false _ _ _) (fun a => row_cont a true _ _ _)
    test htest T B C ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)
    _ _ hB hC.le (by positivity) hbound ?_ ?_
  · simpa only [leftMass, printedMass, mul_assoc] using hm
  · simpa only [sourceMass, printedMass, mul_assoc] using hs

end
end ImbalancedChen.Part3.OriginalGeometricWindowEnergy20261123
