import ImbalancedChen.Part3ActualEisensteinFixedCFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual GammaInfinity\Gamma0 Eisenstein Fourier coefficient is the
height term plus the absolutely convergent sum of its positive-c primitive
blocks. This is proved from the original primitive-row norm-integral bound,
not from formal rearrangement of a divergent tsum. Negating both literal
row coordinates pairs positive and negative c; the c=0 rows are exactly
(0,1) and (0,-1). Thus the earlier factor 1/2 is canceled by an actual
pairing. The level condition remains in every primitive block. No zeta
or spectral identity is claimed.
-/

namespace ImbalancedChen.Part3.ActualEisensteinPositiveCFourier20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEisensteinHalfPairs20261025a
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PrimitiveRealEisensteinAutomorphy
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinFixedCFourier20261025a

/-- The actual integral of one literal primitive row. -/
def rowIntegral (N : ℕ) (s y : ℝ) (hy : 0 < y) (n c : ℤ)
    (d : PrimitiveD N c) : ℂ :=
  ∫ x in Ioc (0 : ℝ) 1,
    fourierPhase n x * (seed s (horizontalPoint y hy x) ![c, d.1] : ℂ)

/-- Grouping the actual primitive Fourier integrals at one integer c. -/
def integerBlockFourier (N : ℕ) (s y : ℝ) (hy : 0 < y) (n c : ℤ) : ℂ :=
  ∑' d : PrimitiveD N c, rowIntegral N s y hy n c d

/-- Absolute convergence BEFORE grouping, on the genuine sigma type of
primitive level rows. -/
theorem rowIntegral_sigma_norm_summable (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Summable (fun p : Σ c : ℤ, PrimitiveD N c =>
      ‖rowIntegral N s y hy n p.1 p.2‖) := by
  have h := (primitiveFourierTerm_integral_norm_summable N s hs y hy n).of_nonneg_of_le
    (fun v => norm_nonneg (∫ x in Ioc (0 : ℝ) 1,
      primitiveFourierTerm N s y hy n v x))
    (fun v => norm_integral_le_integral_norm _)
  exact (rowByFirstEquiv N).symm.summable_iff.mpr h

theorem integerBlockFourier_summable (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Summable (integerBlockFourier N s y hy n) :=
  (rowIntegral_sigma_norm_summable N s hs y hy n).of_norm.sigma

/-- Literal d -> -d is a bijection between the c and -c primitive fibers,
including the actual N|c condition. -/
def negativeDEquiv (N : ℕ) (c : ℤ) : PrimitiveD N c ≃ PrimitiveD N (-c) where
  toFun d := ⟨-d.1, d.property.1.neg_neg, by simpa using d.property.2⟩
  invFun d := ⟨-d.1, by simpa using d.property.1.neg_neg,
    by simpa using d.property.2⟩
  left_inv d := by apply Subtype.ext; simp
  right_inv d := by apply Subtype.ext; simp

/-- Evenness follows from the ACTUAL seed under simultaneous row negation. -/
theorem integerBlockFourier_even (N : ℕ) (s y : ℝ) (hy : 0 < y) (n : ℤ) :
    Function.Even (integerBlockFourier N s y hy n) := by
  intro c
  unfold integerBlockFourier
  rw [← (negativeDEquiv N c).tsum_eq]
  apply tsum_congr
  intro d
  unfold rowIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  have hvec : (![(-c), -(d.1)] : Fin 2 → ℤ) = -![c, d.1] := by
    funext j
    fin_cases j <;> rfl
  change fourierPhase n x *
      (seed s (horizontalPoint y hy x) ![-c, -d.1] : ℂ) = _
  rw [hvec, seed_neg]

/-- The grouped row integrals equal the integral of the FULL primitive
block, with the interchange justified by the original norm-integral sum. -/
theorem integerBlockFourier_eq_fixedFirst (N c : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    integerBlockFourier N s y hy n (c : ℤ) =
      fixedFirstFourier N c s y hy n := by
  let e := (rowByFirstEquiv N).symm
  have hnorm : Summable (fun p : Σ c : ℤ, PrimitiveD N c =>
      ∫ x in Ioc (0 : ℝ) 1,
        ‖fourierPhase n x * (seed s (horizontalPoint y hy x) ![p.1, p.2.1] : ℂ)‖) :=
    e.summable_iff.mpr (primitiveFourierTerm_integral_norm_summable N s hs y hy n)
  have hint (d : PrimitiveD N (c : ℤ)) : IntegrableOn
      (fun x : ℝ => fourierPhase n x *
        (seed s (horizontalPoint y hy x) ![(c : ℤ), d.1] : ℂ)) (Ioc (0 : ℝ) 1) := by
    let v : LevelPrimitiveRow N := ⟨![(c : ℤ), d.1], by simpa using d.property⟩
    exact primitiveFourierTerm_integrable N s hs y hy n v
  unfold integerBlockFourier rowIntegral fixedFirstFourier
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_tsum_of_summable_integral_norm hint (hnorm.sigma_factor (c : ℤ))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [fixedFirstBlock, Complex.ofReal_tsum, tsum_mul_left]

/-- Exactly two primitive rows have c=0; these are genuine rows at every level. -/
def zeroDParam (N : ℕ) : Bool → PrimitiveD N 0
  | false => ⟨1, by norm_num⟩
  | true => ⟨-1, by norm_num⟩

theorem zeroDParam_bijective (N : ℕ) : Function.Bijective (zeroDParam N) := by
  constructor
  · intro a b h
    cases a <;> cases b
    · rfl
    · have h' := congrArg (fun d : PrimitiveD N 0 => d.1) h
      norm_num [zeroDParam] at h'
    · have h' := congrArg (fun d : PrimitiveD N 0 => d.1) h
      norm_num [zeroDParam] at h'
    · rfl
  · intro d
    rcases Int.isUnit_eq_one_or (isCoprime_zero_left.mp d.property.1) with h | h
    · exact ⟨false, Subtype.ext h.symm⟩
    · exact ⟨true, Subtype.ext h.symm⟩

def zeroDEquiv (N : ℕ) : Bool ≃ PrimitiveD N 0 :=
  Equiv.ofBijective (zeroDParam N) (zeroDParam_bijective N)

/-- Orthogonality of the literal phase on its actual period. -/
theorem integral_fourierPhase (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [fourierPhase]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hc : -(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I ≠ 0 := by
      exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) hnc)) Complex.I_ne_zero
    have hperiod : fourierPhase n 1 = 1 := by
      have h := fourierPhase_add_int n 1 0
      simpa [fourierPhase] using h
    simp only [if_neg hn]
    unfold fourierPhase at hperiod ⊢
    rw [intervalIntegral.integral_exp_mul_complex hc]
    simpa using congrArg
      (fun v : ℂ => (v - 1) / (-(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I)) hperiod

/-- The isolated height contribution from the actual c=0 primitive pair. -/
def heightFourier (s y : ℝ) (n : ℤ) : ℂ :=
  if n = 0 then (y ^ s : ℝ) else 0

theorem integerBlockFourier_zero (N : ℕ) (s y : ℝ) (hy : 0 < y) (n : ℤ) :
    integerBlockFourier N s y hy n 0 = 2 * heightFourier s y n := by
  unfold integerBlockFourier
  rw [← (zeroDEquiv N).tsum_eq]
  have hterm (b : Bool) : rowIntegral N s y hy n 0 (zeroDEquiv N b) =
      (∫ x in (0 : ℝ)..1, fourierPhase n x) * (y ^ s : ℂ) := by
    unfold rowIntegral
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hseed (x : ℝ) : seed s (horizontalPoint y hy x)
        ![0, (zeroDEquiv N b).1] = y ^ s := by
      cases b <;> simp [zeroDEquiv, Equiv.ofBijective_apply, zeroDParam, seed, horizontalPoint]
    simp_rw [hseed]
    exact intervalIntegral.integral_mul_const _ _
  simp_rw [hterm]
  rw [tsum_fintype, Fintype.sum_bool, integral_fourierPhase]
  by_cases hn : n = 0 <;> simp [heightFourier, hn] <;> ring

/-- The positive-c series of actual full primitive-block coefficients is
ABSOLUTELY convergent; this is inherited from the original all-row proof. -/
theorem fixedFirstFourier_positive_norm_summable (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Summable (fun c : ℕ+ => ‖fixedFirstFourier N (c : ℕ) s y hy n‖) := by
  have hinj : Function.Injective (fun c : ℕ+ => ((c : ℕ) : ℤ)) := by
    intro a b h
    apply Subtype.ext
    exact_mod_cast h
  have h := (integerBlockFourier_summable N s hs y hy n).norm.comp_injective hinj
  simpa only [integerBlockFourier_eq_fixedFirst N _ s hs y hy n] using h

/-- Full actual parabolic Eisenstein Fourier coefficient: one height term
plus the absolutely convergent POSITIVE c series, with its genuine level rows. -/
theorem actualEisensteinFourier_eq_positive_c_sum (N : ℕ) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    actualEisensteinFourier N s y hy n = heightFourier s y n +
      ∑' c : ℕ+, fixedFirstFourier N (c : ℕ) s y hy n := by
  rw [actualEisensteinFourier_eq_integer_c_sum N s hs y hy n]
  change (1 / 2 : ℂ) * ∑' c : ℤ, integerBlockFourier N s y hy n c = _
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat
    (integerBlockFourier_even N s y hy n) (integerBlockFourier_summable N s hs y hy n),
    integerBlockFourier_zero]
  simp_rw [integerBlockFourier_eq_fixedFirst N _ s hs y hy n]
  rw [nsmul_eq_mul]
  ring

end
end ImbalancedChen.Part3.ActualEisensteinPositiveCFourier20261025a

