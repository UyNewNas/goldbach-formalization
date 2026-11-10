import ImbalancedChen.Part3ActualCharacterOriginalCuspFourier
import ImbalancedChen.Part3OriginalPrincipalTraceRow

/-!
Original signed n-row of the continued Young incoming characters.
The ordinary Whittaker normalization comes from each physical Fourier
integral. Index removal retains the same actual beta and residual phase.
-/
namespace ImbalancedChen.Part3.OriginalCharacterTraceRow20261110

noncomputable section
open Complex Set MeasureTheory
open scoped BigOperators UpperHalfPlane MatrixGroups
open ActualCharacterCriticalFamily20261110 ActualCharacterOriginalCuspFourier20261110
open CharacterPairDivisorAmplitude20261102s OriginalCharacterPairDilation20261102s
open ActualFrickeCuspPhase20261025a ComplexOrderKBridgeSourceOnly
open ActualEisensteinFourierInterchange20261025a PowerSeedFourierLaplaceFubini
open OriginalPrincipalTraceRow20261102r ActualPrincipalCuspOneRemoval20261102r
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalSignedTraceInput20261102
open OriginalTwoZFourierAssembly20261102 P3NativePeriod64SamplingSourceOnly (D4)

private def signed (negative : Bool) (n : ℕ) : ℤ := if negative then -(n : ℤ) else n

private theorem halfK_signed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (negative : Bool) (n : ℕ) (s : ℂ) :
    infinityK χ d (signed negative n) s / 2 =
      uncompletionFactor χ s * pairDilationAmplitude χ χ negative d n s := by
  have hd : ((d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast d.ne_zero
  cases negative
  · simp only [signed,Bool.false_eq_true,if_false,infinityK,pairDilationAmplitude,
      signedPairAmplitude,Int.natCast_dvd_natCast,← Int.natCast_ediv,amplitude_nat,one_mul]
    split_ifs <;> ring
  · simp only [signed,if_true,infinityK,pairDilationAmplitude,signedPairAmplitude,
      dvd_neg,Int.natCast_dvd_natCast]
    split_ifs with h
    · have hfac : (n : ℤ) = ((d : ℕ) : ℤ)*((n/(d : ℕ) : ℕ) : ℤ) := by
        exact_mod_cast (Nat.mul_div_cancel' h).symm
      have hdiv : -(n : ℤ)/((d : ℕ) : ℤ) = -((n/(d : ℕ) : ℕ) : ℤ) := by
        conv_lhs => rw [hfac,← mul_neg,Int.mul_ediv_cancel_left _ hd]
      rw [hdiv,amplitude_neg_nat]
      ring
    · ring

/-- R=sqrt(|n|)*rho_W is half the actual sqrt(y)K coefficient. The second
oldform index e below is the complementary positive dilation N/(q²d). -/
def cuspOneR {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ)
    (e : ℕ+) (n : ℤ) (s : ℂ) : ℂ :=
  sourceCuspPhase N n * (χ (-1 : ZMod q) * (infinityK χ e n s / 2))

theorem physical_infinity_whittaker {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * oldform χ d s (horizontalPoint y hy x)) =
      ((infinityK χ d n s/2) / (Real.sqrt |(n : ℝ)| : ℂ)) *
        (2*(Real.sqrt (|(n : ℝ)|*y) : ℂ)) * complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y) := by
  have hr : (Real.sqrt |(n : ℝ)| : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hn))).ne'
  rw [infinity_fourier χ d s y hy n hn,Real.sqrt_mul (abs_nonneg _),Complex.ofReal_mul]
  field_simp [hr] <;> ring

theorem physical_whittaker {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (hN : 0 < N)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ N) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (sigmaOneSection N hN (oldform χ d s)
      (oldform_invariant hq h1 χ hχ N d hlevel s) y hy) n =
      (cuspOneR χ N (complement N q hN hq d hlevel) n s / (Real.sqrt |(n : ℝ)| : ℂ)) *
        (2*(Real.sqrt (|(n : ℝ)|*y) : ℂ)) * complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y) := by
  have hr : (Real.sqrt |(n : ℝ)| : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hn))).ne'
  rw [original_cuspOne_fourier hq h1 χ hχ N hN d hlevel s y hy n hn,cuspOneR,
    sourceCuspPhase,Real.sqrt_mul (abs_nonneg _),Complex.ofReal_mul]
  field_simp [hr] <;> ring

theorem original_index_character_whittaker
    (D : OriginalData) (k : BlockKey) (z : Row D k) (ha : D.block.atom.residue ≠ 0)
    (negativeM : Bool) {n : ℕ} (hn : n ∈ nCarrier D k z.val) {q : ℕ} [NeZero q]
    (hq : 0 < q) (h1 : q ≠ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ z.val) (s : ℂ) (y : ℝ) (hy : 0 < y) :
    let j := traceIndex D k negativeM z.val n
    let hN := (levelCarrier_licensed D k z.property).1
    fourierCoeff (sigmaOneSection z.val hN (oldform χ d s)
      (oldform_invariant hq h1 χ hχ z.val d hlevel s) y hy) j =
      (cuspOneR χ z.val (complement z.val q hN hq d hlevel) j s / (Real.sqrt |(j : ℝ)| : ℂ)) *
        (2*(Real.sqrt (|(j : ℝ)|*y) : ℂ)) * complexOrderK (s-1/2) (2*Real.pi*|(j : ℝ)|*y) :=
  physical_whittaker hq h1 χ hχ z.val _ d hlevel s y hy _
    (Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z.val hn ha))

private theorem complement_dvd (N q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ N) :
    (complement N q hN hq d hlevel : ℕ) ∣ N :=
  Nat.div_dvd_of_dvd hlevel

private theorem original_signed (D : OriginalData) (k : BlockKey) (negativeM : Bool) (n : ℕ) :
    principalTraceSign D k negativeM*(n : ℤ) = signed (traceNegative D k negativeM) n := by
  cases h : traceNegative D k negativeM <;> simp [principalTraceSign,signed,h]

private theorem cancel_phase {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (e : ℕ+) (n : ℤ) (s : ℂ) :
    sourceCuspPhase N (-n)*cuspOneR χ N e n s = χ (-1 : ZMod q)*(infinityK χ e n s/2) := by
  rw [cuspOneR,← mul_assoc,sourceCuspPhase_neg_mul_self,one_mul]

/-- Physical ABL removal for each true incoming character/dilation. The
outer numerator and both complementary-index divisibility tests are fixed
by the original occupied row. -/
theorem actual_character_row_removal
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) {q : ℕ} [NeZero q]
    (hq : 0 < q) (_h1 : q ≠ 1) (χ : DirichletCharacter ℂ q) (_hχ : χ.IsPrimitive)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ z.val) (s : ℂ) :
    let e := complement z.val q (levelCarrier_licensed D k z.property).1 hq d hlevel
    (∑ n ∈ nCarrier D k z.val, traceBeta D r k upper negativeM ell z.val n *
      cuspOneR χ z.val e (traceIndex D k negativeM z.val n) s) =
      pairAmplitude χ χ (D.block.atom.residue.natAbs*k.1) s *
      ∑ n ∈ nCarrier D k z.val, (modulatedBeta D r k upper ell z.val n *
        sourceCuspPhase z.val (-(principalTraceSign D k negativeM*(n : ℤ)))) *
        cuspOneR χ z.val e (principalTraceSign D k negativeM*(n : ℤ)) s := by
  let e := complement z.val q (levelCarrier_licensed D k z.property).1 hq d hlevel
  have he := complement_dvd z.val q (levelCarrier_licensed D k z.property).1 hq d hlevel
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [traceBeta_eq_principal_phase,traceIndex_eq_principalTraceSign,mul_assoc,cancel_phase]
  simp_rw [original_signed D k negativeM,halfK_signed]
  rw [original_row_character_pair_dilation_removal D k z χ χ (traceNegative D k negativeM)
    e he hn s]
  ring

/-- Exact squared divisor cost on the original finite residual coefficient
for every real t, including zero, before the separately required formal
oldclass Gram sum. -/
theorem actual_character_row_squared
    (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
    (upper negativeM : Bool) (ell : D4 → ℤ) {q : ℕ} [NeZero q]
    (hq : 0 < q) (h1 : q ≠ 1) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ z.val) (t : ℝ) :
    let s : ℂ := 1/2 + (t : ℂ)*I
    let e := complement z.val q (levelCarrier_licensed D k z.property).1 hq d hlevel
    ‖∑ n ∈ nCarrier D k z.val, traceBeta D r k upper negativeM ell z.val n *
      cuspOneR χ z.val e (traceIndex D k negativeM z.val n) s‖^2 ≤
      ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2 *
      ‖∑ n ∈ nCarrier D k z.val, (modulatedBeta D r k upper ell z.val n *
        sourceCuspPhase z.val (-(principalTraceSign D k negativeM*(n : ℤ)))) *
        cuspOneR χ z.val e (principalTraceSign D k negativeM*(n : ℤ)) s‖^2 := by
  dsimp only
  rw [actual_character_row_removal D r k z upper negativeM ell hq h1 χ hχ d hlevel,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (pairAmplitude_critical_norm_le_divisors χ χ (D.block.atom.residue.natAbs*k.1) t) 2)
    (sq_nonneg _)

end
end ImbalancedChen.Part3.OriginalCharacterTraceRow20261110
