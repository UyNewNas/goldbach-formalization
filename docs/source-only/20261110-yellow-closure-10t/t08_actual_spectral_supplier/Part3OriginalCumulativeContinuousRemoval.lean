import ImbalancedChen.Part3OriginalContinuousCuspGram

/-! Actual compact-height cumulative continuous removal, with the
Drappeau dt/cosh(πt) weight and the original native 1/(4π) normalization.
Integrability of every input follows from the explicit physical amplitudes
through the principal center. -/
namespace ImbalancedChen.Part3.OriginalCumulativeContinuousRemoval20261110

noncomputable section
open Complex Set Filter Topology Matrix MeasureTheory
open scoped BigOperators UpperHalfPlane MatrixGroups
open OriginalContinuousCuspGram20261110 OriginalContinuousClassRemoval20261110
open ActualContinuousClassFourier20261110 ActualOrdinaryContinuousModes20261110
open ActualYoungCriticalProjection20261110 ActualYoungFormalClass20261110
open ActualYoungDilationInverse20261110 ActualYoungCuspCoefficients20261110
open ActualCuspDenominatorClasses20261110 ActualCriticalCuspEvaluation20261110
open ActualCharacterCompletedFourier20261110 ActualCharacterCriticalFamily20261110
open ActualCharacterOriginalCuspFourier20261110 ActualYoungCriticalCusps20261110
open ActualPrincipalOldformRemoval20261102r ActualPrincipalCuspOneRemoval20261102r
open NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open OriginalNativeCuspFunctionals20261102 OriginalSignedTraceInput20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 P3NativePeriod64SamplingSourceOnly (D4)

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

private theorem point_cont : Continuous criticalPoint := by unfold criticalPoint; fun_prop

private theorem const_power {α : Type*} [TopologicalSpace α] {s : α → ℂ}
    (hs : Continuous s) (c : ℂ) (hc : c ≠ 0) : Continuous (fun x => c^(s x)) :=
  (show Differentiable ℂ (fun u : ℂ => c^u) from fun _ => differentiableAt_id.const_cpow (.inl hc)).continuous.comp hs

private theorem reciprocal_cont {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t => reciprocalL χ (2*criticalPoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have ht : 1 ≤ (2*criticalPoint t).re := by norm_num [criticalPoint,Complex.mul_re]
  exact (reciprocalL_differentiableAt χ _ ht).continuousAt.comp (continuous_const.mul point_cont).continuousAt

private theorem principal_cont : Continuous (fun t => principalFactor (criticalPoint t)) := by
  simp only [principalFactor,div_eq_mul_inv]
  exact ((const_power point_cont _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mul
    (Complex.differentiable_one_div_Gamma.continuous.comp point_cont)).mul (reciprocal_cont _)

private theorem uncompletion_cont {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Continuous (fun t => uncompletionFactor χ (criticalPoint t)) := by
  let hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hden (t : ℝ) : (q : ℂ)^(criticalPoint t) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hq)
  unfold uncompletionFactor
  simp only [div_eq_mul_inv]
  exact (((((const_power point_cont _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).mul
    ((const_power point_cont _ hq).inv₀ hden)).mul continuous_const).mul
      (Complex.differentiable_one_div_Gamma.continuous.comp point_cont)).mul (reciprocal_cont _)

private theorem principal_amp_cont (n : ℕ) : Continuous (fun t => normalizedDivisorAmplitude n (criticalPoint t)) := by
  by_cases hn : n = 0
  · simp [hn,normalizedDivisorAmplitude,divisorFactor]
  · have hnum := const_power (point_cont.sub continuous_const) (n : ℂ) (Nat.cast_ne_zero.mpr hn)
    unfold normalizedDivisorAmplitude divisorFactor
    apply hnum.mul
    apply continuous_finsetSum
    intro d hd
    exact const_power (continuous_const.sub (continuous_const.mul point_cont)) _
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')

private theorem char_amp_cont {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) :
    Continuous (fun t => amplitude χ n (criticalPoint t)) := by
  by_cases hn : n = 0
  · simp [hn,amplitude,weightedDivisor]
  · have hnr : (|(n : ℝ)| : ℝ) ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
    unfold amplitude weightedDivisor
    apply (const_power (point_cont.sub continuous_const) _ (Complex.ofReal_ne_zero.mpr hnr)).mul
    apply continuous_finsetSum
    intro d hd
    exact continuous_const.mul (const_power (continuous_const.sub (continuous_const.mul point_cont)) _
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'))

private theorem infR_cont {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+) (n : ℤ) :
    Continuous (infR χ d n) := by
  unfold infR
  by_cases h : q = 1
  · simp only [if_pos h,principalDilationAmplitude]
    by_cases hd : (d : ℕ) ∣ n.natAbs
    · simp only [if_pos hd]
      exact principal_cont.mul (continuous_const.mul (principal_amp_cont _))
    · simpa only [if_neg hd,mul_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · simp only [if_neg h,infinityK]
    by_cases hd : ((d : ℕ) : ℤ) ∣ n
    · simp only [if_pos hd]
      exact ((continuous_const.mul (uncompletion_cont χ)).mul (char_amp_cont χ _)).div_const _
    · simp [hd]

private theorem dilationR_cont {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (N : ℕ) (hN : 0 < N) (d : ℕ+) (hle : q^2*(d : ℕ) ∣ N) (one : Bool) (n : ℤ) :
    Continuous (dilationR χ N hN d hle one n) := by
  cases one
  · exact infR_cont χ d n
  · exact continuous_const.mul (continuous_const.mul (infR_cont χ _ n))

private theorem coefficient_cont {q L : ℕ} (χ : DirichletCharacter ℂ q) (hL : 0 < L) (j b : Div L) :
    Continuous (fun t => dilationCoefficient χ (criticalPoint t) j b) := by
  classical
  let A := fun t => kernelMatrix χ (criticalPoint t) L
  have hentry (i k : Div L) : Continuous (fun t => A t i k) := by
    have ht (d : ℕ) : Continuous (fun t => twist χ (criticalPoint t) d) := by
      unfold twist posPower
      exact continuous_const.mul ((point_cont.neg.mul continuous_const).cexp)
    exact (ht _).mul (ht _)
  have hc : Continuous A := continuous_pi (fun i => continuous_pi (hentry i))
  have hu : Continuous (fun t => (A t).updateRow b (Pi.single j 1)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro k
    by_cases h : i = b
    · subst i
      simpa only [Matrix.updateRow_self] using (continuous_const : Continuous (fun _ : ℝ => Pi.single j (1 : ℂ) k))
    · simpa only [Matrix.updateRow_ne h] using hentry i k
  have hlevel : Continuous (fun t => levelFactor (q^2*L) (q*j.1) (criticalPoint t)) :=
    (point_cont.mul continuous_const).cexp
  have hden (t : ℝ) : (A t).det*levelFactor (q^2*L) (q*j.1) (criticalPoint t) ≠ 0 :=
    mul_ne_zero (kernel_det_ne_zero χ (by norm_num [criticalPoint,Complex.mul_re]) L hL) (Complex.exp_ne_zero _)
  simpa only [dilationCoefficient,Matrix.adjugate_apply,A] using hu.matrix_det.div (hc.matrix_det.mul hlevel) hden

theorem channelR_cont {N : ℕ} [NeZero N] (i : CharacterSlots N) (one : Bool) (n : ℤ) :
    Continuous (channelR i one n) := by
  letI : NeZero i.2.conductor := ⟨i.2.conductor_ne_zero⟩
  unfold channelR
  apply continuous_finsetSum
  intro b _
  exact (coefficient_cont _ (originalSlot i).pos _ _).mul (dilationR_cont _ N (NeZero.pos N) _ (legal (originalSlot i) b) one n)

theorem nativeR_cont {N : ℕ} [NeZero N] (a : Parameters N) (one : Bool) (n : ℤ) :
    Continuous (nativeR a one n) := by
  unfold nativeR
  apply continuous_finsetSum
  intro ξ _
  exact continuous_const.mul (channelR_cont (⟨a.1,ξ⟩ : CharacterSlots N) one n)

theorem marked_density_cont (N : ℕ) [NeZero N] (S : Finset ℕ) (w : ℕ → ℂ)
    (ind : ℕ → ℤ) (one : Bool) :
    Continuous (fun t => nativeMass N (fun a => markedRow S w ind (fun n => nativeR a one n t))/
      Real.cosh (Real.pi*t)) := by
  have hm (a : Parameters N) : Continuous (fun t => markedRow S w ind (fun n => nativeR a one n t)) := by
    unfold markedRow
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul (nativeR_cont a one _)
  apply Continuous.div _ (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) (fun t => (Real.cosh_pos _).ne')
  unfold nativeMass
  apply continuous_finsetSum
  intro a _
  exact ((hm a).norm.pow 2).div_const _

/-- Actual finite [lo,hi] cumulative bound. Both compact-window
integrals are finite Bochner integrals of continuous real functions.
The interval [-T,T] needs exactly T≥0. -/
theorem original_cumulative_removal (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey)
    (z : Row D k) (upper negativeM : Bool) (ell : D4 → ℤ) (lo hi : ℝ) (hwin : lo ≤ hi) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    (∫ t in lo..hi, nativeMass z.val (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t))/
      Real.cosh (Real.pi*t)) ≤ ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2*
      ∫ t in lo..hi, nativeMass z.val (fun a => reduced D r k z upper negativeM ell (fun n => nativeR a true n t))/
      Real.cosh (Real.pi*t) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  let C : ℝ := ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2
  let F := fun t => nativeMass z.val (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t))
  let G := fun t => nativeMass z.val (fun a => reduced D r k z upper negativeM ell (fun n => nativeR a true n t))
  have hF : Continuous (fun t => F t/Real.cosh (Real.pi*t)) := marked_density_cont _ _ _ _ _
  have hG : Continuous (fun t => G t/Real.cosh (Real.pi*t)) := marked_density_cont _ _ _ _ _
  change (∫ t in lo..hi, F t/Real.cosh (Real.pi*t)) ≤ C*∫ t in lo..hi,G t/Real.cosh (Real.pi*t)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hwin (hF.intervalIntegrable lo hi) ((continuous_const.mul hG).intervalIntegrable lo hi)
  intro t _
  have H : F t ≤ C*G t := original_native_removal D r k z upper negativeM ell t
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right H (Real.cosh_pos _).le

/-- Nonzero physical S20 indices of this exact completed m/n input. -/
theorem original_physical_modes (D : OriginalData) (k : BlockKey) (z : Row D k)
    (ha : D.block.atom.residue ≠ 0) (negativeM : Bool) (J j : ℕ)
    {p n : ℕ} (hp : p ∈ commonMBlock J j) (hn : n ∈ nCarrier D k z.val)
    (t y : ℝ) (hy : 0 < y) :
    letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
    ∀ a : Parameters z.val,
      sectionMode z.val (NeZero.pos z.val) false (physicalFamily z.val t a) (p : ℤ) y hy =
        radial (p : ℤ) t y*nativeR a false (p : ℤ) t ∧
      fourierCoeff (ActualFrickeCuspPhase20261025a.sigmaOneSection z.val (NeZero.pos z.val) (physicalFamily z.val t a)
        (native_invariant a t) y hy) (traceIndex D k negativeM z.val n) =
        radial (traceIndex D k negativeM z.val n) t y*nativeR a true (traceIndex D k negativeM z.val n) t := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  intro a
  have hp0 : 0 < p := lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℕ) < 2) j) (Finset.mem_Ico.mp hp).1
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hnz := Int.natAbs_pos.mp (traceIndex_natAbs_pos D k negativeM z.val hn ha)
  exact ⟨by simpa only [cuspFamily,Equiv.symm_apply_apply,physicalFamily] using native_mode a false (p : ℤ) hpz t y hy,
    native_sigmaOne a _ hnz t y hy⟩

end
end ImbalancedChen.Part3.OriginalCumulativeContinuousRemoval20261110

