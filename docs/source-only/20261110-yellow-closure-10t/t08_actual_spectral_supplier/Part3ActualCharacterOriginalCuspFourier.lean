import ImbalancedChen.Part3ActualCharacterCriticalFamily
import ImbalancedChen.Part3CharacterPairDivisorAmplitude
import ImbalancedChen.Part3ActualEisensteinPositiveCFourier
import ImbalancedChen.Part3LevelOldformFrickeIdentity
import ImbalancedChen.Part3ActualFrickeCuspPhase

/-!
The genuine dilated character family in the original two cusp frames.
At infinity use d, at cusp one use N/(q²d), the character parity,
and the original positive translation phase. The K radial coefficient
is computed by a physical Fourier integral without dividing by K.
-/
namespace ImbalancedChen.Part3.ActualCharacterOriginalCuspFourier20261110

noncomputable section
open Complex Set Filter MeasureTheory Matrix UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups BigOperators
open ActualCharacterCriticalFamily20261110 ActualCharacterCompletedFourier20261110
open ActualCharacterPoissonRows20261110 CharacterPairDivisorAmplitude20261102s
open CharacterEisensteinSeries CharacterEisensteinRowAction
open PrimitiveEisensteinParameterAnalytic PrimitiveEisensteinParameterAutomorphy
open PrimitiveRealEisensteinAutomorphy ActualEisensteinFourierInterchange20261025a
open ActualEisensteinPositiveCFourier20261025a PowerSeedFourierLaplaceFubini
open ComplexOrderKBridgeSourceOnly Gamma0DegeneracyMapSourceOnly
open FrickeNormalizer LevelOldformFricke20261026a ActualFrickeCuspPhase20261025a
open Gamma0ActualCuspsSourceOnly Gamma0GeneralCuspUnitPeriod20261025a

theorem amplitude_nat {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :
    amplitude χ (N : ℤ) s = pairAmplitude χ χ N s := by
  rw [amplitude,weightedDivisor,pairAmplitude_eq_divisor_pairs,Nat.sum_divisorsAntidiagonal]
  simp only [Int.natAbs_natCast,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg N),
    Complex.ofReal_natCast,← Int.natCast_ediv,Int.cast_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have hc0 : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hc).ne'
  have hd := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hc)
  have hN : (N : ℂ)^(s-1/2) =
      (c : ℂ)^(s-1/2)*((N/c : ℕ) : ℂ)^(s-1/2) := by
    conv_lhs => rw [← hd]
    rw [Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he : (c : ℂ)^(1/2-s) = (c : ℂ)^(s-1/2)*(c : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ hc0]
    congr 1
    ring
  rw [hN,he]
  ring

theorem amplitude_neg_nat {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (s : ℂ) :
    amplitude χ (-(N : ℤ)) s = χ (-1 : ZMod q)*pairAmplitude χ χ N s := by
  have hsign : star (χ (-1 : ZMod q)) = χ (-1) := by
    rcases χ.even_or_odd with h | h
    · change χ (-1) = 1 at h
      simp [h]
    · change χ (-1) = -1 at h
      simp [h]
  rw [← amplitude_nat χ N s]
  unfold amplitude weightedDivisor
  simp only [Int.cast_neg,abs_neg,Int.natAbs_neg,Int.natAbs_natCast]
  rw [mul_left_comm (χ _) _ _,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hcZ : (c : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hc).ne'
  have hfac : (N : ℤ) = (c : ℤ)*((N/c : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hc)).symm
  have hd : (-(N : ℤ))/(c : ℤ) = -((N/c : ℕ) : ℤ) := by
    conv_lhs => rw [hfac,← mul_neg,Int.mul_ediv_cancel_left _ hcZ]
  rw [hd,← Int.natCast_ediv]
  simp only [Int.cast_neg,Int.cast_natCast]
  rw [← neg_one_mul ((N/c : ℕ) : ZMod q),map_mul, star_mul',hsign]
  ring

/-- Reuse the S21 arithmetic estimate on the realized signed coefficient. -/
theorem realized_amplitude_critical_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℤ) (t : ℝ) :
    ‖amplitude χ n (1/2 + (t : ℂ)*I)‖ ≤ n.natAbs.divisors.card := by
  cases n with
  | ofNat N => simpa [amplitude_nat] using pairAmplitude_critical_norm_le_divisors χ χ N t
  | negSucc N =>
    change ‖amplitude χ (-((N+1 : ℕ) : ℤ)) _‖ ≤ ((N+1).divisors.card : ℝ)
    rw [amplitude_neg_nat,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
      (pairAmplitude_critical_norm_le_divisors χ χ _ t)

def oldform {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+) (s : ℂ) (z : ℍ) : ℂ :=
  primitiveFamily χ s (degeneracyDiagonal d d.pos • z)

theorem oldform_invariant {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (d : ℕ+)
    (hlevel : q^2*(d : ℕ) ∣ N) (s : ℂ) (g : SL(2,ℤ))
    (hg : g ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    oldform χ d s (g • z) = oldform χ d s z := by
  simp only [oldform,primitiveFamily,completed_oldform_invariant hq h1 χ hχ N d hlevel g hg z]

private theorem phase_product (n b : ℤ) (d : ℕ+) (x : ℝ) :
    fourierPhase n x * fourier b (((d : ℝ)*x : ℝ) : UnitAddCircle) =
      fourierPhase (n - ((d : ℕ) : ℤ)*b) x := by
  rw [fourier_coe_apply]
  unfold fourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem dilated_fourier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedFamily χ s (degeneracyDiagonal d d.pos • horizontalPoint y hy x)) =
        if ((d : ℕ) : ℤ) ∣ n then continuedCoefficient χ (n/(d : ℕ)) ((d : ℝ)*y) s else 0 := by
  let Y := (d : ℝ)*y
  have hY : 0 < Y := mul_pos (by exact_mod_cast d.pos) hy
  let A (b : ℤ) := continuedCoefficient χ b Y s
  let f (b : ℤ) (x : ℝ) := A b * fourierPhase (n - ((d : ℕ) : ℤ)*b) x
  have H (x : ℝ) : fourierPhase n x *
        completedFamily χ s (degeneracyDiagonal d d.pos • horizontalPoint y hy x) = ∑' b : ℤ, f b x := by
    have hco := degeneracyDiagonal_smul_coe d d.pos (horizontalPoint y hy x)
    have him : (degeneracyDiagonal d d.pos • horizontalPoint y hy x).im = Y := by
      simpa [Y,horizontalPoint,Complex.mul_im] using congrArg Complex.im hco
    have hre : (degeneracyDiagonal d d.pos • horizontalPoint y hy x).re = (d : ℝ)*x := by
      simpa [horizontalPoint,Complex.mul_re] using congrArg Complex.re hco
    rw [completedFamily,him,hre,← tsum_mul_left]
    apply tsum_congr
    intro b
    rw [mul_left_comm,phase_product]
  have hI (b : ℤ) : IntegrableOn (f b) (Ioc (0 : ℝ) 1) := by
    exact ((show Continuous (f b) by unfold f fourierPhase; fun_prop).intervalIntegrable 0 1).1
  have hnorm : Summable (fun b : ℤ => ∫ x in Ioc (0 : ℝ) 1, ‖f b x‖) := by
    simpa [f,A,norm_mul,fourierPhase_norm,measureReal_def] using coefficient_norm_summable χ Y hY s
  have Hzero (b : ℤ) : (∫ x in Ioc (0 : ℝ) 1, f b x) =
      if ((d : ℕ) : ℤ)*b = n then A b else 0 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [show (∫ x in (0 : ℝ)..1, f b x) = A b * ∫ x in (0 : ℝ)..1,
      fourierPhase (n - ((d : ℕ) : ℤ)*b) x from intervalIntegral.integral_const_mul _ _,
      integral_fourierPhase]
    by_cases h : ((d : ℕ) : ℤ)*b = n <;> simp [h,sub_eq_zero,eq_comm]
  simp_rw [H]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_tsum_of_summable_integral_norm hI hnorm]
  simp_rw [Hzero]
  by_cases h : ((d : ℕ) : ℤ) ∣ n
  · obtain ⟨b,hb⟩ := h
    have hd : ((d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast d.ne_zero
    have hu (j : ℤ) : ((d : ℕ) : ℤ)*j = n ↔ j = b := by rw [hb,mul_right_inj' hd]
    have hdiv : n/((d : ℕ) : ℤ) = b := by rw [hb,Int.mul_ediv_cancel_left _ hd]
    have h' : ((d : ℕ) : ℤ) ∣ n := ⟨b,hb⟩
    simp [hu,h',hdiv,A,Y]
  · have hz (b : ℤ) : ¬ ((d : ℕ) : ℤ)*b = n := fun hb => h ⟨b,hb.symm⟩
    simp [hz,h]

def infinityK {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (d : ℕ+)
    (n : ℤ) (s : ℂ) : ℂ :=
  if ((d : ℕ) : ℤ) ∣ n then
    2*(Real.sqrt (d : ℝ) : ℂ)*uncompletionFactor χ s*amplitude χ (n/(d : ℕ)) s else 0

/-- Infinity coefficient extracted from the actual native positive dilation.
It includes the signed frequency selection, sqrt(d) and original height. -/
theorem infinity_fourier {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (d : ℕ+) (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * oldform χ d s (horizontalPoint y hy x)) =
      (Real.sqrt y : ℂ) * infinityK χ d n s * complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y) := by
  have H (x : ℝ) : fourierPhase n x * oldform χ d s (horizontalPoint y hy x) =
      uncompletionFactor χ s * (fourierPhase n x * completedFamily χ s
        (degeneracyDiagonal d d.pos • horizontalPoint y hy x)) := by
    unfold oldform primitiveFamily
    ring
  simp_rw [H]
  rw [intervalIntegral.integral_const_mul,dilated_fourier,infinityK]
  split_ifs with h
  · have hd : ((d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast d.ne_zero
    obtain ⟨b,hb⟩ := h
    have hdiv : n/((d : ℕ) : ℤ) = b := by rw [hb,Int.mul_ediv_cancel_left _ hd]
    have hb0 : b ≠ 0 := fun h => hn (by simp [hb,h])
    have hc : |(n : ℝ)| = (d : ℝ)*|(b : ℝ)| := by
      rw [hb,Int.cast_mul,Int.cast_natCast,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      rfl
    rw [hdiv,continuedCoefficient,if_neg hb0,Real.sqrt_mul (by exact_mod_cast d.pos.le),hc,
      show 2*Real.pi*|(b : ℝ)|*((d : ℝ)*y) = 2*Real.pi*((d : ℝ)*|(b : ℝ)|)*y by ring]
    push_cast
    ring
  · ring

private theorem lattice_S {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (u v : ℍ) (hS : scaledPoint q hq u = ModularGroup.S • scaledPoint q hq v) (s : ℂ) :
    characterEisenstein hq χ s u = χ (-1 : ZMod q)*characterEisenstein hq χ s v := by
  let e := primitivePairEquiv ModularGroup.S
  have εsq : χ (-1 : ZMod q)*χ (-1) = 1 := by rw [← map_mul]; simp
  have hpair (p : PrimitivePair) : primitiveWeight χ (e p) = χ (-1)*primitiveWeight χ p := by
    have he := primitivePairEquiv_value ModularGroup.S p
    have ha : (e p).1 0 = p.1 1 := by
      simpa [e,vecMul,dotProduct,Fin.sum_univ_two,ModularGroup.coe_S] using congrFun he 0
    have hb : (e p).1 1 = -p.1 0 := by
      simpa [e,vecMul,dotProduct,Fin.sum_univ_two,ModularGroup.coe_S] using congrFun he 1
    simp only [primitiveWeight,characterWeight,ha,hb,Int.cast_neg]
    rw [← neg_one_mul (p.1 0 : ZMod q),map_mul]
    ring
  have H (p : PrimitivePair) : characterSeed hq χ u p s =
      χ (-1) * characterSeed hq χ v (e p) s := by
    rw [characterSeed,characterSeed,hS,complexSeed_SL2_apply,hpair]
    change _ = χ (-1) * ((χ (-1)*_) * complexSeed _ (e p) s)
    rw [← mul_assoc,← mul_assoc,εsq,one_mul]
  unfold characterEisenstein
  simp_rw [H,tsum_mul_left]
  rw [e.tsum_eq]
  ring

def complement (N q : ℕ) (hN : 0 < N) (hq : 0 < q) (d : ℕ+)
    (hlevel : q^2*(d : ℕ) ∣ N) : ℕ+ :=
  ⟨N/(q^2*(d : ℕ)),Nat.div_pos (Nat.le_of_dvd hN hlevel) (mul_pos (pow_pos hq 2) d.pos)⟩

theorem oldform_fricke {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (hN : 0 < N)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ N) (s : ℂ) (z : ℍ) :
    oldform χ d s (frickeSL N hN • z) =
      χ (-1 : ZMod q)*oldform χ (complement N q hN hq d hlevel) s z := by
  let e := complement N q hN hq d hlevel
  let u := degeneracyDiagonal d d.pos • (frickeSL N hN • z)
  let v := degeneracyDiagonal e e.pos • z
  have hNfac : (N : ℂ) = (q : ℂ)^2*(d : ℕ)*(e : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hlevel).symm
  have hS : scaledPoint q hq u = ModularGroup.S • scaledPoint q hq v := by
    apply UpperHalfPlane.ext
    rw [scaledPoint_coe,UpperHalfPlane.modular_S_smul]
    change (q : ℂ)*(u : ℂ) = (-((scaledPoint q hq v : ℍ) : ℂ))⁻¹
    rw [scaledPoint_coe]
    simp only [u,v,degeneracyDiagonal_smul_coe,fricke_action_coe,hNfac,inv_neg]
    field_simp [z.ne_zero,show (q : ℂ) ≠ 0 by exact_mod_cast hq.ne',
      show ((d : ℕ) : ℂ) ≠ 0 by exact_mod_cast d.ne_zero,
      show ((e : ℕ) : ℂ) ≠ 0 by exact_mod_cast e.ne_zero] <;> ring
  have hE : (fun w => completedFamily χ w u) =ᶠ[𝓝 (2 : ℂ)]
      (fun w => χ (-1 : ZMod q)*completedFamily χ w v) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    rw [completedFamily_initial hq h1 χ hχ w hw,completedFamily_initial hq h1 χ hχ w hw,
      completedPrimitive,completedPrimitive,lattice_S hq χ u v hS w]
    ring
  have hF : AnalyticOnNhd ℂ (fun w => completedFamily χ w u) univ :=
    (completedFamily_entire χ u).differentiableOn.analyticOnNhd isOpen_univ
  have hG : AnalyticOnNhd ℂ (fun w => χ (-1 : ZMod q)*completedFamily χ w v) univ :=
    ((completedFamily_entire χ v).const_mul _).differentiableOn.analyticOnNhd isOpen_univ
  change uncompletionFactor χ s * completedFamily χ s u =
    χ (-1) * (uncompletionFactor χ s * completedFamily χ s v)
  rw [congrFun (hF.eq_of_eventuallyEq hG hE) s]
  ring

/-- The second original cusp coefficient, obtained from the repaired R22 true
sigma-one frame. Its positive translation phase is retained at signed n. -/
theorem original_cuspOne_fourier {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (N : ℕ) (hN : 0 < N)
    (d : ℕ+) (hlevel : q^2*(d : ℕ) ∣ N) (s : ℂ) (y : ℝ) (hy : 0 < y)
    (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff (sigmaOneSection N hN (oldform χ d s)
      (oldform_invariant hq h1 χ hχ N d hlevel s) y hy) n =
      Complex.exp (2*Real.pi*I*(n : ℂ)/(N : ℂ)) * χ (-1 : ZMod q) *
      ((Real.sqrt y : ℂ)*infinityK χ (complement N q hN hq d hlevel) n s *
        complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y)) := by
  let e := complement N q hN hq d hlevel
  let HΓ := oldform_invariant hq h1 χ hχ N d hlevel s
  have HH (x : ℝ) : frickeSection N hN (oldform χ d s) HΓ y hy (x : UnitAddCircle) =
      χ (-1 : ZMod q)*oldform χ e s (horizontalPoint y hy x) :=
    oldform_fricke hq h1 χ hχ N hN d hlevel s _
  rw [sigmaOne_fourierCoeff_fricke_phase,frickeFourierCoeff,
    fourierCoeff_eq_intervalIntegral _ n (0 : ℝ)]
  simp only [div_one,one_smul,zero_add,smul_eq_mul,PowerSeedPeriodization.native_fourier_phase,HH]
  simp_rw [mul_left_comm (fourierPhase n _) (χ (-1 : ZMod q))]
  rw [intervalIntegral.integral_const_mul,infinity_fourier χ e s y hy n hn]
  ring

end
end ImbalancedChen.Part3.ActualCharacterOriginalCuspFourier20261110
