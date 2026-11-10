import ImbalancedChen.Part3ActualCharacterPoissonRows
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Young (4.1)–(4.3) at infinity for every nontrivial primitive conductor
in the trivial-nebentypus class. Absolute integration starts on the
original horizontal segment of the genuine primitive lattice function.
The finite divisor expression continues each signed Fourier coefficient.
-/
namespace ImbalancedChen.Part3.ActualCharacterCompletedFourier20261110

noncomputable section
open Complex Set MeasureTheory UpperHalfPlane EisensteinSeries Filter
open scoped UpperHalfPlane BigOperators
open ActualCharacterLatticeCompletion20261110 ActualCharacterPoissonRows20261110
open RealEisensteinSeedConvergence CharacterEisensteinSeries CharacterEisensteinRowAction
open ActualEisensteinFourierInterchange20261025a PowerSeedFourierLaplaceFubini
open NativeCuspComplexPowerFourier20261027 ComplexOrderKBridgeSourceOnly
open ComplexOrderKEntire20261025a

private def pairVec : ℤ × ℤ ≃ Vec where
  toFun p := ![p.1,p.2]
  invFun v := (v 0,v 1)
  left_inv _ := rfl
  right_inv v := by ext i; fin_cases i <;> rfl

private def segment : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
private instance : IsFiniteMeasure segment := ⟨by simp [segment]⟩

def latticeFourier {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierPhase n x * latticeG hq χ s (horizontalPoint y hy x)

private theorem block_even {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Function.Even (fun c : ℤ => blockFourier hq χ c s y hy n) := by
  intro c
  unfold blockFourier
  apply intervalIntegral.integral_congr
  intro x _
  congr 1
  unfold block
  rw [← (Equiv.neg ℤ).tsum_eq (fun d : ℤ =>
    latticeTerm χ (scaledPoint q hq (horizontalPoint y hy x)) s ![-c,d])]
  apply tsum_congr
  intro d
  let z := scaledPoint q hq (horizontalPoint y hy x)
  change latticeTerm χ z s ![-c,-d] = latticeTerm χ z s ![c,d]
  have hv : (![-c,-d] : Vec) = -![c,d] := by ext i; fin_cases i <;> rfl
  have hbase : latticeBase z ![-c,-d] = latticeBase z ![c,d] := by
    simp only [latticeBase,Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_neg,
      neg_mul,← neg_add,norm_neg]
  simp only [latticeTerm,Matrix.cons_val_zero,Matrix.cons_val_one,characterWeight_neg]
  congr 1
  unfold latticeSeed
  rw [hbase]
  simp only [hv,neg_eq_zero]

private theorem block_zero {q : ℕ} (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    blockFourier hq χ 0 s y hy n = 0 := by
  simp [blockFourier,block,latticeTerm,characterWeight,χ.map_zero' h1]

/-- Absolute horizontal Fourier interchange for the character-weighted all-lattice
sum. Both positive and negative c are still present at this step. -/
theorem latticeFourier_all_c {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (n : ℤ) :
    Summable (fun c : ℤ => blockFourier hq χ c s y hy n) ∧
    latticeFourier hq χ s y hy n =
      (1/2 : ℂ) * ∑' c : ℤ, blockFourier hq χ c s y hy n := by
  classical
  let z (x : ℝ) := scaledPoint q hq (horizontalPoint y hy x)
  let F (p : ℤ × ℤ) (x : ℝ) := fourierPhase n x * latticeTerm χ (z x) s (pairVec p)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hY : 0 < (q : ℝ)*y := mul_pos hqR hy
  let C := ((q : ℝ)*y)^s.re *
    EisensteinSeries.r ⟨⟨(q : ℝ), (q : ℝ)*y⟩,hY⟩ ^ (-(2*s.re))
  let M (p : ℤ × ℤ) := C * ‖pairVec p‖ ^ (-(2*s.re))
  have hM : Summable M := pairVec.summable_iff.mpr
    ((EisensteinSeries.summable_one_div_norm_rpow (by linarith : 2 < 2*s.re)).mul_left C)
  have hbound (p : ℤ × ℤ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : ‖F p x‖ ≤ M p := by
    have him : (z x).im = (q : ℝ)*y := scaledPoint_im q hq _
    have hre : (z x).re = (q : ℝ)*x := by
      simpa [z,horizontalPoint,Complex.mul_re] using
        congrArg Complex.re (scaledPoint_coe q hq (horizontalPoint y hy x))
    have hz : z x ∈ UpperHalfPlane.verticalStrip (q : ℝ) ((q : ℝ)*y) := by
      change |(z x).re| ≤ (q : ℝ) ∧ (q : ℝ)*y ≤ (z x).im
      rw [hre,him,abs_of_nonneg (mul_nonneg hqR.le hx.1.le)]
      exact ⟨(mul_le_mul_of_nonneg_left hx.2 hqR.le).trans_eq (mul_one _),le_rfl⟩
    have H := seed_bound_on_boundedStrip s.re hs q ((q : ℝ)*y) ((q : ℝ)*y)
      hY (pairVec p) (z x) hz him.le
    rw [F,norm_mul,fourierPhase_norm,one_mul,latticeTerm,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (characterWeight_norm_le_one χ _ _)).trans
      ((norm_latticeSeed (z x) s hs (pairVec p)).le.trans H)
  have hmeas (p : ℤ × ℤ) : Measurable (F p) := by
    unfold F latticeTerm latticeSeed latticeBase
    split_ifs <;> simp only [z,scaledPoint_im,scaledPoint_coe,horizontalPoint,fourierPhase] <;>
      fun_prop
  have hmass : segment.real univ = 1 := by simp [segment,measureReal_def]
  have hbae (p : ℤ × ℤ) : ∀ᵐ x ∂segment, ‖F p x‖ ≤ M p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hbound p hx
  have hint (p : ℤ × ℤ) : Integrable (F p) segment :=
    Integrable.of_bound (hmeas p).aestronglyMeasurable (M p) (hbae p)
  have hnorm : Summable (fun p : ℤ × ℤ => ∫ x, ‖F p x‖ ∂segment) := by
    apply hM.of_nonneg_of_le (fun p => integral_nonneg (fun x => norm_nonneg _))
    intro p
    simpa only [integral_const,hmass,one_smul] using
      integral_mono_ae (hint p).norm (integrable_const (M p)) (hbae p)
  let a (p : ℤ × ℤ) := ∫ x, F p x ∂segment
  have ha : Summable a := (hnorm.of_nonneg_of_le (fun p => norm_nonneg (a p))
    (fun p => norm_integral_le_integral_norm _)).of_norm
  have hc (c : ℤ) : (∑' d : ℤ, a (c,d)) = blockFourier hq χ c s y hy n := by
    rw [blockFourier,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    change (∑' d : ℤ, ∫ x, F (c,d) x ∂segment) = _
    rw [integral_tsum_of_summable_integral_norm (fun d => hint (c,d)) (hnorm.prod_factor c)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [F,block,tsum_mul_left,pairVec,z,Equiv.coe_fn_mk]
  refine ⟨ha.prod.congr hc,?_⟩
  rw [latticeFourier,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    _ = ∫ x, (1/2 : ℂ) * ∑' p : ℤ × ℤ, F p x ∂segment := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold F latticeG
      rw [tsum_mul_left,pairVec.tsum_eq]
      ring
    _ = (1/2 : ℂ) * ∑' p : ℤ × ℤ, a p := by
      rw [integral_const_mul,← integral_tsum_of_summable_integral_norm hint hnorm]
    _ = _ := by rw [ha.tsum_prod]; simp_rw [hc]

theorem latticeFourier_nat_c {q : ℕ} (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    latticeFourier hq χ s y hy n = ∑' c : ℕ, blockFourier hq χ c s y hy n := by
  obtain ⟨hS,hE⟩ := latticeFourier_all_c hq χ s hs y hy n
  have h0 := block_zero hq h1 χ s y hy n
  rw [hE,tsum_int_eq_zero_add_two_mul_tsum_pnat (block_even hq χ s y hy n) hS,
    h0,zero_add,nsmul_eq_mul]
  have hp : (∑' c : ℕ+, blockFourier hq χ (c : ℕ) s y hy n) =
      ∑' c : ℕ, blockFourier hq χ c s y hy n :=
    tsum_pnat_eq_tsum_of_eq_zero (by simpa using h0)
  rw [hp]
  ring

def weightedDivisor {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) (s : ℂ) : ℂ :=
  ∑ c ∈ n.natAbs.divisors,
    χ (c : ZMod q) * star (χ ((n/(c : ℤ) : ℤ) : ZMod q)) * (c : ℂ)^(1-2*s)

/-- Young's signed divisor amplitude in the form |n|^(s−1/2)
Σ_{c||n|} χ(c) conjugate(χ(n/c)) c^(1−2s). -/
def amplitude {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) (s : ℂ) : ℂ :=
  ((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2) * weightedDivisor χ n s

def continuedCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ) (y : ℝ) (s : ℂ) : ℂ :=
  if n = 0 then 0 else 2 * (Real.sqrt y : ℂ) * amplitude χ n s *
    complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y)

theorem latticeFourier_zero {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) : latticeFourier hq χ s y hy 0 = 0 := by
  rw [latticeFourier_nat_c hq h1 χ s hs]
  apply tsum_eq_zero
  intro c
  by_cases hc : c = 0
  · subst c
    simpa using block_zero hq h1 χ s y hy 0
  · letI : NeZero c := ⟨hc⟩
    rw [positive_blockFourier c q hq χ hχ s hs]
    simp [χ.map_zero' h1]

theorem latticeFourier_divisor {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    latticeFourier hq χ s y hy n =
      (q : ℂ)^(-s) * gauss χ * weightedDivisor χ n s * nonzeroKExpression y n s := by
  rw [latticeFourier_nat_c hq h1 χ s hs]
  calc
    _ = ∑ c ∈ n.natAbs.divisors, blockFourier hq χ c s y hy n := by
      apply tsum_eq_sum
      intro c hc
      by_cases hc0 : c = 0
      · subst c
        simpa using block_zero hq h1 χ s y hy n
      · letI : NeZero c := ⟨hc0⟩
        have hnd : ¬ (c : ℤ) ∣ n := fun h => hc
          (Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp h,Int.natAbs_ne_zero.mpr hn⟩)
        rw [positive_blockFourier c q hq χ hχ s hs,if_neg hnd]
    _ = _ := by
      unfold weightedDivisor
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      have hc0 := (Nat.pos_of_mem_divisors hc).ne'
      letI : NeZero c := ⟨hc0⟩
      have hd := Int.natCast_dvd.mpr (Nat.dvd_of_mem_divisors hc : c ∣ n.natAbs)
      rw [positive_blockFourier c q hq χ hχ s hs,if_pos hd,actualPowerFourier_nonzero hy hn s hs,
        rowScale,sub_eq_add_neg (1 : ℂ) (2*s), Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hc0),
        Complex.cpow_one]
      ring

def completedPrimitive {q : ℕ} [NeZero q] (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (s : ℂ) (z : ℍ) : ℂ :=
  ((q : ℂ)^s / (Real.pi : ℂ)^s * Complex.Gamma s / gauss χ) *
    ((χ^2).LFunction (2*s) * characterEisenstein hq χ s z)

/-- The Fourier integral of Young's actual E* in its defining domain. The
conjugated second character is evaluated at the signed quotient n/c. -/
theorem physical_completed_coefficient {q : ℕ} [NeZero q] (hq : 0 < q) (h1 : q ≠ 1)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedPrimitive hq χ s (horizontalPoint y hy x)) = continuedCoefficient χ n y s := by
  let C := (q : ℂ)^s / (Real.pi : ℂ)^s * Complex.Gamma s / gauss χ
  have hfactor (x : ℝ) : fourierPhase n x * completedPrimitive hq χ s (horizontalPoint y hy x) =
      C * (fourierPhase n x * latticeG hq χ s (horizontalPoint y hy x)) := by
    rw [completedPrimitive,latticeG_eq_LFunction_mul hq χ _ _ hs]
    dsimp only [C]
    ring
  simp_rw [hfactor]
  rw [intervalIntegral.integral_const_mul]
  change C * latticeFourier hq χ s y hy n = _
  by_cases hn : n = 0
  · subst n
    rw [latticeFourier_zero hq h1 χ hχ s hs]
    simp [continuedCoefficient]
  · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hpC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [latticeFourier_divisor hq h1 χ hχ s hs y hy n hn,continuedCoefficient,if_neg hn,
      nonzeroKExpression,amplitude,Complex.cpow_neg]
    dsimp only [C]
    field_simp [show (q : ℂ)^s ≠ 0 from Complex.cpow_ne_zero_iff.mpr (.inl hqC),
      show (Real.pi : ℂ)^s ≠ 0 from Complex.cpow_ne_zero_iff.mpr (.inl hpC),
      Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re),gauss_ne_zero hχ] <;> ring

theorem continuedCoefficient_entire {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℤ)
    (y : ℝ) (hy : 0 < y) : Differentiable ℂ (continuedCoefficient χ n y) := by
  by_cases hn : n = 0
  · simpa [continuedCoefficient,hn] using (differentiable_const (c := (0 : ℂ)))
  · have hnr : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hp : Differentiable ℂ (fun s : ℂ => ((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2)) :=
      (differentiable_id.sub_const _).const_cpow (.inl (Complex.ofReal_ne_zero.mpr hnr.ne'))
    have hD : Differentiable ℂ (weightedDivisor χ n) := by
      unfold weightedDivisor
      apply Differentiable.fun_sum
      intro c hc
      have hcC : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hc).ne'
      exact differentiable_const.mul
        ((differentiable_const.sub (differentiable_id.const_mul (2 : ℂ))).const_cpow (.inl hcC))
    have hK := (complexOrderK_differentiable_all
      (show 0 < 2*Real.pi*|(n : ℝ)|*y by positivity)).comp (differentiable_id.sub_const (1/2 : ℂ))
    simpa only [continuedCoefficient,if_neg hn,amplitude] using
      ((differentiable_const.mul (hp.mul hD)).mul hK :
        Differentiable ℂ (fun s : ℂ => (2 * (Real.sqrt y : ℂ)) *
          (((|(n : ℝ)| : ℝ) : ℂ)^(s-1/2) * weightedDivisor χ n s) *
          complexOrderK (s-1/2) (2*Real.pi*|(n : ℝ)|*y)))

end
end ImbalancedChen.Part3.ActualCharacterCompletedFourier20261110
