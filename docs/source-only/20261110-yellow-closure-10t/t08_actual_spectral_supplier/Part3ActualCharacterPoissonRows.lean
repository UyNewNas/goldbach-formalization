import ImbalancedChen.Part3ActualCharacterLatticeCompletion
import ImbalancedChen.Part3NativeCuspComplexPeriodization
import ImbalancedChen.Part3ActualEisensteinFourierInterchange
import Mathlib.Analysis.Fourier.ZMod

/-!
Positive first-coordinate rows of Young's unrestricted series (3.8).
The signed integer Fourier mode is taken on the physical unit horocycle.
The two finite residues come from d = v + q (u + c k).
-/
namespace ImbalancedChen.Part3.ActualCharacterPoissonRows20261110

noncomputable section
open Complex Set MeasureTheory UpperHalfPlane
open scoped BigOperators UpperHalfPlane FourierTransform
open ActualCharacterLatticeCompletion20261110 CharacterEisensteinSeries
open CharacterEisensteinRowAction ActualEisensteinFourierInterchange20261025a
open PowerSeedFourierLaplaceFubini NativeCuspComplexPowerFourier20261027
open NativeCuspComplexPeriodization20261027

private def residueEquiv (m : ℕ) [NeZero m] : ZMod m × ℤ ≃ ℤ :=
  Equiv.ofBijective (fun p => (p.1.val : ℤ) + (m : ℤ)*p.2) (by
    constructor
    · intro p r h
      have hr : p.1 = r.1 := by
        simpa using congrArg (fun z : ℤ => (z : ZMod m)) h
      change (p.1.val : ℤ) + (m : ℤ)*p.2 = (r.1.val : ℤ) + (m : ℤ)*r.2 at h
      rw [hr] at h
      exact Prod.ext hr (mul_left_cancel₀ (by exact_mod_cast NeZero.ne m : (m : ℤ) ≠ 0)
        (add_left_cancel h))
    · intro d
      obtain ⟨k,hk⟩ := (ZMod.intCast_eq_iff m d (d : ZMod m)).mp rfl
      exact ⟨((d : ZMod m), k), hk.symm⟩)

private def doubleResidueEquiv (c q : ℕ) [NeZero c] [NeZero q] :
    (ZMod q × ZMod c) × ℤ ≃ ℤ :=
  (Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl _) (residueEquiv c)).trans (residueEquiv q))

def shift (c q : ℕ) (p : ZMod q × ZMod c) : ℝ :=
  (p.1.val : ℝ) / ((c : ℝ)*q) + (p.2.val : ℝ) / c

def rowScale (c q : ℕ) (s : ℂ) : ℂ :=
  (c : ℂ)^(-(2*s)) * (q : ℂ)^(-s)

def block {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (c : ℤ)
    (s : ℂ) (y : ℝ) (hy : 0 < y) (x : ℝ) : ℂ :=
  ∑' d : ℤ, latticeTerm χ (scaledPoint q hq (horizontalPoint y hy x)) s ![c,d]

def blockFourier {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (c : ℤ)
    (s : ℂ) (y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierPhase n x * block hq χ c s y hy x

private theorem positive_seed (q c : ℕ) [NeZero c] (hq : 0 < q) (s : ℂ)
    (d : ℤ) (x y : ℝ) (hy : 0 < y) :
    latticeSeed (scaledPoint q hq (horizontalPoint y hy x)) s ![(c : ℤ),d] =
      rowScale c q s * complexPowerSeed y s (x + (d : ℝ)/((c : ℝ)*q)) := by
  have hc : 0 < (c : ℝ) := by exact_mod_cast NeZero.pos c
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hv : (![(c : ℤ),d] : Vec) ≠ 0 := by
    intro h
    have h0 : (c : ℤ) = 0 := congrFun h 0
    exact (NeZero.ne c) (by exact_mod_cast h0)
  let u := x + (d : ℝ)/((c : ℝ)*q)
  have hlin : (c : ℂ)*((q : ℂ)*(horizontalPoint y hy x : ℂ)) + (d : ℂ) =
      ((c : ℂ)*q)*(horizontalPoint y hy u : ℂ) := by
    apply Complex.ext <;> simp [horizontalPoint,u,Complex.mul_re,Complex.mul_im] <;>
      field_simp [hc.ne',hqR.ne'] <;> ring
  have hnorm : ‖(horizontalPoint y hy u : ℂ)‖^2 = u^2+y^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,horizontalPoint,pow_two]
  have hb : latticeBase (scaledPoint q hq (horizontalPoint y hy x)) ![(c : ℤ),d] =
      powerBase y u / ((c : ℝ)^2*q) := by
    unfold latticeBase powerBase
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_natCast,
      scaledPoint_im,scaledPoint_coe,hlin,norm_mul,Complex.norm_natCast,mul_pow,hnorm]
    change (q : ℝ)*y / ((c^2*q^2 : ℝ)*(u^2+y^2)) =
      y/(u^2+y^2) / ((c : ℝ)^2*q)
    field_simp [hc.ne',hqR.ne',show u^2+y^2 ≠ 0 by positivity] <;> ring
  have hclog : Complex.log (c : ℂ) = (Real.log (c : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hc.le).symm
  have hqlog : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hqR.le).symm
  rw [latticeSeed,if_neg hv,hb,Real.log_div (powerBase_pos hy u).ne' (by positivity),
    Real.log_mul (pow_ne_zero _ hc.ne') hqR.ne',Real.log_pow,rowScale,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hc.ne' : (c : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne' : (q : ℂ) ≠ 0),
    hclog,hqlog,complexPowerSeed,← Complex.exp_add,← Complex.exp_add]
  congr 1
  dsimp only [u]
  push_cast
  ring

/-- Reindex the literal full second coordinate, with every residue and translate. -/
theorem positive_block_periodization (c q : ℕ) [NeZero c] [NeZero q]
    (hq : 0 < q) (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    block hq χ c s y hy x = χ (c : ZMod q) * rowScale c q s *
      ∑ p : ZMod q × ZMod c, χ p.1 * periodizedComplexPowerSeed y s (x + shift c q p) := by
  let e := doubleResidueEquiv c q
  let z := scaledPoint q hq (horizontalPoint y hy x)
  have hsum : Summable (fun d : ℤ => latticeTerm χ z s ![(c : ℤ),d]) :=
    (latticeTerm_norm_summable χ z s hs).of_norm.comp_injective
      (fun _ _ h => congrFun h 1)
  have harg (p : ZMod q × ZMod c) (k : ℤ) :
      x + (e (p,k) : ℝ)/((c : ℝ)*q) = (x + shift c q p) + k := by
    change x + (((p.1.val : ℤ) + (q : ℤ)*((p.2.val : ℤ)+(c : ℤ)*k) : ℤ) : ℝ) /
        ((c : ℝ)*q) = _
    unfold shift
    push_cast
    field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne',
      show (c : ℝ) ≠ 0 by exact_mod_cast NeZero.ne c] <;> ring
  have hterm (p : ZMod q × ZMod c) (k : ℤ) :
      latticeTerm χ z s ![(c : ℤ),e (p,k)] =
        (χ (c : ZMod q)*rowScale c q s)*χ p.1 *
          complexPowerSeed y s ((x + shift c q p) + k) := by
    have he : ((e (p,k) : ℤ) : ZMod q) = p.1 := by
      change (((p.1.val : ℤ) + (q : ℤ)*((p.2.val : ℤ)+(c : ℤ)*k) : ℤ) : ZMod q) = _
      simp
    rw [latticeTerm,positive_seed q c hq s _ x y hy,harg,characterWeight]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_natCast,he]
    ring
  unfold block
  change (∑' d : ℤ, latticeTerm χ z s ![(c : ℤ),d]) = _
  rw [← e.tsum_eq, (e.summable_iff.mpr hsum).tsum_prod,tsum_fintype]
  simp_rw [hterm,tsum_mul_left]
  simp only [periodizedComplexPowerSeed,Finset.mul_sum,mul_assoc]

private theorem phase_residue (m : ℕ) [NeZero m] (b : ℤ) (r : ZMod m) :
    fourierPhase (-b) ((r.val : ℝ)/m) = ZMod.stdAddChar ((b : ZMod m)*r) := by
  have he : (b : ZMod m)*r = ((b*(r.val : ℤ) : ℤ) : ZMod m) := by simp
  rw [he,ZMod.stdAddChar_coe]
  unfold fourierPhase
  congr 1
  push_cast
  ring

private theorem phase_add (n : ℤ) (x y : ℝ) :
    fourierPhase n (x+y) = fourierPhase n x * fourierPhase n y := by
  unfold fourierPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  gaussSum χ ZMod.stdAddChar

theorem gauss_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : gauss χ ≠ 0 := by
  intro h
  have hF : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
    ext k
    simpa [gauss] using (hχ.fourierTransform_eq_inv_mul_gaussSum k).trans
      (by rw [show gaussSum χ ZMod.stdAddChar = 0 from h,mul_zero])
  have h0 : (χ : ZMod q → ℂ) = 0 := ZMod.dft.injective (by simpa using hF)
  simpa using congrFun h0 1

private theorem phase_sum (c q : ℕ) [NeZero c] [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ℤ) :
    (∑ p : ZMod q × ZMod c, χ p.1 * fourierPhase (-n) (shift c q p)) =
      if (c : ℤ) ∣ n then (c : ℂ)*star (χ ((n/(c : ℤ) : ℤ) : ZMod q))*gauss χ
      else 0 := by
  classical
  have hu : (∑ u : ZMod c, fourierPhase (-n) ((u.val : ℝ)/c)) =
      if (c : ℤ) ∣ n then (c : ℂ) else 0 := by
    simp_rw [phase_residue c n, mul_comm (n : ZMod c)]
    rw [AddChar.sum_mulShift (n : ZMod c) (ZMod.isPrimitive_stdAddChar c)]
    simp only [ZMod.card,ZMod.intCast_zmod_eq_zero_iff_dvd]
  calc
    _ = (∑ v : ZMod q, χ v * fourierPhase (-n) ((v.val : ℝ)/((c : ℝ)*q))) *
        (∑ u : ZMod c, fourierPhase (-n) ((u.val : ℝ)/c)) := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [shift,phase_add,mul_assoc]
    _ = _ := by
      rw [hu]
      split_ifs with hd
      · obtain ⟨b,hb⟩ := hd
        have hdiv : n/(c : ℤ) = b := by
          rw [hb,Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne c)]
        have hp (v : ZMod q) : fourierPhase (-n) ((v.val : ℝ)/((c : ℝ)*q)) =
            ZMod.stdAddChar ((b : ZMod q)*v) := by
          rw [← phase_residue, hb]
          unfold fourierPhase
          congr 1
          push_cast
          field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast NeZero.ne c,
            show (q : ℝ) ≠ 0 by exact_mod_cast NeZero.ne q] <;> ring
        have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (b : ZMod q)
        simp_rw [hp]
        rw [hdiv,MulChar.star_apply']
        change gaussSum χ (ZMod.stdAddChar.mulShift (b : ZMod q)) * c = _
        rw [hg,gauss]
        ring
      · exact mul_zero _

/-- Complete Gauss evaluation of each physical row, with the actual signed
frequency and divisor selection. The transform is the full-line integral
of the original seed after unfolding. -/
theorem positive_blockFourier (c q : ℕ) [NeZero c] [NeZero q] (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs : 1 < s.re)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    blockFourier hq χ c s y hy n =
      if (c : ℤ) ∣ n then χ (c : ZMod q) * rowScale c q s *
        ((c : ℂ)*star (χ ((n/(c : ℤ) : ℤ) : ZMod q))*gauss χ) * actualPowerFourier y n s
      else 0 := by
  classical
  let A := χ (c : ZMod q)*rowScale c q s
  have hpoint (x : ℝ) : fourierPhase n x * block hq χ c s y hy x =
      A * ∑ p : ZMod q × ZMod c, χ p.1 *
        (fourierPhase n x * periodizedComplexPowerSeed y s (x + shift c q p)) := by
    rw [positive_block_periodization c q hq χ s hs]
    dsimp only [A]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  calc
    _ = A * ∑ p : ZMod q × ZMod c, χ p.1 *
        (fourierPhase (-n) (shift c q p)*actualPowerFourier y n s) := by
      unfold blockFourier
      simp_rw [hpoint]
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum
        (fun p _ => (shifted_complex_phase_integrable hy s hs n (shift c q p)).const_mul (χ p.1))]
      simp_rw [intervalIntegral.integral_const_mul,shifted_periodizedComplexPowerSeed_fourier hy s hs]
    _ = _ := by
      simp_rw [← mul_assoc (χ _) _ (actualPowerFourier y n s)]
      rw [← Finset.sum_mul,phase_sum c q χ hχ n]
      split_ifs <;> simp [A,mul_assoc]

end
end ImbalancedChen.Part3.ActualCharacterPoissonRows20261110
