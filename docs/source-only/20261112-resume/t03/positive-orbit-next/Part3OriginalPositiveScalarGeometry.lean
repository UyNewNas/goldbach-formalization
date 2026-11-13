import ImbalancedChen.Part3OriginalPositiveHeightTest
import ImbalancedChen.Part3OriginalPrescribedAbelOrbit
import ImbalancedChen.Part3OriginalOppositeMarkedKuznetsov
import ImbalancedChen.Part3OriginalPositiveStripDiagonal
import Batteries.Tactic.OpenPrivate

/-! The original conjugated positive Bruhat integral and its physical identity
cell. The constructions are linear in H(a,b) = ψ(a) star(φ(b)). -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (e spectralTest)
open OriginalAbelGaussian (dilation productAt)
open OriginalAbelOrbit (heights)
open ActualMarkedBruhatTest20261112 (orbitTest orbitTestKernel)
open ActualMarkedGeometricSeries20261112 (pairDiagonal)
open ActualCuspOneGeometricPairing20261112 (sourceDiagonal)
open CompactCuspGeometricFubini20261025a (radialWeight)
open OriginalContinuousPoincarePackets20261110 (scaledSeed)
open RadialSchrodingerL2Form20261025a (RadialTest)
open OriginalPositiveRatioWindows20261112 (unit unit_mass ratio ratio_pointwise)
open OriginalPositiveHeightTest20261112 (height height_exp original)
open OriginalPositiveStrip20261112 (half_at_zero)
open ActualPositiveHolomorphicDiagonal20261112 (diagonalMoment)
open private height_integral from ImbalancedChen.Part3OriginalAbelOrbit

def plane (H : ℝ→ℝ→ℂ) (k x a : ℝ) : ℂ :=
  ((a⁻¹)^2:ℝ) • (H a (k*a/(x^2+a^2))*e (x+k*x/(x^2+a^2)))

def induced (H : ℝ→ℝ→ℂ) (q : ℝ) :=
  (4*Real.pi/q:ℝ) • (∫ x : ℝ,∫ a,plane H ((q/(4*Real.pi))^2) x a ∂heights)

theorem rank_one (ψ φ : ℝ→ℂ) (hpψ : tsupport ψ⊆Ioi (0:ℝ)) (q : ℝ) :
    induced (fun a b => ψ a*star (φ b)) q=orbitTest 1 ψ φ q := by
  let k := (q/(4*Real.pi))^2
  have phase (x v : ℝ) : star (e (-x)*e (-v))=e (x+v) := by
    simp only [e,←Complex.exp_add,Complex.star_def,←Complex.exp_conj,map_add,map_mul,
      Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,Complex.ofReal_add]
    congr 1; ring
  have integrand (x a : ℝ) : (Ioi (0:ℝ)).indicator (plane (fun a b => ψ a*star (φ b)) k x) a =
      star (orbitTestKernel 1 ψ φ k x a) := by
    by_cases ha : 0<a
    · rw [indicator_of_mem ha,plane,←phase x (k*x/(x^2+a^2))]
      simp only [orbitTestKernel,radialWeight,Complex.real_smul,star_mul',star_star,Int.cast_one,
        neg_one_mul,neg_mul,neg_div,Complex.star_def,Complex.conj_ofReal]
      ring
    · have z := image_eq_zero_of_notMem_tsupport (fun h => ha (hpψ h))
      simp [ha,show ψ a=0 from z,orbitTestKernel,radialWeight,Set.mem_Ioi]
  simp only [induced,orbitTest,Complex.real_smul]
  congr 1
  change (∫x,∫a in Ioi (0:ℝ),plane _ k x a)=_
  simp_rw [←integral_indicator measurableSet_Ioi,integrand,Complex.star_def,integral_conj]

def diagonal (H : ℝ→ℝ→ℂ) (z p : ℕ) (b : ℤ) := if z=1 ∧ (p:ℤ)=b then
  ∫ a in Ioi (0:ℝ),((a⁻¹)^2:ℝ) • H a a else 0

/-- The e(b/z) in sourceDiagonal equals one on its only contributing branch.
The two square-root seed factors and the y ↦ py Jacobian cancel. -/
theorem diagonal_rank_one (ψ φ : ℝ→ℂ) (hpψ : tsupport ψ⊆Ioi (0:ℝ))
    (z p : ℕ) (hp : 0<p) (b : ℤ) :
    diagonal (fun a v => ψ a*star (φ v)) z p b=pairDiagonal z p b ψ φ := by
  by_cases hit : z=1 ∧ (p:ℤ)=b
  · obtain ⟨rfl,rfl⟩ := hit
    let c : ℝ := p
    have cp : 0<c := by exact_mod_cast hp
    let F := fun a : ℝ => ((a⁻¹)^2:ℝ) • (ψ a*star (φ a))
    have side (y : ℝ) : star (radialWeight (scaledSeed (p:ℤ) ψ) y*scaledSeed (p:ℤ) φ y)=c • F (c*y) := by
      have sq : (Real.sqrt c:ℂ)^2=(c:ℂ) := by exact_mod_cast Real.sq_sqrt cp.le
      have si : ((Real.sqrt c:ℂ)⁻¹)^2=(c:ℂ)⁻¹ := by rw [←inv_pow,sq]
      have ci : (c:ℂ)*(c:ℂ)⁻¹^2=(c:ℂ)⁻¹ := by field_simp [Complex.ofReal_ne_zero.mpr cp.ne']
      calc
        _ = ((Real.sqrt c:ℂ)⁻¹)^2*((y:ℂ)⁻¹)^2*(ψ (c*y)*star (φ (c*y))) := by
          simp only [radialWeight,scaledSeed,Int.cast_natCast,show (p:ℝ)=c from rfl,abs_of_pos cp,
            star_mul',star_star,Complex.star_def,Complex.conj_ofReal,map_inv₀,map_pow,
            Complex.ofReal_inv,Complex.ofReal_pow]
          ring
        _ = _ := by
          rw [si]; dsimp only [F]
          simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv,
            Complex.ofReal_mul,mul_inv_rev,mul_pow]
          linear_combination -((y:ℂ)⁻¹^2*(ψ (c*y)*star (φ (c*y))))*ci
    have cut : (∫ y : ℝ,c • F (c*y)) = ∫ y in Ioi (0:ℝ),c • F (c*y) := by
      symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have z : ψ (c*y)=0 := image_eq_zero_of_notMem_tsupport (fun h =>
        (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos cp.le (not_lt.mp hy))) (hpψ h))
      simp [F,z]
    have ph : e (p:ℝ)=1 := by
      unfold e
      rw [mul_comm _ ((p:ℝ):ℂ)]
      simpa using Complex.exp_nat_mul_two_pi_mul_I p
    rw [diagonal,if_pos ⟨rfl,rfl⟩,pairDiagonal,sourceDiagonal,if_pos ⟨rfl,rfl⟩]
    simp only [Nat.cast_one,Int.cast_natCast,div_one,ph,one_mul,Complex.star_def,←integral_conj]
    change (∫ a in Ioi (0:ℝ),F a)=∫ y,star (radialWeight (scaledSeed (p:ℤ) ψ) y*scaledSeed (p:ℤ) φ y)
    simp_rw [side]
    rw [cut,integral_smul]
    simpa only [mul_zero] using (integral_comp_mul_left_Ioi' F 0 cp).symm
  · simp [diagonal,pairDiagonal,sourceDiagonal,hit]

theorem height_diagonal (η H : RadialTest) (R : ℝ) :
    (∫ a in Ioi (0:ℝ),((a⁻¹)^2:ℝ) • height η H R a a)=
      (∫ s : ℝ,η.function s)*H.function 0/2 := by
  rw [height_integral (p:=1) (by norm_num)]
  have val (w : ℝ) :
      dilation 1 w • (((dilation 1 w)⁻¹)^2 • height η H R (dilation 1 w) (dilation 1 w))=
      η.function (2*w+R)*H.function 0 := by
    simp only [dilation,Real.sqrt_one,one_mul,height_exp,OriginalPositiveHeightTest20261112.logHeight,
      sub_self,zero_div,show (w+w)/2=w by ring,←two_mul w,Complex.real_smul,Complex.ofReal_mul,
      Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos w).ne'] <;> ring
  simp_rw [val,integral_mul_const]
  have A : (∫ w : ℝ,η.function (2*w+R))=(2:ℂ)⁻¹*(∫ s : ℝ,η.function s) := by
    have L := Measure.integral_comp_mul_left (fun x : ℝ => η.function (x+R)) (2:ℝ)
    simpa [integral_add_right_eq_self,Complex.real_smul] using L
  rw [A]; ring

theorem original_diagonal (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (R : ℝ) (n z p : ℕ) (b : ℤ) :
    diagonal (original ell hY R n) z p b =
      if z=1 ∧ (p:ℤ)=b then (ratio ell hY n).function 0/2 else 0 := by
  simp only [diagonal,original,height_diagonal,unit_mass,one_mul]

theorem original_diagonal_limit (ell : D4→ℤ) {Y : ℝ} (hY : 0<Y) (z p : ℕ) (b : ℤ) :
    Tendsto (fun n => if z=1 ∧ (p:ℤ)=b then (ratio ell hY n).function 0/2 else 0) atTop
      (𝓝 (if z=1 ∧ (p:ℤ)=b then diagonalMoment 0 (spectralTest ell Y)/(2*(Real.pi:ℂ)) else 0)) := by
  split_ifs
  · rw [←half_at_zero ell hY]
    exact (ratio_pointwise ell hY 0).div_const 2
  · exact tendsto_const_nhds
end ImbalancedChen.Part3.OriginalPositiveScalarGeometry20261112
end
