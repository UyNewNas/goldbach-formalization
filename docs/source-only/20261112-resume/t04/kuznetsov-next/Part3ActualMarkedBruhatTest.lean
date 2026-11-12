import ImbalancedChen.Part3ActualCuspOneGeometricPairing
import ImbalancedChen.Part3OriginalContinuousPoincarePackets
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Scaling both physical height probes in the actual Bruhat integral.
The resulting test depends on the signed branch and the manuscript's
single normalized real argument. -/
namespace ImbalancedChen.Part3.ActualMarkedBruhatTest20261112

noncomputable section
open Set MeasureTheory Complex AddCircle
open scoped BigOperators
open CompactCuspGeometricFubini20261025a InfinityZeroActualFiberGeometricPair20261026a
open InfinityZeroActualFiberFourier20261026a OriginalSignedTraceInput20261102
open OriginalContinuousPoincarePackets20261110 P3Period64NativeReconstructionSourceOnly (e)

/-- The integrand after (X,Y)=(p x,p y). The surviving sign is the
sign of the second physical index, including the Poisson sign. -/
def orbitTestKernel (s : ℤ) (ψ φ : ℝ → ℂ) (k x y : ℝ) : ℂ :=
  radialWeight ψ y * e (-x) * (e (-(s : ℝ)*k*x/(x^2+y^2))*φ (k*y/(x^2+y^2)))

/-- Real-argument test for the orientation with the cusp-one vector on
the left. It includes the complete two-probe overlap transform. -/
def orbitTest (s : ℤ) (ψ φ : ℝ → ℂ) (u : ℝ) : ℂ :=
  ((4*Real.pi/u : ℝ) : ℂ) *
    star (∫ x : ℝ,∫ y : ℝ,orbitTestKernel s ψ φ ((u/(4*Real.pi))^2) x y)

private theorem phase_real (m : ℤ) (v : ℝ) : phase m v=e ((m : ℝ)*v) := by
  simp only [phase,fourier_coe_apply,e,Complex.ofReal_one,div_one,Complex.ofReal_mul,
    Complex.ofReal_intCast]
  congr 1
  ring

private theorem divide_coords (a C x y v : ℝ) (ha : a≠0) :
    (v/a)/(C^2*((x/a)^2+(y/a)^2)) = a*v/(C^2*(x^2+y^2)) := by
  simp only [div_pow,← add_div,← mul_div_assoc]
  rw [div_div_eq_mul_div]
  congr 1
  field_simp [ha] <;> ring

private theorem kernel_scale (p : ℕ) (hp : 0<p) (n : ℤ) (ψ φ : ℝ → ℂ) (C x y : ℝ) :
    let a := (p : ℝ)
    let b := |(n : ℝ)|
    geometricPairKernel C (p : ℤ) n (scaledSeed (p : ℤ) ψ) (scaledSeed n φ) (x/a,y/a) =
      (((a^2/(Real.sqrt a*Real.sqrt b) : ℝ) : ℂ)) *
        orbitTestKernel n.sign ψ φ (a*b/C^2) x y := by
  dsimp only
  let a := (p : ℝ)
  let b := |(n : ℝ)|
  have ha : 0<a := by exact_mod_cast hp
  have hb : (n.sign : ℝ)*b=(n : ℝ) := by
    exact_mod_cast Int.sign_mul_abs n
  have scaledY : b*((y/a)/(C^2*((x/a)^2+(y/a)^2)))=(a*b/C^2)*y/(x^2+y^2) := by
    rw [divide_coords a C x y y ha.ne']
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have scaledX : (n : ℝ)*(-(x/a)/(C^2*((x/a)^2+(y/a)^2))) =
      -(n.sign : ℝ)*(a*b/C^2)*x/(x^2+y^2) := by
    rw [neg_div,divide_coords a C x y x ha.ne',← hb]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have firstX : (-(p : ℤ) : ℝ)*(x/a)= -x := by
    push_cast
    change -a*(x/a)= -x
    field_simp [ha.ne']
  have weight : ((y/a)⁻¹)^2 = a^2*(y⁻¹)^2 := by
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_pow]
  have shift : a*(y/a)=y := by field_simp [ha.ne']
  change radialWeight (scaledSeed (p : ℤ) ψ) (y/a)*phase (-(p : ℤ)) (x/a)*
      (phase n (-(x/a)/(C^2*((x/a)^2+(y/a)^2)))*
        scaledSeed n φ ((y/a)/(C^2*((x/a)^2+(y/a)^2)))) = _
  simp only [phase_real,firstX,scaledX,scaledSeed,Int.cast_natCast,abs_of_nonneg ha.le,
    show |(n : ℝ)|=b from rfl,show (p : ℝ)=a from rfl,
    shift,scaledY,orbitTestKernel,radialWeight,weight,star_mul',star_inv₀,
    Complex.star_def,Complex.conj_ofReal,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    mul_inv_rev,div_eq_mul_inv]
  ring

private theorem scale_plane (F : ℝ → ℝ → ℂ) {a : ℝ} (ha : 0<a) :
    (∫ x : ℝ,∫ y : ℝ,F (x/a) (y/a)) = ((a^2 : ℝ) : ℂ)*(∫ x : ℝ,∫ y : ℝ,F x y) := by
  calc
    _ = ∫ x : ℝ, |a| • (∫ y : ℝ,F (x/a) y) :=
      integral_congr_ae (ae_of_all _ (fun x => Measure.integral_comp_div (F (x/a)) a))
    _ = _ := by
      rw [integral_smul,Measure.integral_comp_div (fun x => ∫ y : ℝ,F x y) a,abs_of_pos ha,smul_smul]
      simp only [Complex.real_smul,pow_two]

/-- Both Jacobians, both square-root seed normalizations, the geometric
factor 1/(d sqrt N) and the 4π argument occur in this identity. -/
theorem orbit_integral (N : ℕ) [NeZero N] (d : ℕ+) (p : ℕ) (hp : 0<p) (n : ℤ) (hn : n≠0)
    (ψ φ : ℝ → ℂ) :
    let C := traceModulus N d
    let u := 4*Real.pi*Real.sqrt ((p : ℝ)*(n.natAbs : ℝ))/C
    star (∫ x : ℝ,∫ y : ℝ,mixedOrbitKernel N d (p : ℤ) n
      (scaledSeed (p : ℤ) ψ) (scaledSeed n φ) (x,y)) = orbitTest n.sign ψ φ u / (C : ℂ) := by
  let a := (p : ℝ)
  let b := |(n : ℝ)|
  let C := traceModulus N d
  let u := 4*Real.pi*Real.sqrt (a*b)/C
  let K := fun x y => geometricPairKernel C (p : ℤ) n (scaledSeed (p : ℤ) ψ) (scaledSeed n φ) (x,y)
  let L := fun x y => orbitTestKernel n.sign ψ φ (a*b/C^2) x y
  have ha : 0<a := by exact_mod_cast hp
  have hb : 0<b := abs_pos.mpr (by exact_mod_cast hn)
  have hC : 0<C := traceModulus_pos (NeZero.pos N) d.property
  have hu : 0<u := by dsimp [u]; positivity
  have K1 (x y : ℝ) : K (x/a) (y/a) = ((a^2/(Real.sqrt a*Real.sqrt b) : ℝ) : ℂ)*L x y :=
    kernel_scale p hp n ψ φ C x y
  have IJ := scale_plane K ha
  simp_rw [K1,integral_const_mul] at IJ
  have Ja : (a : ℂ)≠0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have J : (∫ x,∫ y,K x y) = ((Real.sqrt a*Real.sqrt b : ℝ) : ℂ)⁻¹ * (∫ x,∫ y,L x y) := by
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul] at IJ ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 Ja)
    rw [← IJ]
    simp only [div_eq_mul_inv,mul_assoc]
  have arg : (u/(4*Real.pi))^2 = a*b/C^2 := by
    have E : u/(4*Real.pi)=Real.sqrt (a*b)/C := by dsimp [u]; field_simp [Real.pi_ne_zero,hC.ne']
    rw [E,div_pow,Real.sq_sqrt (mul_nonneg ha.le hb.le)]
  have norm : (4*Real.pi/u)/C=(Real.sqrt a*Real.sqrt b)⁻¹ := by
    dsimp [u]
    rw [Real.sqrt_mul ha.le]
    field_simp [hC.ne',Real.pi_ne_zero,(Real.sqrt_pos.mpr ha).ne',(Real.sqrt_pos.mpr hb).ne']
  have bn : (n.natAbs : ℝ)=b := by exact_mod_cast Int.natCast_natAbs n
  dsimp only
  rw [bn]
  simp_rw [mixedOrbitKernel_eq_realC]
  change star (∫ x,∫ y,K x y) = orbitTest n.sign ψ φ u/(C : ℂ)
  rw [J,orbitTest,arg,star_mul',star_inv₀,Complex.star_def,Complex.conj_ofReal]
  have cn := congrArg (fun q : ℝ => (q : ℂ)) norm
  simp only [Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_mul] at cn
  simp only [Complex.ofReal_div,Complex.ofReal_inv,Complex.ofReal_mul,L,div_eq_mul_inv] at cn ⊢
  linear_combination -cn * (conj (∫ x : ℝ,∫ y : ℝ,orbitTestKernel n.sign ψ φ (a*b/C^2) x y))

end
end ImbalancedChen.Part3.ActualMarkedBruhatTest20261112
