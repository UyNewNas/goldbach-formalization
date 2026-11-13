import ImbalancedChen.Part3OriginalSameInfinityFixedScalarTrace
import ImbalancedChen.Part3OriginalSameInfinityWeightedHol

/-! The fixed literal period-64 mode on Γ₀(q) and positive native
Fourier marks m,n, with the same observation cusp on both legs. -/
namespace ImbalancedChen.Part3.OriginalSameInfinityPeriodTrace20261113
noncomputable section
open Complex MeasureTheory
open scoped BigOperators MatrixGroups ComplexConjugate
open OriginalSameInfinityWeightedHol20261113 (holSum basisTerm diagonal)
open OriginalSameInfinityFixedScalarTrace20261113 (total fixed_scalar_trace)
open OriginalSameInfinityTensorSpectrum20261113 (disc cont)
open OriginalSameInfinityScalarLimits20261113 (scalar_limits target)
open OriginalSameInfinityScalarGeometry20261113 (term)
open OriginalPositiveStrip20261112 (residual)
open OriginalHolomorphicWeightSum20261112 (oddProjection gamma_step)
open ActualPrescribedPositiveJ20261112 ActualPositiveNativeDiagonal20261112
open OriginalHolomorphicBasisMass20261112 (basisCost basis_mass)
open OriginalHolomorphicPeterssonSpace20261112 (BasisIndex formsBasis)
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalHolomorphicCuspFrames20261110 (frameR)
open ActualPositiveHolomorphicWeights20261112 (holWeight moment)
open OriginalHolomorphicProjectionPrices20261112 (weighted_moments)
open P3NativePeriod64SamplingSourceOnly (D4) P3Period64NativeReconstructionSourceOnly (spectralTest)
open private product_le from ImbalancedChen.Part3ActualMarkedSpectralMajorants

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem cost (q m n : ℕ+) (Φ : ℝ→ℂ) (j : ℕ) :
    (∑ i,‖basisTerm q m n Φ j i‖)≤
      ((basisCost q.val m.val 1+basisCost q.val n.val 1)/Real.pi)*
        (((2*j+1:ℕ):ℝ)*‖moment (2*j+1) Φ‖) := by
  let X (a : ℕ+) (i : BasisIndex q.val (j+1)) :=
    frameR q.val (NeZero.pos q.val) (j+1) (formsBasis q.val (j+1) i) 1 a.val
  let τ := 4*Real.pi*Real.Gamma (2*(j:ℝ)+1)
  let b := ((2*j+1:ℕ):ℝ)*‖moment (2*j+1) Φ‖/Real.pi
  have gp : 0<Real.Gamma (2*(j:ℝ)+1) := Real.Gamma_pos_of_pos (by positivity)
  have ne (i : BasisIndex q.val (j+1)) : ‖basisTerm q m n Φ j i‖=b*(τ*(‖X m i‖*‖X n i‖)) := by
    rw [basisTerm,norm_mul,norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,gamma_step,
      show 2*((j+1:ℕ):ℝ)-1=2*(j:ℝ)+1 by push_cast;ring,
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) gp.le)]
    simp only [holWeight,norm_mul,norm_pow,Complex.norm_I,one_pow,mul_one,Complex.norm_ofNat]
    dsimp only [b,τ,X]
    field_simp [Real.pi_ne_zero] <;> ring
  have M : τ*(∑ i,‖X m i‖*‖X n i‖)≤basisCost q.val m.val 1+basisCost q.val n.val 1 := by
    apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => product_le (X m i) (X n i)))
      (show 0≤τ by dsimp [τ];positivity)).trans
    rw [Finset.sum_add_distrib,mul_add]
    exact add_le_add (basis_mass q.val j m.property 1) (basis_mass q.val j n.property 1)
  simp_rw [ne]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left M (show 0≤b by dsimp [b];positivity)).trans_eq (by dsimp only [b];ring)

theorem basis_absolute (q m n : ℕ+) (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) :
    Summable (fun p : (Σ j : ℕ,BasisIndex q.val (j+1)) =>
      ‖basisTerm q m n (spectralTest ell Y) p.1 p.2‖) := by
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun j => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype]
  exact ((weighted_moments ell yp).mul_left _).of_nonneg_of_le
    (fun _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (cost q m n _)

/-- All three physically normalized spectra. The two same-mark
J₀ collisions cancel before the complete geometric test is formed. -/
theorem same_infinity_period_trace (q m n : ℕ+) (ell : D4→ℤ) {Y : ℝ} (yp : 0<Y) :
    let Φ := spectralTest ell Y
    Summable (fun k : ℕ+ => ‖term Φ q m n k‖) ∧
    (∑' k : ℕ+,term Φ q m n k)=
      total q m n (nativeWeight q.val Φ) (fun t => positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))+
        holSum q m n Φ := by
  let Φ := spectralTest ell Y
  have R := (scalar_limits ell yp q m n).2.2.1
  obtain ⟨P,_,EqP⟩ := OriginalSameInfinityWeightedHol20261113.weighted_hol q m n ell yp
  have HS := (R.of_norm.hasSum.add P.of_norm.hasSum).congr_fun (g:=fun k => term Φ q m n k) (fun k => by
    by_cases good : q.val∣k.val
    · simp only [term,if_pos good,oddProjection,Φ,mul_sub]
      ring
    · simp [term,good])
  have EqR := fixed_scalar_trace q m n ell yp
  change diagonal m n Φ+(∑' k : ℕ+,term (residual ell Y) q m n k)=_ at EqR
  refine ⟨summable_norm_iff.mpr HS.summable,?_⟩
  change _=total q m n (nativeWeight q.val Φ)
    (fun t => positiveWeight Φ t/(Real.cosh (Real.pi*t):ℂ))+holSum q m n Φ
  rw [HS.tsum_eq,EqP,←EqR]
  ring

end
end ImbalancedChen.Part3.OriginalSameInfinityPeriodTrace20261113
