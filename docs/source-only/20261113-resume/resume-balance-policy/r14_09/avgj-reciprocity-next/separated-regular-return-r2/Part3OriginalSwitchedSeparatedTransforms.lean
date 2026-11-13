import ImbalancedChen.Part3OriginalSwitchedFourCoordinateRows
import ImbalancedChen.Part3OriginalSwitchedUniformRegularTransform

/-! Exchange the physical rank-one modes through the actual two
regular transformations of the positive trace. -/
namespace ImbalancedChen.Part3.OriginalSwitchedSeparatedTransforms20261113
noncomputable section
open Set MeasureTheory Complex
open scoped BigOperators
open OriginalSwitchedFourCoordinateSymbol20261113 (coefficient lattice_budget)
open OriginalSwitchedFourCoordinateRows20261113 (phase norm_phase ratio physical_weights)
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode norm_e)
open OriginalSwitchedCutoffModes20261113 (mode)
open ActualPrescribedPositiveJ20261112 (positiveWeight regular_transform)
open ActualPositiveJRotationPair20261112 (regularKernel)
open ActualPositiveHolomorphicWeights20261112
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)
open OriginalSwitchedUniformRegularTransform20261113 (mode_uniform)
open OriginalSwitchedSchwartzPrices20261113 (weight)

private abbrev μ : Measure ℝ := volume.restrict (Ioi 0)

def factor (j : ℕ) (Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (m n : ℕ) : ℂ :=
  let ζ := ratio (j:=j) Y Q d
  if ζ∈Icc (1/8:ℝ) 8 then coefficient k*phase k ((m:ℝ)/classicalMScale j)
    ((n:ℝ)/classicalMScale j) ζ else 0

theorem factor_norm (j : ℕ) (Y Q : ℝ) (d : ℕ+) (k : D4→ℤ) (m n : ℕ) :
    ‖factor j Y Q d k m n‖≤‖coefficient k‖ := by
  unfold factor
  split_ifs <;> simp only [norm_zero,norm_mul,norm_phase,mul_one,norm_nonneg,le_rfl]

private theorem integrated (K : ℝ→ℂ) {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+)
    (int : ∀ l : ℤ,Integrable (fun x => K x*spectralTest (mode l) Y⁻¹ x) μ) :
    HasSum (fun k : D4→ℤ => factor j Y Q d k m n*∫ x,K x*spectralTest (mode (k 0)) Y⁻¹ x ∂μ)
      (∫ x,K x*switchedTest Y ((d.val:ℝ)*Q) m n x ∂μ) := by
  let f (l : ℤ) (x : ℝ) := K x*spectralTest (mode l) Y⁻¹ x
  let a := fun k : D4→ℤ => factor j Y Q d k m n
  obtain ⟨_,_,S,_⟩ := lattice_budget 0
  have S0 : Summable (fun k : D4→ℤ => ‖coefficient k‖) := by simpa using S
  have fn (l : ℤ) (x : ℝ) : ‖f l x‖=‖f 0 x‖ := by
    simp only [f,spectralTest,spectralMode,norm_mul,norm_e,mul_one]
  have p := hasSum_integral_of_dominated_convergence (μ:=μ)
    (F:=fun k x => a k*f (k 0) x) (f:=fun x => K x*switchedTest Y ((d.val:ℝ)*Q) m n x)
    (fun k x => ‖coefficient k‖*‖f 0 x‖)
    (fun k => ((int (k 0)).const_mul (a k)).aestronglyMeasurable)
    (fun k => ae_of_all _ fun x => by
      rw [norm_mul,fn]
      exact mul_le_mul_of_nonneg_right (factor_norm j Y Q d k m n) (norm_nonneg _))
    (ae_of_all _ fun x => S0.mul_right _)
    (by simpa only [tsum_mul_right] using (int 0).norm.const_mul (∑' k : D4→ℤ,‖coefficient k‖))
    (ae_of_all _ fun x => ((physical_weights hm hn yp qp d x).mul_left (K x)).congr_fun
      (fun k => by change a k*(K x*spectralTest (mode (k 0)) Y⁻¹ x)=K x*(a k*_);ring))
  simpa only [integral_const_mul,a,f] using p

theorem principal {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (t : ℝ) :
    HasSum (fun k : D4→ℤ => factor j Y Q d k m n*positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t)
      (positiveWeight (switchedTest Y ((d.val:ℝ)*Q) m n) t) := by
  have e (a b c : ℂ) : a/c*b=a*b/c := by ring
  simpa only [e,positiveWeight] using integrated (fun x => regularKernel x t/(x:ℂ)) hm hn yp qp d
    (fun l => by simpa only [e] using (regular_transform (mode l) (inv_pos.mpr yp) t).1)

theorem holomorphic {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) (h : ℕ) :
    HasSum (fun k : D4→ℤ => factor j Y Q d k m n*holWeight h (spectralTest (mode (k 0)) Y⁻¹))
      (holWeight h (switchedTest Y ((d.val:ℝ)*Q) m n)) := by
  have e (a b c : ℂ) : a/c*b=a*b/c := by ring
  have p := integrated (fun x => intJ (2*h+1) x/(x:ℂ)) hm hn yp qp d
    (fun l => by simpa only [e] using moment_L1 (2*h+1) (mode l) (inv_pos.mpr yp))
  simp only [e] at p
  have q : HasSum (fun k : D4→ℤ => factor j Y Q d k m n*moment (2*h+1) (spectralTest (mode (k 0)) Y⁻¹))
      (moment (2*h+1) (switchedTest Y ((d.val:ℝ)*Q) m n)) := p
  exact (q.mul_left (4*I^(2*(h+1)))).congr_fun (fun k => by unfold holWeight;ring)

/-- This is the entire absolute mode budget available before inserting
both shifted coefficient rows into a principal or incoming-Eisenstein sieve. -/
theorem principal_budget :
    ∃ C : ℝ,0≤C ∧ ∀ Y : ℝ,1≤Y → ∀ t : ℝ,
      let a := fun k : D4→ℤ => (1+|t|)^3*‖coefficient k‖*
        ‖positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t‖
      Summable a ∧ (∑' k,a k)≤C*(1+Real.log (2*Y)^2) := by
  obtain ⟨r,H,hp,B⟩ := mode_uniform
  obtain ⟨A,ap,S,E⟩ := lattice_budget r
  refine ⟨H*A,mul_nonneg hp ap.le,fun Y y1 t => ?_⟩
  let p := H*(1+Real.log (2*Y)^2)
  have pp : 0≤p := mul_nonneg hp (by positivity)
  let g := fun k : D4→ℤ => ‖coefficient k‖*(1+|(k 0:ℝ)|)^r
  let a := fun k : D4→ℤ => (1+|t|)^3*‖coefficient k‖*‖positiveWeight (spectralTest (mode (k 0)) Y⁻¹) t‖
  have h (k : D4→ℤ) : a k≤p*g k := by
    have z := mul_le_mul_of_nonneg_left (B (k 0) Y y1 t) (norm_nonneg (coefficient k))
    dsimp only [a,g,p];unfold weight at z
    nlinarith only [z]
  have s : Summable a := Summable.of_nonneg_of_le (fun k => by dsimp only [a];positivity) h (S.mul_left p)
  refine ⟨s,(s.tsum_le_tsum h (S.mul_left p)).trans ?_⟩
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left E pp).trans_eq
  dsimp only [p];ring

end
end ImbalancedChen.Part3.OriginalSwitchedSeparatedTransforms20261113
