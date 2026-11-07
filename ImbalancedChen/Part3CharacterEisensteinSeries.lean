import ImbalancedChen.Part3CharacterEisensteinRowAction
import Mathlib.Analysis.Calculus.SmoothSeries

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ACTUAL character-weighted primitive Eisenstein series at q*z.
Signed chi(c)chi(d) is retained in every summand. The bounded character
weights inherit the existing genuine primitive lattice/derivative majorants.
Only absolute convergence and parameter holomorphy on Re(s)>1 are proved;
no continuation, nonzero/newform or channel-completeness claim is made.
-/
namespace ImbalancedChen.Part3.CharacterEisensteinSeries
noncomputable section
open Set Filter Topology Complex Metric UpperHalfPlane EisensteinSeries
open scoped UpperHalfPlane MatrixGroups BigOperators
open RealEisensteinSeedConvergence PrimitiveEisensteinParameterAnalytic
open Gamma0DegeneracyMapSourceOnly CharacterEisensteinRowAction

/-- Native positive dilation; the existing action theorem identifies it
with q*z, including its actual imaginary coordinate q*Im(z). -/
def scaledPoint (q : ℕ) (hq : 0 < q) (z : ℍ) : ℍ := degeneracyDiagonal q hq • z

theorem scaledPoint_coe (q : ℕ) (hq : 0 < q) (z : ℍ) :
    (scaledPoint q hq z : ℂ) = (q : ℂ)*(z : ℂ) :=
  degeneracyDiagonal_smul_coe q hq z

theorem scaledPoint_im (q : ℕ) (hq : 0 < q) (z : ℍ) :
    (scaledPoint q hq z).im = (q : ℝ)*z.im := by
  simpa using congrArg Complex.im (scaledPoint_coe q hq z)

/-- This is the literal positive base q*Im(z)/|c*q*z+d|^2. -/
theorem scaled_positiveBase (q : ℕ) (hq : 0 < q) (z : ℍ) (v : PrimitivePair) :
    positiveBase (scaledPoint q hq z) v =
      ((q : ℝ)*z.im)/‖(v.1 0 : ℂ)*((q : ℂ)*(z : ℂ))+(v.1 1 : ℂ)‖^2 := by
  rw [positiveBase,scaledPoint_im,scaledPoint_coe]

/-- The actual complex summand uses exp(s*log(positive base)), so the
real-positive powers have their canonical complex branch. -/
def characterSeed {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  primitiveWeight chi v*complexSeed (scaledPoint q hq z) v s

def characterSeedDerivative {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (v : PrimitivePair) (s : ℂ) : ℂ :=
  primitiveWeight chi v*complexSeedDerivative (scaledPoint q hq z) v s

/-- The requested half primitive-pair series; this is not an oldform
renaming or a formal zero object. -/
def characterEisenstein {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (s : ℂ) (z : ℍ) : ℂ :=
  (1/2 : ℂ)*∑' v : PrimitivePair, characterSeed hq chi z v s

theorem characterSeed_literal {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    characterSeed hq chi z v s =
      (chi (v.1 0 : ZMod q)*chi (v.1 1 : ZMod q))*
        Complex.exp (s*(Real.log (((q : ℝ)*z.im)/
          ‖(v.1 0 : ℂ)*((q : ℂ)*(z : ℂ))+(v.1 1 : ℂ)‖^2) : ℂ)) := by
  rw [characterSeed,primitiveWeight,characterWeight,complexSeed,scaled_positiveBase]

theorem characterSeed_norm_le {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    ‖characterSeed hq chi z v s‖ ≤ seed s.re (scaledPoint q hq z) v.1 := by
  rw [characterSeed,norm_mul]
  have hw := characterWeight_norm_le_one chi (v.1 0) (v.1 1)
  have hm := mul_le_mul_of_nonneg_right hw (norm_nonneg (complexSeed (scaledPoint q hq z) v s))
  simpa only [one_mul,norm_complexSeed,positiveBase_rpow_eq_seed] using hm

/-- Actual absolute convergence, including character zeros and q=1. -/
theorem characterSeed_norm_summable {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair => ‖characterSeed hq chi z v s‖) := by
  apply (primitiveSeed_summable s.re hs (scaledPoint q hq z)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro v
  exact characterSeed_norm_le hq chi z v s

theorem characterSeed_summable {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : PrimitivePair => characterSeed hq chi z v s) := by
  exact Summable.of_norm_bounded (primitiveSeed_summable s.re hs (scaledPoint q hq z))
    (fun v => characterSeed_norm_le hq chi z v s)

/-- Uniform convergence on every bounded real-part slab in Re(s)>1,
stronger than pointwise parameter convergence on a compact neighborhood. -/
theorem characterSeed_tendstoUniformlyOn {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    TendstoUniformlyOn
      (fun F : Finset PrimitivePair => fun s : ℂ => ∑ v ∈ F, characterSeed hq chi z v s)
      (fun s : ℂ => ∑' v : PrimitivePair, characterSeed hq chi z v s)
      atTop {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
  apply tendstoUniformlyOn_tsum
    ((primitiveSeed_summable a ha (scaledPoint q hq z)).add
      (primitiveSeed_summable b hb (scaledPoint q hq z)))
  intro v s hs
  have h0 : ‖characterSeed hq chi z v s‖ ≤ ‖complexSeed (scaledPoint q hq z) v s‖ := by
    rw [characterSeed,norm_mul]
    exact (mul_le_mul_of_nonneg_right (characterWeight_norm_le_one chi (v.1 0) (v.1 1))
      (norm_nonneg _)).trans_eq (one_mul _)
  exact h0.trans (norm_complexSeed_le_endpoint_seeds (scaledPoint q hq z) v a b s hs.1 hs.2)

theorem characterSeed_hasDerivAt {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (v : PrimitivePair) (s : ℂ) :
    HasDerivAt (characterSeed hq chi z v) (characterSeedDerivative hq chi z v s) s :=
  (complexSeed_hasDerivAt (scaledPoint q hq z) v s).const_mul (primitiveWeight chi v)

theorem characterSeedDerivative_norm_le {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (a b epsilon : ℝ) (hepsilon : 0 < epsilon) (v : PrimitivePair)
    (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖characterSeedDerivative hq chi z v s‖ ≤
      (seed (a-epsilon) (scaledPoint q hq z) v.1+
        seed (b+epsilon) (scaledPoint q hq z) v.1)/epsilon := by
  have h0 : ‖characterSeedDerivative hq chi z v s‖ ≤
      ‖complexSeedDerivative (scaledPoint q hq z) v s‖ := by
    rw [characterSeedDerivative,norm_mul]
    exact (mul_le_mul_of_nonneg_right (characterWeight_norm_le_one chi (v.1 0) (v.1 1))
      (norm_nonneg _)).trans_eq (one_mul _)
  exact h0.trans (complexSeedDerivative_norm_le (scaledPoint q hq z) a b epsilon hepsilon v s ha hb)

/-- Proved weighted derivative majorant gives actual parameter derivative. -/
theorem character_tsum_hasDerivAt_parameter {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => ∑' v : PrimitivePair, characterSeed hq chi z v w)
      (∑' v : PrimitivePair, characterSeedDerivative hq chi z v s) s := by
  let r : ℝ := (s.re-1)/4
  let a : ℝ := s.re-r
  let b : ℝ := s.re+r
  have hr : 0 < r := by dsimp only [r]; linarith
  have ha : 1 < a-r := by dsimp only [a,r]; linarith
  have hb : 1 < b+r := by dsimp only [b,r]; linarith
  let u : PrimitivePair → ℝ := fun v =>
    (seed (a-r) (scaledPoint q hq z) v.1+seed (b+r) (scaledPoint q hq z) v.1)/r
  have hu : Summable u := derivativeMajorant_summable (scaledPoint q hq z) a b r ha hb
  have hsball : s ∈ ball s r := mem_ball_self hr
  refine hasDerivAt_tsum_of_isPreconnected (u := u) (t := ball s r)
    hu isOpen_ball (convex_ball s r).isPreconnected
    (fun v w _ => characterSeed_hasDerivAt hq chi z v w) ?_
    hsball (characterSeed_summable hq chi z s hs) hsball
  intro v w hw
  have hnorm : ‖w-s‖ < r := by simpa only [mem_ball,dist_eq_norm] using hw
  have hre : |w.re-s.re| ≤ ‖w-s‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w-s)
  obtain ⟨hl,hu⟩ := abs_le.mp (hre.trans hnorm.le)
  exact characterSeedDerivative_norm_le hq chi z a b r hr v w
    (by dsimp only [a]; linarith) (by dsimp only [b]; linarith)

theorem characterEisenstein_hasDerivAt {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    HasDerivAt (fun w : ℂ => characterEisenstein hq chi w z)
      ((1/2 : ℂ)*∑' v : PrimitivePair, characterSeedDerivative hq chi z v s) s :=
  (character_tsum_hasDerivAt_parameter hq chi z s hs).const_mul (1/2 : ℂ)

theorem characterEisenstein_analyticOnNhd {q : ℕ} (hq : 0 < q) (chi : DirichletCharacter ℂ q)
    (z : ℍ) : AnalyticOnNhd ℂ (fun s : ℂ => characterEisenstein hq chi s z) {s : ℂ | 1 < s.re} := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => characterEisenstein hq chi s z) {s : ℂ | 1 < s.re} := by
    intro s hs
    exact (characterEisenstein_hasDerivAt hq chi z s hs).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)
end
end ImbalancedChen.Part3.CharacterEisensteinSeries
