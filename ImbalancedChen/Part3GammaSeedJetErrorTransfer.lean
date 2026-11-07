import ImbalancedChen.Part3GammaCompactSeedGraphTransport
import ImbalancedChen.Part3CompactProductKernelSixJet
import ImbalancedChen.Part3Gamma0CompactUpperChartExtension

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The precise Euclidean-to-hyperbolic error dictionary used by finite tensor
approximation. A fixed positive planar rectangle lifts to an actual compact
subset of H. The literal value/xx/yy jets are identified with upperMaass;
the height-square coefficient is retained in the quantitative error.
This does not assume a quotient graph limit or core membership.
-/

namespace ImbalancedChen.Part3.GammaSeedJetErrorTransfer20261026a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactUpperChartExtension20261025a ActualGamma0MaassDescent20261025a
open CompactProductKernelSixJet20261025a

/-- A genuine compact H carrier, not the unbounded strip below a height. -/
def liftedBox (A a b : ℝ) : Set UpperHalfPlane :=
  {z | (z.re, z.im) ∈ planeBox A a b}

theorem liftedBox_isCompact (A a b : ℝ) (ha : 0 < a) :
    IsCompact (liftedBox A a b) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have himage : ((↑) : UpperHalfPlane → ℂ) '' liftedBox A a b =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) '' planeBox A a b := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.re, z.im), hz, by ext <;> rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hpos : 0 < p.2 := ha.trans_le hp.2.1
      exact ⟨⟨⟨p.1, p.2⟩, hpos⟩, hp, rfl⟩
  rw [himage]
  exact (isCompact_planeBox A a b).image (by fun_prop)

theorem seed_support_liftedBox (f : UpperHalfPlane → ℂ) (A a b : ℝ)
    (hs : tsupport (extendUpper f) ⊆ planeBox A a b) :
    Function.support f ⊆ liftedBox A a b := by
  intro z hz
  apply hs
  apply subset_tsupport
  simpa only [extendUpper_pair] using hz

def valueJet : JetIndex := ⟨(0, 0), by norm_num⟩
def xxJet : JetIndex := ⟨(2, 0), by norm_num⟩
def yyJet : JetIndex := ⟨(0, 2), by norm_num⟩

@[simp] theorem partialJet_value (F : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    partialJet valueJet F p = F p := by
  simp [partialJet, valueJet]

@[simp] theorem partialJet_xx (F : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    partialJet xxJet F p = deriv (deriv (fun x : ℝ => F (x, p.2))) p.1 := by
  simp [partialJet, xxJet, iteratedDeriv_succ]

@[simp] theorem partialJet_yy (F : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) :
    partialJet yyJet F p = deriv (deriv (fun y : ℝ => F (p.1, y))) p.2 := by
  simp [partialJet, yyJet, iteratedDeriv_succ]

theorem upperMaass_eq_jets (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    upperMaass f z = -((z.im : ℂ)^2 *
      (partialJet xxJet (extendUpper f) (z.re, z.im) +
        partialJet yyJet (extendUpper f) (z.re, z.im))) := by
  simp only [partialJet_xx, partialJet_yy, upperMaass,
    Complex.measurableEquivRealProd_apply, chartMaass]

theorem value_error_of_jet (f g : UpperHalfPlane → ℂ) (z : UpperHalfPlane)
    {epsilon : ℝ}
    (hv : ‖partialJet valueJet (extendUpper f) (z.re, z.im) -
      partialJet valueJet (extendUpper g) (z.re, z.im)‖ ≤ epsilon) :
    ‖f z - g z‖ ≤ epsilon := by
  simpa only [partialJet_value, extendUpper_pair] using hv

/-- The actual coefficient y² must be paid on a common bounded-height
carrier. A Euclidean C2 error alone is not a global Maass error. -/
theorem maass_error_of_jets (f g : UpperHalfPlane → ℂ) (z : UpperHalfPlane)
    {B epsilon : ℝ} (hB : z.im ≤ B) (he : 0 ≤ epsilon)
    (hx : ‖partialJet xxJet (extendUpper f) (z.re, z.im) -
      partialJet xxJet (extendUpper g) (z.re, z.im)‖ ≤ epsilon)
    (hy : ‖partialJet yyJet (extendUpper f) (z.re, z.im) -
      partialJet yyJet (extendUpper g) (z.re, z.im)‖ ≤ epsilon) :
    ‖upperMaass f z - upperMaass g z‖ ≤ (2 * B^2) * epsilon := by
  let Xf := partialJet xxJet (extendUpper f) (z.re, z.im)
  let Xg := partialJet xxJet (extendUpper g) (z.re, z.im)
  let Yf := partialJet yyJet (extendUpper f) (z.re, z.im)
  let Yg := partialJet yyJet (extendUpper g) (z.re, z.im)
  have heq : upperMaass f z - upperMaass g z =
      -((z.im : ℂ)^2 * ((Xf-Xg)+(Yf-Yg))) := by
    rw [upperMaass_eq_jets, upperMaass_eq_jets]
    dsimp [Xf, Xg, Yf, Yg]
    ring
  have hnorm : ‖((Xf-Xg)+(Yf-Yg))‖ ≤ 2 * epsilon :=
    (norm_add_le _ _).trans (by simpa only [two_mul] using add_le_add hx hy)
  have hsq : z.im^2 ≤ B^2 := pow_le_pow_left₀ z.im_pos.le hB 2
  calc
    ‖upperMaass f z - upperMaass g z‖ =
        z.im^2 * ‖(Xf-Xg)+(Yf-Yg)‖ := by
      rw [heq, norm_neg, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos z.im_pos]
    _ ≤ z.im^2 * (2 * epsilon) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _ ≤ B^2 * (2 * epsilon) := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (2 * B^2) * epsilon := by ring

/-- A convenient single accuracy budget for the value and both second
jets on the fixed compact support rectangle. -/
def jetLoss (B : ℝ) : ℝ := 1 + 2 * B^2

theorem jetLoss_pos (B : ℝ) : 0 < jetLoss B := by unfold jetLoss; positivity

theorem value_maass_errors_on_liftedBox (f g : UpperHalfPlane → ℂ)
    (A a B : ℝ) {epsilon : ℝ} (he : 0 ≤ epsilon)
    (hjets : ∀ p ∈ planeBox A a B, ∀ ij : JetIndex,
      ‖partialJet ij (extendUpper f) p - partialJet ij (extendUpper g) p‖ ≤ epsilon) :
    (∀ z ∈ liftedBox A a B, ‖f z - g z‖ ≤ jetLoss B * epsilon) ∧
    (∀ z ∈ liftedBox A a B, ‖upperMaass f z - upperMaass g z‖ ≤ jetLoss B * epsilon) := by
  constructor
  · intro z hz
    exact (value_error_of_jet f g z (hjets _ hz valueJet)).trans
      (by dsimp [jetLoss]; nlinarith [mul_nonneg (sq_nonneg B) he])
  · intro z hz
    exact (maass_error_of_jets f g z hz.2.2 he
      (hjets _ hz xxJet) (hjets _ hz yyJet)).trans
      (by dsimp [jetLoss]; nlinarith)

end
end ImbalancedChen.Part3.GammaSeedJetErrorTransfer20261026a
