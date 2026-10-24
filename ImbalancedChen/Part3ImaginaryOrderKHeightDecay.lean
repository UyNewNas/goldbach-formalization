import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
ROOT alone owns the compilation queue. No actual source is changed.

For the ACTUAL integral imaginaryOrderK, this proves the twice integrated
identity and quadratic decay in the real height parameter. The positive
envelope is an explicit ordinary u integral; no spectral inequality,
continuity, integrability, boundary value or Plancherel identity is assumed.

This is a coarse polynomial bound on K itself. It is not the manuscript's
regular Bessel transform bound t^(-5/2)+Y0*t^(-3), and supplies no Kuznetsov,
automorphic measure, Fourier coefficients, large sieve or 7/32 theorem.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKHeightDecaySourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly

def amplitude (q u : ℝ) : ℝ := Real.exp (-q * Real.cosh u)

def amplitudeD1 (q u : ℝ) : ℝ :=
  -q * Real.sinh u * amplitude q u

def amplitudeD2 (q u : ℝ) : ℝ :=
  (q^2 * Real.sinh u^2 - q * Real.cosh u) * amplitude q u

def secondPositiveEnvelope (q u : ℝ) : ℝ :=
  (q * Real.cosh u + q^2 * Real.sinh u^2) * amplitude q u

def decayMajorant (q u : ℝ) : ℝ := Real.exp (-(q/4)*u)

def twiceIBPIntegrand (t q u : ℝ) : ℝ :=
  (q * Real.cosh u - q^2 * Real.sinh u^2) *
    amplitude q u * Real.cos (2*t*u)

/-- A genuine positive u-integral, not a spectral estimate parameter. -/
def secondPositiveMass (q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), secondPositiveEnvelope q u

lemma amplitude_pos (q u : ℝ) : 0 < amplitude q u := by
  exact Real.exp_pos _

lemma amplitude_hasDerivAt (q u : ℝ) :
    HasDerivAt (amplitude q) (amplitudeD1 q u) u := by
  convert ((Real.hasDerivAt_cosh u).const_mul (-q)).exp using 1 <;>
    dsimp [amplitude, amplitudeD1] <;> ring

lemma amplitudeD1_hasDerivAt (q u : ℝ) :
    HasDerivAt (amplitudeD1 q) (amplitudeD2 q u) u := by
  convert (((Real.hasDerivAt_sinh u).const_mul (-q)).mul
    (amplitude_hasDerivAt q u)) using 1 <;>
    dsimp [amplitudeD1, amplitudeD2, amplitude] <;> ring

lemma abs_sinh_le_cosh (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  rw [Real.sinh_eq, Real.cosh_eq]
  apply abs_le.mpr
  constructor <;> linarith [Real.exp_pos u, Real.exp_pos (-u)]

lemma half_amplitude_le_decay {q : ℝ} (hq : 0 < q) (u : ℝ) :
    Real.exp (-(q/2)*Real.cosh u) ≤ decayMajorant q u := by
  unfold decayMajorant
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (half_le_cosh u)
    (by positivity : 0 ≤ q/2)
  nlinarith

lemma amplitude_norm_le_decay {q : ℝ} (hq : 0 < q) (u : ℝ) :
    ‖amplitude q u‖ ≤ decayMajorant q u := by
  rw [Real.norm_eq_abs, abs_of_pos (amplitude_pos q u)]
  apply le_trans _ (half_amplitude_le_decay hq u)
  unfold amplitude
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hq.le (Real.cosh_pos u).le]

lemma first_polynomial_exp_bound (q u : ℝ) :
    q * Real.cosh u * amplitude q u ≤
      2 * Real.exp (-(q/2)*Real.cosh u) := by
  have hp : q * Real.cosh u ≤ 2 * Real.exp (q*Real.cosh u/2) := by
    have h := Real.add_one_le_exp (q*Real.cosh u/2)
    linarith
  calc
    q * Real.cosh u * amplitude q u ≤
        (2 * Real.exp (q*Real.cosh u/2)) * amplitude q u :=
      mul_le_mul_of_nonneg_right hp (amplitude_pos q u).le
    _ = 2 * Real.exp (-(q/2)*Real.cosh u) := by
      unfold amplitude
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

lemma second_polynomial_exp_bound {q : ℝ} (hq : 0 < q) (u : ℝ) :
    q^2 * Real.sinh u^2 * amplitude q u ≤
      8 * Real.exp (-(q/2)*Real.cosh u) := by
  have hx : 0 ≤ q*Real.cosh u/2 := by positivity
  have hp0 := Real.pow_div_factorial_le_exp hx 2
  norm_num at hp0
  have hp : (q*Real.cosh u)^2 ≤ 8 * Real.exp (q*Real.cosh u/2) := by
    nlinarith
  have hs : Real.sinh u^2 ≤ Real.cosh u^2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq u]
  have hqs : q^2 * Real.sinh u^2 ≤ (q*Real.cosh u)^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg q)]
  calc
    q^2 * Real.sinh u^2 * amplitude q u ≤
        (8 * Real.exp (q*Real.cosh u/2)) * amplitude q u :=
      mul_le_mul_of_nonneg_right (hqs.trans hp) (amplitude_pos q u).le
    _ = 8 * Real.exp (-(q/2)*Real.cosh u) := by
      unfold amplitude
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

lemma amplitudeD1_norm_le_decay {q : ℝ} (hq : 0 < q) (u : ℝ) :
    ‖amplitudeD1 q u‖ ≤ 2 * decayMajorant q u := by
  calc
    ‖amplitudeD1 q u‖ = q * |Real.sinh u| * amplitude q u := by
      simp only [amplitudeD1, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_pos hq, abs_of_pos (amplitude_pos q u)]
    _ ≤ q * Real.cosh u * amplitude q u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_sinh_le_cosh u) hq.le)
        (amplitude_pos q u).le
    _ ≤ 2 * Real.exp (-(q/2)*Real.cosh u) := first_polynomial_exp_bound q u
    _ ≤ 2 * decayMajorant q u :=
      mul_le_mul_of_nonneg_left (half_amplitude_le_decay hq u) (by norm_num)

lemma secondPositiveEnvelope_nonneg {q : ℝ} (hq : 0 < q) (u : ℝ) :
    0 ≤ secondPositiveEnvelope q u := by
  unfold secondPositiveEnvelope
  positivity

lemma secondPositiveEnvelope_le_decay {q : ℝ} (hq : 0 < q) (u : ℝ) :
    secondPositiveEnvelope q u ≤ 10 * decayMajorant q u := by
  have h1 := first_polynomial_exp_bound q u
  have h2 := second_polynomial_exp_bound hq u
  have h3 := half_amplitude_le_decay hq u
  unfold secondPositiveEnvelope
  nlinarith

lemma amplitudeD2_norm_le_envelope {q : ℝ} (hq : 0 < q) (u : ℝ) :
    ‖amplitudeD2 q u‖ ≤ secondPositiveEnvelope q u := by
  have ha : 0 ≤ q * Real.cosh u := by positivity
  have hb : 0 ≤ q^2 * Real.sinh u^2 := by positivity
  have hc : |q^2 * Real.sinh u^2 - q * Real.cosh u| ≤
      q * Real.cosh u + q^2 * Real.sinh u^2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [amplitudeD2, secondPositiveEnvelope, Real.norm_eq_abs,
    abs_mul, abs_of_pos (amplitude_pos q u)] using
    mul_le_mul_of_nonneg_right hc (amplitude_pos q u).le

lemma decayMajorant_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (decayMajorant q) (Ioi 0) := by
  exact integrableOn_exp_mul_Ioi (by linarith : -(q/4) < 0) 0

lemma decayMajorant_tendsto_zero {q : ℝ} (hq : 0 < q) :
    Tendsto (decayMajorant q) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (by linarith : -(q/4) < 0)).2 tendsto_id)

lemma amplitude_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (amplitude q) (Ioi 0) := by
  simpa only [kIntegrand, zero_mul, mul_zero, Real.cos_zero, mul_one, amplitude] using
    kIntegrand_integrable 0 hq

lemma amplitudeD1_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (amplitudeD1 q) (Ioi 0) := by
  have hc : Continuous (amplitudeD1 q) := by
    unfold amplitudeD1 amplitude
    fun_prop
  exact ((decayMajorant_integrable hq).const_mul 2).mono'
    hc.aestronglyMeasurable
    (Eventually.of_forall (amplitudeD1_norm_le_decay hq))

lemma secondPositiveEnvelope_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (secondPositiveEnvelope q) (Ioi 0) := by
  have hc : Continuous (secondPositiveEnvelope q) := by
    unfold secondPositiveEnvelope amplitude
    fun_prop
  apply ((decayMajorant_integrable hq).const_mul 10).mono' hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (secondPositiveEnvelope_nonneg hq u)]
  exact secondPositiveEnvelope_le_decay hq u

lemma amplitudeD2_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (amplitudeD2 q) (Ioi 0) := by
  have hc : Continuous (amplitudeD2 q) := by
    unfold amplitudeD2 amplitude
    fun_prop
  exact (secondPositiveEnvelope_integrable hq).mono' hc.aestronglyMeasurable
    (Eventually.of_forall (amplitudeD2_norm_le_envelope hq))

/-- The only bounded-factor helper; all applications below use proved actual
amplitudes. Its premise is an ordinary integrability theorem, never a
desired height-decay or spectral estimate. -/
lemma integrable_mul_cos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (b : ℝ) :
    IntegrableOn (fun u => f u * Real.cos (b*u)) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => Real.cos (b*u)) := by fun_prop
  exact hf.mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall (fun u => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (b*u)))

lemma integrable_mul_sin {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (b : ℝ) :
    IntegrableOn (fun u => f u * Real.sin (b*u)) (Ioi 0) := by
  have hc : Continuous (fun u : ℝ => Real.sin (b*u)) := by fun_prop
  exact hf.mul_bdd hc.aestronglyMeasurable
    (Eventually.of_forall (fun u => by
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (b*u)))

lemma linear_sin_hasDerivAt (b u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (b*x)) (b*Real.cos (b*u)) u := by
  convert ((hasDerivAt_id u).const_mul b).sin using 1 <;> ring

lemma linear_cos_hasDerivAt (b u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (b*x)) (-b*Real.sin (b*u)) u := by
  convert ((hasDerivAt_id u).const_mul b).cos using 1 <;> ring

lemma first_boundary_zero (q b : ℝ) :
    Tendsto (fun u => amplitude q u * Real.sin (b*u)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun u : ℝ => amplitude q u * Real.sin (b*u)) := by
    unfold amplitude
    fun_prop
  have ht : Tendsto (fun u : ℝ => amplitude q u * Real.sin (b*u)) (𝓝 0)
      (𝓝 (amplitude q 0 * Real.sin (b*0))) := hc.continuousAt
  simpa only [mul_zero, Real.sin_zero] using ht.mono_left inf_le_left

lemma second_boundary_zero (q b : ℝ) :
    Tendsto (fun u => amplitudeD1 q u * Real.cos (b*u)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun u : ℝ => amplitudeD1 q u * Real.cos (b*u)) := by
    unfold amplitudeD1 amplitude
    fun_prop
  have ht : Tendsto (fun u : ℝ => amplitudeD1 q u * Real.cos (b*u)) (𝓝 0)
      (𝓝 (amplitudeD1 q 0 * Real.cos (b*0))) := hc.continuousAt
  simpa only [amplitudeD1, Real.sinh_zero, mul_zero, zero_mul] using
    ht.mono_left inf_le_left

lemma first_boundary_infty {q : ℝ} (hq : 0 < q) (b : ℝ) :
    Tendsto (fun u => amplitude q u * Real.sin (b*u)) atTop (𝓝 0) := by
  apply squeeze_zero_norm _ (decayMajorant_tendsto_zero hq)
  intro u
  calc
    ‖amplitude q u * Real.sin (b*u)‖ ≤ ‖amplitude q u‖ * 1 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (b*u))
        (norm_nonneg _)
    _ ≤ decayMajorant q u := by
      simpa only [mul_one] using amplitude_norm_le_decay hq u

lemma second_boundary_infty {q : ℝ} (hq : 0 < q) (b : ℝ) :
    Tendsto (fun u => amplitudeD1 q u * Real.cos (b*u)) atTop (𝓝 0) := by
  have hm : Tendsto (fun u => 2 * decayMajorant q u) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decayMajorant_tendsto_zero hq).const_mul 2
  apply squeeze_zero_norm _ hm
  intro u
  calc
    ‖amplitudeD1 q u * Real.cos (b*u)‖ ≤ ‖amplitudeD1 q u‖ * 1 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (b*u))
        (norm_nonneg _)
    _ ≤ 2 * decayMajorant q u := by
      simpa only [mul_one] using amplitudeD1_norm_le_decay hq u

lemma twiceIBPIntegrand_eq (t q u : ℝ) :
    twiceIBPIntegrand t q u = - (amplitudeD2 q u * Real.cos (2*t*u)) := by
  unfold twiceIBPIntegrand amplitudeD2
  ring

lemma twiceIBPIntegrand_integrable (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (twiceIBPIntegrand t q) (Ioi 0) := by
  have h := (integrable_mul_cos (amplitudeD2_integrable hq) (2*t)).neg
  exact h.congr (Eventually.of_forall (fun u => (twiceIBPIntegrand_eq t q u).symm))

/-- Both endpoint products vanish; all integrability premises of the actual
improper IBP theorem have already been proved above. This identity includes
t=0 and hence does not divide by a vanishing spectral height. -/
theorem imaginaryOrderK_twiceIBP_mul (t : ℝ) {q : ℝ} (hq : 0 < q) :
    4*t^2 * imaginaryOrderK t q =
      ∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u := by
  let J : ℝ := ∫ u in Ioi (0 : ℝ), amplitudeD1 q u * Real.sin (2*t*u)
  let H : ℝ := ∫ u in Ioi (0 : ℝ), amplitudeD2 q u * Real.cos (2*t*u)
  have hJ := integrable_mul_sin (amplitudeD1_integrable hq) (2*t)
  have hK := kIntegrand_integrable t hq
  have hH := integrable_mul_cos (amplitudeD2_integrable hq) (2*t)
  have hsum1 : IntegrableOn
      ((amplitudeD1 q) * (fun u => Real.sin (2*t*u)) +
        (amplitude q) * (fun u => (2*t)*Real.cos (2*t*u))) (Ioi 0) := by
    apply (hJ.add (hK.const_mul (2*t))).congr
    exact Eventually.of_forall (fun u => by
      simp only [Pi.add_apply, Pi.mul_apply, kIntegrand, amplitude]
      ring)
  have hp1 := integral_Ioi_deriv_mul_eq_sub
    (u := amplitude q) (u' := amplitudeD1 q)
    (v := fun u => Real.sin (2*t*u)) (v' := fun u => (2*t)*Real.cos (2*t*u))
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (fun u _ => amplitude_hasDerivAt q u)
    (fun u _ => linear_sin_hasDerivAt (2*t) u)
    hsum1 (first_boundary_zero q (2*t)) (first_boundary_infty hq (2*t))
  have h1 : J + (2*t)*imaginaryOrderK t q = 0 := by
    calc
      J + (2*t)*imaginaryOrderK t q =
          ∫ u in Ioi (0 : ℝ), amplitudeD1 q u * Real.sin (2*t*u) +
            (2*t)*kIntegrand t q u := by
        rw [integral_add hJ (hK.const_mul (2*t)), integral_const_mul]
        rfl
      _ = ∫ u in Ioi (0 : ℝ), amplitudeD1 q u * Real.sin (2*t*u) +
          amplitude q u * ((2*t)*Real.cos (2*t*u)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by unfold kIntegrand amplitude; ring)
      _ = 0 := by simpa only [sub_self] using hp1
  have hsum2 : IntegrableOn
      ((amplitudeD2 q) * (fun u => Real.cos (2*t*u)) +
        (amplitudeD1 q) * (fun u => -(2*t)*Real.sin (2*t*u))) (Ioi 0) := by
    apply (hH.add (hJ.const_mul (-(2*t)))).congr
    exact Eventually.of_forall (fun u => by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring)
  have hp2 := integral_Ioi_deriv_mul_eq_sub
    (u := amplitudeD1 q) (u' := amplitudeD2 q)
    (v := fun u => Real.cos (2*t*u)) (v' := fun u => -(2*t)*Real.sin (2*t*u))
    (a := (0 : ℝ)) (a' := (0 : ℝ)) (b' := (0 : ℝ))
    (fun u _ => amplitudeD1_hasDerivAt q u)
    (fun u _ => linear_cos_hasDerivAt (2*t) u)
    hsum2 (second_boundary_zero q (2*t)) (second_boundary_infty hq (2*t))
  have h2 : H + (-(2*t))*J = 0 := by
    calc
      H + (-(2*t))*J =
          ∫ u in Ioi (0 : ℝ), amplitudeD2 q u * Real.cos (2*t*u) +
            (-(2*t))*(amplitudeD1 q u * Real.sin (2*t*u)) := by
        rw [integral_add hH (hJ.const_mul (-(2*t))), integral_const_mul]
        rfl
      _ = ∫ u in Ioi (0 : ℝ), amplitudeD2 q u * Real.cos (2*t*u) +
          amplitudeD1 q u * (-(2*t)*Real.sin (2*t*u)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun u => by ring)
      _ = 0 := by simpa only [sub_self] using hp2
  have hHvalue : H + (2*t)^2 * imaginaryOrderK t q = 0 := by
    linear_combination h2 + (2*t)*h1
  have hI : (∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u) = -H := by
    calc
      (∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u) =
          ∫ u in Ioi (0 : ℝ), -(amplitudeD2 q u * Real.cos (2*t*u)) := by
        apply integral_congr_ae
        exact Eventually.of_forall (twiceIBPIntegrand_eq t q)
      _ = -H := integral_neg _
  linear_combination hHvalue - hI

/-- The requested twice-integrated formula, with its exact positive sign. -/
theorem imaginaryOrderK_twiceIBP {t q : ℝ} (ht : t ≠ 0) (hq : 0 < q) :
    imaginaryOrderK t q = (1/(4*t^2)) *
      ∫ u in Ioi (0 : ℝ),
        (q * Real.cosh u - q^2 * Real.sinh u^2) *
          Real.exp (-q*Real.cosh u) * Real.cos (2*t*u) := by
  have hd : 4*t^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  calc
    imaginaryOrderK t q =
        (∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u) / (4*t^2) :=
      (eq_div_iff hd).2 (by
        simpa only [mul_comm] using imaginaryOrderK_twiceIBP_mul t hq)
    _ = (1/(4*t^2)) *
        ∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u := by ring
    _ = _ := rfl

lemma twiceIBPIntegrand_norm_le_envelope (t : ℝ) {q : ℝ} (hq : 0 < q) (u : ℝ) :
    ‖twiceIBPIntegrand t q u‖ ≤ secondPositiveEnvelope q u := by
  rw [twiceIBPIntegrand_eq, norm_neg, norm_mul]
  calc
    ‖amplitudeD2 q u‖ * ‖Real.cos (2*t*u)‖ ≤ ‖amplitudeD2 q u‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2*t*u))
        (norm_nonneg _)
    _ ≤ secondPositiveEnvelope q u := by
      simpa only [mul_one] using amplitudeD2_norm_le_envelope hq u

theorem secondPositiveMass_nonneg {q : ℝ} (hq : 0 < q) :
    0 ≤ secondPositiveMass q := by
  exact integral_nonneg (secondPositiveEnvelope_nonneg hq)

theorem imaginaryOrderK_abs_le_positiveMass {t q : ℝ} (ht : t ≠ 0) (hq : 0 < q) :
    |imaginaryOrderK t q| ≤ (1/(4*t^2)) * secondPositiveMass q := by
  have hi : |∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u| ≤ secondPositiveMass q := by
    simpa only [Real.norm_eq_abs, secondPositiveMass] using
      norm_integral_le_of_norm_le (secondPositiveEnvelope_integrable hq)
        (Eventually.of_forall (twiceIBPIntegrand_norm_le_envelope t hq))
  have hd : 0 ≤ (1/(4*t^2) : ℝ) := by positivity
  calc
    |imaginaryOrderK t q| =
        (1/(4*t^2)) * |∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u| := by
      rw [imaginaryOrderK_twiceIBP ht hq, abs_mul, abs_of_nonneg hd]
      rfl
    _ ≤ (1/(4*t^2)) * secondPositiveMass q :=
      mul_le_mul_of_nonneg_left hi hd

lemma decayMajorant_integral {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), decayMajorant q u) = 4/q := by
  change (∫ u in Ioi (0 : ℝ), Real.exp (-(q/4)*u)) = 4/q
  rw [integral_exp_mul_Ioi (by linarith : -(q/4) < 0) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp [hq.ne']

theorem secondPositiveMass_le {q : ℝ} (hq : 0 < q) :
    secondPositiveMass q ≤ 40/q := by
  calc
    secondPositiveMass q ≤ ∫ u in Ioi (0 : ℝ), 10*decayMajorant q u :=
      integral_mono (secondPositiveEnvelope_integrable hq)
        ((decayMajorant_integrable hq).const_mul 10)
        (secondPositiveEnvelope_le_decay hq)
    _ = 40/q := by
      rw [integral_const_mul, decayMajorant_integral hq]
      ring

/-- Concrete height decay for the already defined actual K integral.
All u-integral envelopes and all endpoint limits have been proved. -/
theorem imaginaryOrderK_abs_le_quadratic {t q : ℝ} (ht : t ≠ 0) (hq : 0 < q) :
    |imaginaryOrderK t q| ≤ 10/(q*t^2) := by
  calc
    |imaginaryOrderK t q| ≤ (1/(4*t^2)) * secondPositiveMass q :=
      imaginaryOrderK_abs_le_positiveMass ht hq
    _ ≤ (1/(4*t^2)) * (40/q) :=
      mul_le_mul_of_nonneg_left (secondPositiveMass_le hq) (by positivity)
    _ = 10/(q*t^2) := by field_simp [ht, hq.ne']; ring

/-- Preserve the actual dq/q kernel normalizer. -/
theorem imaginaryOrderK_div_norm_le_quadratic {t q : ℝ}
    (ht : t ≠ 0) (hq : 0 < q) :
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 10/(q^2*t^2) := by
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ = |imaginaryOrderK t q|/q := by
      simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    _ ≤ (10/(q*t^2))/q :=
      div_le_div_of_nonneg_right (imaginaryOrderK_abs_le_quadratic ht hq) hq.le
    _ = 10/(q^2*t^2) := by field_simp [ht, hq.ne']; ring

/-- Actual packet support gives q>0 and its lower scale automatically. -/
theorem extendedKKernel_norm_le_quadratic_on_region {ι : Type*} (P : PacketData ι)
    {t : ℝ} (ht : t ≠ 0) (q : ℝ) (hq : q ∈ P.region) :
    ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t q‖ ≤
      2560/(P.Y0^2*t^2) := by
  rw [extendedKKernel_eq_on_physical_region P t q hq]
  have hlow : 0 < P.Y0/16 := by have h := P.Y0_pos; positivity
  have hqp : 0 < q := lt_of_lt_of_le hlow hq.1
  have hsq : (P.Y0/16)^2 ≤ q^2 := by
    gcongr
    exact hq.1
  have ht2 : 0 < t^2 := sq_pos_iff.mpr ht
  calc
    ‖(imaginaryOrderK t q : ℂ)/(q : ℂ)‖ ≤ 10/(q^2*t^2) :=
      imaginaryOrderK_div_norm_le_quadratic ht hqp
    _ ≤ 10/((P.Y0/16)^2*t^2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_right hsq ht2.le)
    _ = 2560/(P.Y0^2*t^2) := by field_simp [ht, P.Y0_pos.ne']; ring

/-- Sup norm of the specific actual restricted K kernel, at nonzero height. -/
theorem restrictedKKernel_norm_le_quadratic {ι : Type*} (P : PacketData ι)
    {t : ℝ} (ht : t ≠ 0) :
    ‖restrictedKKernel P t‖ ≤ 2560/(P.Y0^2*t^2) := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤
    2560/(P.Y0^2*t^2))).mpr
  intro q
  change ‖extendedKKernel (P.Y0/32) (by have h := P.Y0_pos; positivity) t
    (q : ℝ)‖ ≤ 2560/(P.Y0^2*t^2)
  exact extendedKKernel_norm_le_quadratic_on_region P ht (q : ℝ) q.property

end
end ImbalancedChen.Part3.ImaginaryOrderKHeightDecaySourceOnly
