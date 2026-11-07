import ImbalancedChen.Part3HalfCosinePlancherel

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The continuous, full-axis cross-K kernel follows from the genuine L2
Fourier inner-product isometry. No cross identity, Plancherel formula,
finite Gram assertion, or spectral estimate is a hypothesis.
-/

noncomputable section

namespace ImbalancedChen.Part3.CrossKPlancherelSourceOnly

open MeasureTheory FourierTransform
open scoped FourierTransform ComplexInnerProductSpace ComplexConjugate
open FourierL1L2PlancherelSourceOnly HalfCosinePlancherelSourceOnly
open KFullLineFourierBridgeSourceOnly P3ActualKProfileLpSourceOnly
open ImaginaryOrderKBesselSourceOnly

/-- The actual pointwise inner product of two L2 functions is integrable. -/
theorem integrable_inner_of_memLp {f g : ℝ → ℂ}
    (hf : MemLp f 2) (hg : MemLp g 2) :
    Integrable (fun x : ℝ => inner ℂ (f x) (g x)) := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx]

/-- Inner-product Plancherel for the actual integral Fourier transform.
The a.e. representative bridge was proved in the preceding module. -/
theorem integral_inner_fourier {f g : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    (∫ ξ : ℝ, inner ℂ (𝓕 f ξ) (𝓕 g ξ)) =
      ∫ u : ℝ, inner ℂ (f u) (g u) := by
  calc
    _ = ∫ ξ : ℝ, inner ℂ
        ((𝓕 (hf₂.toLp f) : Lp ℂ 2) ξ)
        ((𝓕 (hg₂.toLp g) : Lp ℂ 2) ξ) := by
      apply integral_congr_ae
      filter_upwards [fourier_toLp_ae_eq hf₁ hf₂,
        fourier_toLp_ae_eq hg₁ hg₂] with ξ hfξ hgξ
      rw [hfξ, hgξ]
    _ = inner ℂ (𝓕 (hf₂.toLp f)) (𝓕 (hg₂.toLp g)) :=
      (L2.inner_def _ _).symm
    _ = inner ℂ (hf₂.toLp f) (hg₂.toLp g) :=
      Lp.inner_fourier_eq _ _
    _ = ∫ u : ℝ, inner ℂ (hf₂.toLp f u) (hg₂.toLp g u) :=
      L2.inner_def _ _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with u hfu hgu
      rw [hfu, hgu]

private theorem inner_half_mul (a b : ℂ) :
    inner ℂ ((1 / 2 : ℂ) * a) ((1 / 2 : ℂ) * b) =
      (1 / 4 : ℂ) * inner ℂ a b := by
  simp [RCLike.inner_apply'] <;> ring

/-- The same genuine inner-product identity with the exact K frequency
and half-transform normalization. -/
theorem integral_inner_half_rescaled_fourier {f g : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    (∫ t : ℝ, inner ℂ ((1 / 2 : ℂ) * 𝓕 f (t / Real.pi))
        ((1 / 2 : ℂ) * 𝓕 g (t / Real.pi))) =
      ((Real.pi : ℂ) / 4) * ∫ u : ℝ, inner ℂ (f u) (g u) := by
  calc
    _ = (1 / 4 : ℂ) * ∫ t : ℝ,
        inner ℂ (𝓕 f (t / Real.pi)) (𝓕 g (t / Real.pi)) := by
      simp_rw [inner_half_mul]
      rw [integral_const_mul]
    _ = (1 / 4 : ℂ) * ((Real.pi : ℂ) *
        ∫ ξ : ℝ, inner ℂ (𝓕 f ξ) (𝓕 g ξ)) := by
      rw [Measure.integral_comp_div
        (fun ξ : ℝ => inner ℂ (𝓕 f ξ) (𝓕 g ξ)) Real.pi]
      simp [abs_of_pos Real.pi_pos, Complex.real_smul]
    _ = _ := by rw [integral_inner_fourier hf₁ hf₂ hg₁ hg₂]; ring

theorem integrable_inner_half_rescaled_fourier {f g : ℝ → ℂ}
    (hf₁ : Integrable f) (hf₂ : MemLp f 2)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) :
    Integrable (fun t : ℝ =>
      inner ℂ ((1 / 2 : ℂ) * 𝓕 f (t / Real.pi))
        ((1 / 2 : ℂ) * 𝓕 g (t / Real.pi))) := by
  have h := integrable_inner_of_memLp (memLp_fourier hf₁ hf₂)
    (memLp_fourier hg₁ hg₂)
  refine ((h.comp_div Real.pi_ne_zero).const_mul (1 / 4 : ℂ)).congr ?_
  filter_upwards with t
  exact (inner_half_mul _ _).symm

/-- Multiplication of the real positive profiles adds their q parameters. -/
theorem kEvenProfile_inner (q r u : ℝ) :
    inner ℂ (kEvenProfile q u) (kEvenProfile r u) =
      kEvenProfile (q + r) u := by
  simp only [kEvenProfile, evenLaplaceProfile, RCLike.inner_apply',
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- The zero-frequency case of the already established actual Fourier
bridge computes the full-line profile integral, with its factor two. -/
theorem integral_kEvenProfile {q : ℝ} (hq : 0 < q) :
    (∫ u : ℝ, kEvenProfile q u) = (2 : ℂ) * (imaginaryOrderK 0 q : ℂ) := by
  simpa [Real.fourier_eq] using fourier_kEvenProfile_eq q 0 hq

theorem integral_inner_kEvenProfile {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    (∫ u : ℝ, inner ℂ (kEvenProfile q u) (kEvenProfile r u)) =
      (2 : ℂ) * (imaginaryOrderK 0 (q + r) : ℂ) := by
  simp_rw [kEvenProfile_inner]
  exact integral_kEvenProfile (add_pos hq hr)

private theorem inner_half_fourier_K {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) (t : ℝ) :
    inner ℂ ((1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / Real.pi))
      ((1 / 2 : ℂ) * 𝓕 (kEvenProfile r) (t / Real.pi)) =
        ((imaginaryOrderK t q * imaginaryOrderK t r : ℝ) : ℂ) := by
  rw [← imaginaryOrderK_eq_half_fourier t q hq,
    ← imaginaryOrderK_eq_half_fourier t r hr]
  simp [RCLike.inner_apply', Complex.ofReal_mul]

/-- Absolute integrability of the real cross-K product on the full axis. -/
theorem imaginaryOrderK_mul_integrable {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    Integrable (fun t : ℝ => imaginaryOrderK t q * imaginaryOrderK t r) := by
  have h := integrable_inner_half_rescaled_fourier
    (kEvenProfile_integrable hq) (kEvenProfile_memLp_two hq)
    (kEvenProfile_integrable hr) (kEvenProfile_memLp_two hr)
  refine h.re.congr ?_
  filter_upwards with t
  rw [inner_half_fourier_K hq hr t, Complex.ofReal_re]

/-- The continuous full-axis cross-K kernel, with actual q,r>0 inputs. -/
theorem imaginaryOrderK_cross_plancherel {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    (∫ t : ℝ, imaginaryOrderK t q * imaginaryOrderK t r) =
      (Real.pi / 2) * imaginaryOrderK 0 (q + r) := by
  apply Complex.ofReal_injective
  calc
    ((∫ t : ℝ, imaginaryOrderK t q * imaginaryOrderK t r : ℝ) : ℂ) =
        ∫ t : ℝ, inner ℂ
          ((1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / Real.pi))
          ((1 / 2 : ℂ) * 𝓕 (kEvenProfile r) (t / Real.pi)) := by
      rw [← integral_ofReal]
      apply integral_congr_ae
      filter_upwards with t
      exact (inner_half_fourier_K hq hr t).symm
    _ = ((Real.pi : ℂ) / 4) *
        ∫ u : ℝ, inner ℂ (kEvenProfile q u) (kEvenProfile r u) :=
      integral_inner_half_rescaled_fourier
        (kEvenProfile_integrable hq) (kEvenProfile_memLp_two hq)
        (kEvenProfile_integrable hr) (kEvenProfile_memLp_two hr)
    _ = ((Real.pi : ℂ) / 4) *
        ((2 : ℂ) * (imaginaryOrderK 0 (q + r) : ℂ)) := by
      rw [integral_inner_kEvenProfile hq hr]
    _ = (((Real.pi / 2) * imaginaryOrderK 0 (q + r) : ℝ) : ℂ) := by
      push_cast
      ring

/-- The squared L2 distance between two actual order profiles is integrable. -/
theorem imaginaryOrderK_sub_sq_integrable {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    Integrable (fun t : ℝ => |imaginaryOrderK t q - imaginaryOrderK t r| ^ 2) := by
  have hq₂ : Integrable (fun t : ℝ => imaginaryOrderK t q ^ 2) := by
    simpa only [sq_abs] using imaginaryOrderK_sq_integrable hq
  have hr₂ : Integrable (fun t : ℝ => imaginaryOrderK t r ^ 2) := by
    simpa only [sq_abs] using imaginaryOrderK_sq_integrable hr
  refine ((hq₂.add hr₂).sub
    ((imaginaryOrderK_mul_integrable hq hr).const_mul 2)).congr ?_
  filter_upwards with t
  simp only [sq_abs]
  ring

/-- Exact two-point squared L2 distance. This is an integral identity
for the actual full-axis K functions, not a finite sampled Gram identity. -/
theorem imaginaryOrderK_l2_distance_sq {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r) :
    (∫ t : ℝ, |imaginaryOrderK t q - imaginaryOrderK t r| ^ 2) =
      (Real.pi / 2) * (imaginaryOrderK 0 (2 * q) +
        imaginaryOrderK 0 (2 * r) - 2 * imaginaryOrderK 0 (q + r)) := by
  have hq₂ : Integrable (fun t : ℝ => imaginaryOrderK t q ^ 2) := by
    simpa only [sq_abs] using imaginaryOrderK_sq_integrable hq
  have hr₂ : Integrable (fun t : ℝ => imaginaryOrderK t r ^ 2) := by
    simpa only [sq_abs] using imaginaryOrderK_sq_integrable hr
  have hqr := imaginaryOrderK_mul_integrable hq hr
  have hdiagq : (∫ t : ℝ, imaginaryOrderK t q ^ 2) =
      (Real.pi / 2) * imaginaryOrderK 0 (2 * q) := by
    simpa only [sq_abs] using imaginaryOrderK_plancherel hq
  have hdiagr : (∫ t : ℝ, imaginaryOrderK t r ^ 2) =
      (Real.pi / 2) * imaginaryOrderK 0 (2 * r) := by
    simpa only [sq_abs] using imaginaryOrderK_plancherel hr
  calc
    _ = ∫ t : ℝ, (imaginaryOrderK t q ^ 2 + imaginaryOrderK t r ^ 2 -
        2 * (imaginaryOrderK t q * imaginaryOrderK t r)) := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [sq_abs]
      ring
    _ = (∫ t : ℝ, imaginaryOrderK t q ^ 2) +
        (∫ t : ℝ, imaginaryOrderK t r ^ 2) -
        2 * (∫ t : ℝ, imaginaryOrderK t q * imaginaryOrderK t r) := by
      rw [integral_sub (hq₂.add hr₂) (hqr.const_mul 2),
        integral_add hq₂ hr₂, integral_const_mul]
    _ = _ := by
      rw [hdiagq, hdiagr, imaginaryOrderK_cross_plancherel hq hr]
      ring

end ImbalancedChen.Part3.CrossKPlancherelSourceOnly
