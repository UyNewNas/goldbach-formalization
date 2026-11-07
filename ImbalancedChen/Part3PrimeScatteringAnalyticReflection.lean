import ImbalancedChen.Part3PrimePhysicalScattering

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The prime physical coefficient matrix has a genuine complex analytic
central extension. Its scalar is expressed using the entire Lambda_0 and
the already constructed pole-removed denominator Q. The formula
  (2s) Q(s-1/2) / ((2s-2) Q(s))
equals Lambda(2s-1)/Lambda(2s) off the center on its explicit domain and
has value -1 at s=1/2. No totalized pole value supplies the center.

True completed-zeta conjugation and the positive-real-base complex power
then identify S(-t) with S(t)^*, giving S(t)S(-t)=I for the physical matrix.
This is coefficient scattering for the identified two physical charts;
no spectral completeness or automorphic Plancherel measure follows here.
-/

noncomputable section
open Set Complex Filter Topology
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimePhysicalScattering20261026b
open ImbalancedChen.Part3.CriticalEisensteinScattering20261025a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a

namespace ImbalancedChen.Part3.PrimeScatteringAnalytic20261026b

/-- Algebraic pole removal for Lambda itself, including nonpositive real
parts away from the two explicitly excluded poles. Gamma is unused here. -/
theorem reciprocalDenominator_eq_lambda (s : ℂ) (hs0 : s ≠ 0)
    (hsh : s ≠ 1 / 2) :
    reciprocalDenominator s = polePolynomial s * completedRiemannZeta (2 * s) := by
  have h20 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have h21 : 1 - 2 * s ≠ 0 := by
    intro h
    apply hsh
    linear_combination -(1 / 2 : ℂ) * h
  rw [completedRiemannZeta_eq]
  unfold reciprocalDenominator polePolynomial
  field_simp [h20, h21]
  <;> ring

def regularScattering (s : ℂ) : ℂ :=
  (2 * s) * reciprocalDenominator (s - 1 / 2) /
    ((2 * s - 2) * reciprocalDenominator s)

@[simp] theorem regularScattering_half : regularScattering (1 / 2 : ℂ) = -1 := by
  norm_num [regularScattering, reciprocalDenominator, polePolynomial]

private theorem twice_sub_two_ne_zero {s : ℂ} (hs : s ≠ 1) : 2 * s - 2 ≠ 0 := by
  intro h
  apply hs
  linear_combination (1 / 2 : ℂ) * h

theorem regularScattering_analyticOnNhd :
    AnalyticOnNhd ℂ regularScattering centralNormalizationDomain := by
  intro s hs
  have hQshift : AnalyticAt ℂ (fun w : ℂ => reciprocalDenominator (w - 1 / 2)) s :=
    (reciprocalDenominator_analyticAt (s - 1 / 2)).comp
      (analyticAt_id.sub_const (1 / 2 : ℂ))
  exact ((analyticAt_id.const_mul (2 : ℂ)).mul hQshift).div
    (((analyticAt_id.const_mul (2 : ℂ)).sub_const 2).mul
      (reciprocalDenominator_analyticAt s))
    (mul_ne_zero (twice_sub_two_ne_zero hs.2.1) hs.2.2)

/-- Equality on an honest zero-free domain, not a global nonvanishing
assumption for zeta. This denominator's nonzero value follows from Q. -/
theorem regularScattering_eq_completed (s : ℂ)
    (hs : s ∈ centralNormalizationDomain) (hc : s ≠ 1 / 2) :
    regularScattering s = completedScattering s := by
  have hs0 : s ≠ 0 := by intro h; subst s; simpa using hs.1
  have hshift0 : s - 1 / 2 ≠ 0 := sub_ne_zero.mpr hc
  have hshifthalf : s - 1 / 2 ≠ 1 / 2 := by
    intro h
    apply hs.2.1
    linear_combination h
  have h20 : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have h21 : 2 * s - 1 ≠ 0 := by
    intro h
    apply hc
    linear_combination (1 / 2 : ℂ) * h
  have h22 := twice_sub_two_ne_zero hs.2.1
  have hden : completedRiemannZeta (2 * s) ≠ 0 := by
    intro h
    apply hs.2.2
    rw [reciprocalDenominator_eq_lambda s hs0 hc, h, mul_zero]
  have hshift : reciprocalDenominator (s - 1 / 2) =
      ((2 * s - 1) * (2 * s - 2)) * completedRiemannZeta (2 * s - 1) := by
    rw [reciprocalDenominator_eq_lambda _ hshift0 hshifthalf, polePolynomial,
      show 2 * (s - 1 / 2) = 2 * s - 1 by ring]
    ring
  rw [regularScattering, hshift, reciprocalDenominator_eq_lambda s hs0 hc,
    polePolynomial, completedScattering]
  field_simp [h20, h21, h22, hden]
  <;> ring

/-- The analytic extension agrees with the existing true residue-based
critical scalar, including the center. -/
theorem regularScattering_critical (t : ℝ) :
    regularScattering (criticalParameter t) = criticalScattering t := by
  by_cases ht : t = 0
  · subst t
    simpa [criticalParameter] using regularScattering_half
  rw [regularScattering_eq_completed _ (criticalParameter_mem_centralDomain t)
      (criticalParameter_ne_half ht), criticalScattering_of_ne_zero t ht]
  exact completedScattering_eq_complexScattering _
    (by rw [criticalParameter_re]; norm_num) (critical_gamma_shift_legal t ht)

theorem primeRatio_analyticAt {p : ℕ} (hp : p.Prime) (s : ℂ) :
    AnalyticAt ℂ (primeRatio p) s := by
  have hneg : Differentiable ℂ (fun w : ℂ => -w) := differentiable_id.neg
  have hq := hneg.const_cpow (.inl (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℂ) ≠ 0))
  exact hq.analyticAt s

theorem primeDiagonal_analyticAt {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ (primeDiagonal p) s := by
  have hq := primeRatio_analyticAt hp s
  exact (analyticAt_const.mul (hq.pow 2)).div (analyticAt_const.sub (hq.pow 2))
    (prime_local_denominator_ne_zero hp hs)

theorem primeOffDiagonal_analyticAt {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 0 < s.re) : AnalyticAt ℂ (primeOffDiagonal p) s := by
  have hq := primeRatio_analyticAt hp s
  exact (hq.mul (analyticAt_const.sub (analyticAt_const.mul (hq.pow 2)))).div
    (analyticAt_const.sub (hq.pow 2)) (prime_local_denominator_ne_zero hp hs)

def primeAnalyticMatrix (p : ℕ) (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => regularScattering s * primeLocalMatrix p s i j

/-- A genuine complex neighborhood statement for every coefficient. -/
theorem primeAnalyticMatrix_entry_analyticOnNhd {p : ℕ} (hp : p.Prime)
    (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun s => primeAnalyticMatrix p s i j) centralNormalizationDomain := by
  intro s hs
  have hscalar := regularScattering_analyticOnNhd s hs
  have ha := hscalar.mul (primeDiagonal_analyticAt hp hs.1)
  have hb := hscalar.mul (primeOffDiagonal_analyticAt hp hs.1)
  fin_cases i <;> fin_cases j
  · simpa [primeAnalyticMatrix, primeLocalMatrix] using ha
  · simpa [primeAnalyticMatrix, primeLocalMatrix] using hb
  · simpa [primeAnalyticMatrix, primeLocalMatrix] using hb
  · simpa [primeAnalyticMatrix, primeLocalMatrix] using ha

theorem primeAnalyticMatrix_critical (p : ℕ) (t : ℝ) :
    primeAnalyticMatrix p (criticalParameter t) = primeScatteringMatrix p t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeAnalyticMatrix, primeLocalMatrix, primeScatteringMatrix,
      primeCriticalDiagonal, primeCriticalOffDiagonal, regularScattering_critical]

theorem primeAnalyticMatrix_half {p : ℕ} (hp : p.Prime) :
    primeAnalyticMatrix p (1 / 2) = -1 := by
  have h := (primeAnalyticMatrix_critical p 0).trans (primeScatteringMatrix_center hp)
  simpa [criticalParameter] using h

/-- The genuine completed denominator at -t is its conjugate at t. -/
private theorem critical_completed_denominator_neg (t : ℝ) :
    completedRiemannZeta (2 * criticalParameter (-t)) =
      conj (completedRiemannZeta (2 * criticalParameter t)) := by
  have harg : 2 * criticalParameter (-t) = conj (2 * criticalParameter t) := by
    apply Complex.ext <;> simp [criticalParameter, Complex.mul_re, Complex.mul_im] <;> ring
  rw [harg]
  apply completedZeta_conj_of_re_pos
  simp [criticalParameter, Complex.mul_re, Complex.mul_im]

theorem criticalScattering_neg (t : ℝ) :
    criticalScattering (-t) = conj (criticalScattering t) := by
  by_cases ht : t = 0
  · subst t
    simp
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  rw [criticalScattering_of_ne_zero (-t) hnt, criticalScattering_of_ne_zero t ht,
    complexScattering_critical_eq_conj_quotient (-t) hnt,
    complexScattering_critical_eq_conj_quotient t ht]
  simp only [critical_completed_denominator_neg, map_div₀, conj_conj]

theorem primeRatio_critical_neg (p : ℕ) (t : ℝ) :
    primeRatio p (criticalParameter (-t)) = conj (primeRatio p (criticalParameter t)) := by
  have harg : (p : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg p)]
    exact Real.pi_ne_zero.symm
  have hexp : -criticalParameter (-t) = conj (-criticalParameter t) := by
    apply Complex.ext <;> simp [criticalParameter] <;> ring
  unfold primeRatio
  rw [hexp]
  simpa only [map_natCast] using Complex.cpow_conj (p : ℂ) (-criticalParameter t) harg

theorem primeDiagonal_critical_neg (p : ℕ) (t : ℝ) :
    primeDiagonal p (criticalParameter (-t)) = conj (primeDiagonal p (criticalParameter t)) := by
  simp only [primeDiagonal, primeRatio_critical_neg, map_div₀, map_mul,
    map_sub, map_natCast, map_one, map_pow]

theorem primeOffDiagonal_critical_neg (p : ℕ) (t : ℝ) :
    primeOffDiagonal p (criticalParameter (-t)) = conj (primeOffDiagonal p (criticalParameter t)) := by
  simp only [primeOffDiagonal, primeRatio_critical_neg, map_div₀, map_mul,
    map_sub, map_natCast, map_one, map_pow]

/-- Actual critical coefficient reflection, not a functional-equation input. -/
theorem primeScatteringMatrix_neg (p : ℕ) (t : ℝ) :
    primeScatteringMatrix p (-t) = (primeScatteringMatrix p t).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primeScatteringMatrix, Matrix.conjTranspose_apply, primeCriticalDiagonal,
      primeCriticalOffDiagonal, criticalScattering_neg,
      primeDiagonal_critical_neg, primeOffDiagonal_critical_neg, map_mul]

/-- Critical functional equation for the identified physical prime matrix. -/
theorem primeScatteringMatrix_critical_functionalEquation {p : ℕ} (hp : p.Prime) (t : ℝ) :
    primeScatteringMatrix p t * primeScatteringMatrix p (-t) = 1 := by
  rw [primeScatteringMatrix_neg]
  exact primeScatteringMatrix_mul_conjTranspose hp t

end ImbalancedChen.Part3.PrimeScatteringAnalytic20261026b
