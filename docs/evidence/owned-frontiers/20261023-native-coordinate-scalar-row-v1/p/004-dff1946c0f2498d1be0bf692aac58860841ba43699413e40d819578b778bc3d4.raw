import ImbalancedChen.Part3ActualNormalizedSmoothF
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
SOURCEONLY, no compilation. Standalone geometry/scalar companion to the actual
433-line finite Poisson draft 86340f2e. The actual parent normalizedF is 61023c93.
No spectral or Fourier-decay hypothesis. No continuous replacement of the
DISCRETE c sum is made. Only the actual psi and actual Schwartz Fourier transform
occur. Every auxiliary cutoff is removed using its actual [1,2] plateau theorem.
-/
namespace ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
noncomputable section
open Set CommonSmoothCutoff ActualNormalizedSmoothF
open scoped SchwartzMap FourierTransform

def point (t v w z : ℝ) : E4 := WithLp.toLp 2 ![t,v,w,z]

def chartT (u v w z : ℝ) : ℝ := Real.sqrt (v*w/z) / u

def chart (u v w z : ℝ) : E4 := point (chartT u v w z) v w z

def poissonScale (D c : ℝ) : ℝ := D/c

def spectralArgument (A p n z c : ℝ) : ℝ :=
  4*Real.pi*Real.sqrt (A*p*n)/(c*Real.sqrt z)

def spectralScale (A V U Z C : ℝ) : ℝ :=
  4*Real.pi*Real.sqrt (A*V*U)/(C*Real.sqrt Z)

theorem chartT_pos {u v w z : ℝ} (hu : 0<u) (hv : 0<v)
    (hw : 0<w) (hz : 0<z) : 0 < chartT u v w z := by
  unfold chartT
  positivity

theorem sqrt_cross {v w z : ℝ} (hv : 0<v) (hw : 0<w) (hz : 0<z) :
    Real.sqrt (v*w/z) * Real.sqrt (v*z/w) = v := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ v*w/z)]
  have he : (v*w/z)*(v*z/w) = v^2 := by
    field_simp [hw.ne',hz.ne']
  rw [he, Real.sqrt_sq hv.le]

theorem chart_cutoff_argument {u v w z : ℝ} (hu : 0<u) (hv : 0<v)
    (hw : 0<w) (hz : 0<z) :
    Real.sqrt (v*w/z) / chartT u v w z = u := by
  have hs : Real.sqrt (v*w/z) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold chartT
  field_simp [hu.ne',hs]

theorem chart_fourier_argument {u v w z : ℝ} (hu : 0<u) (hv : 0<v)
    (hw : 0<w) (hz : 0<z) :
    chartT u v w z * Real.sqrt (v*z/w) = v/u := by
  have _ := hu
  unfold chartT
  rw [div_mul_eq_mul_div, sqrt_cross hv hw hz]

/-- Exact actual F, including its genuine zero-extension and its three auxiliary
cutoffs. There is no parity or conjugation assertion about the Fourier factor. -/
theorem normalizedF_chart {u v w z : ℝ} (hu : 0<u)
    (hv : v ∈ Icc (1:ℝ) 2) (hw : w ∈ Icc (1:ℝ) 2)
    (hz : z ∈ Icc (1:ℝ) 2) (rho sigma : ℝ) :
    normalizedF rho sigma (chart u v w z) =
      ((Real.sqrt z * dyadicCutoff u : ℝ) : ℂ) *
        ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ,ℂ))) (sigma*rho*(v/u)) := by
  have hvp : 0<v := lt_of_lt_of_le zero_lt_one hv.1
  have hwp : 0<w := lt_of_lt_of_le zero_lt_one hw.1
  have hzp : 0<z := lt_of_lt_of_le zero_lt_one hz.1
  have hp : positive (chart u v w z) :=
    ⟨chartT_pos hu hvp hwp hzp,hvp,hwp,hzp⟩
  rw [normalizedF, if_pos hp]
  change
    ((dyadicCutoff v*dyadicCutoff w*dyadicCutoff z*Real.sqrt z*
      dyadicCutoff (Real.sqrt (v*w/z)/chartT u v w z) : ℝ) : ℂ)*
      ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ,ℂ)))
        (sigma*rho*chartT u v w z*Real.sqrt (v*z/w)) = _
  rw [dyadicCutoff_eq_one hv,dyadicCutoff_eq_one hw,dyadicCutoff_eq_one hz,
    chart_cutoff_argument hu hvp hwp hzp]
  have hf : sigma*rho*chartT u v w z*Real.sqrt (v*z/w) = sigma*rho*(v/u) := by
    rw [mul_assoc, chart_fourier_argument hu hvp hwp hzp]
  rw [hf]
  simp only [one_mul]

/-- This is a derived identity for the literal physical scales, not a kernel
matching premise. It holds for every real sigma; rapid estimates later need ±1. -/
theorem normalizedF_physical {D C V U Z c p n z : ℝ}
    (hD : 0<D) (hC : 0<C) (hV : 0<V) (hU : 0<U) (hZ : 0<Z)
    (hc : 0<c) (hp : p/V ∈ Icc (1:ℝ) 2)
    (hn : n/U ∈ Icc (1:ℝ) 2) (hz : z/Z ∈ Icc (1:ℝ) 2) (sigma : ℝ) :
    normalizedF (V*D/C) sigma (chart (c/C) (p/V) (n/U) (z/Z)) =
      ((Real.sqrt (z/Z)*dyadicCutoff (c/C) : ℝ) : ℂ)*
        ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ,ℂ))) (sigma*(D/c)*p) := by
  have _ := hU
  have _ := hZ
  rw [normalizedF_chart (div_pos hc hC) hp hn hz]
  have he : sigma*(V*D/C)*((p/V)/(c/C)) = sigma*(D/c)*p := by
    field_simp [hV.ne',hC.ne',hc.ne']
  rw [he]

/-- Exact extraction: D/C from Poisson and C sqrt Z from the canonical
1/(c sqrt z) normalization. No discrete-c Jacobian is introduced. -/
theorem poisson_scalar_match {D C V U Z c p n z : ℝ}
    (hD : 0<D) (hC : 0<C) (hV : 0<V) (hU : 0<U) (hZ : 0<Z)
    (hc : 0<c) (hp : p/V ∈ Icc (1:ℝ) 2)
    (hn : n/U ∈ Icc (1:ℝ) 2) (hz : z/Z ∈ Icc (1:ℝ) 2) (sigma : ℝ) :
    ((dyadicCutoff (c/C) * poissonScale D c : ℝ) : ℂ)*
        ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ,ℂ))) (sigma*(D/c)*p) =
      ((D*Real.sqrt Z/(c*Real.sqrt z) : ℝ) : ℂ)*
        normalizedF (V*D/C) sigma (chart (c/C) (p/V) (n/U) (z/Z)) := by
  have hzp : 0<z := by
    have hh : 0 < z/Z := lt_of_lt_of_le zero_lt_one hz.1
    exact (div_pos_iff.mp hh).elim (fun h => h.1) (fun h => False.elim (not_lt_of_gt hZ h.2))
  have hsz : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hzp).ne'
  have hsZ : Real.sqrt Z ≠ 0 := (Real.sqrt_pos.mpr hZ).ne'
  rw [normalizedF_physical hD hC hV hU hZ hc hp hn hz]
  rw [Real.sqrt_div hzp.le]
  have hr : (D*Real.sqrt Z/(c*Real.sqrt z)) *
      (Real.sqrt z/Real.sqrt Z*dyadicCutoff (c/C)) =
        dyadicCutoff (c/C)*poissonScale D c := by
    unfold poissonScale
    field_simp [hc.ne',hsz,hsZ]
  rw [← mul_assoc, ← Complex.ofReal_mul, hr]

/-- The same exact identity under arbitrary literal complex coefficient and
complete sum. In particular no conjugation or real-part operation is moved. -/
theorem poisson_scalar_match_with_coeff {D C V U Z c p n z : ℝ}
    (hD : 0<D) (hC : 0<C) (hV : 0<V) (hU : 0<U) (hZ : 0<Z)
    (hc : 0<c) (hp : p/V ∈ Icc (1:ℝ) 2)
    (hn : n/U ∈ Icc (1:ℝ) 2) (hz : z/Z ∈ Icc (1:ℝ) 2)
    (sigma : ℝ) (beta K : ℂ) :
    beta * (((dyadicCutoff (c/C)*poissonScale D c : ℝ) : ℂ)*
      ((𝓕 dyadicCutoffSchwartz : 𝓢(ℝ,ℂ))) (sigma*(D/c)*p)) * K =
    beta * (((D*Real.sqrt Z/(c*Real.sqrt z) : ℝ) : ℂ)*
      normalizedF (V*D/C) sigma (chart (c/C) (p/V) (n/U) (z/Z))) * K := by
  rw [poisson_scalar_match hD hC hV hU hZ hc hp hn hz]

/-- The positive residue magnitude cancels from the normalized coordinates.
No bound on A is needed for this exact identity. -/
theorem spectral_argument_normalized {A V U Z C c p n z : ℝ}
    (hA : 0<A) (hV : 0<V) (hU : 0<U) (hZ : 0<Z) (hC : 0<C)
    (hc : 0<c) (hp : 0<p) (hn : 0<n) (hz : 0<z) :
    spectralArgument A p n z c / spectralScale A V U Z C =
      chartT (c/C) (p/V) (n/U) (z/Z) := by
  have hbase : 0 < A*V*U := by positivity
  have hnum : 0 ≤ A*p*n := by positivity
  have hsbase : Real.sqrt (A*V*U) ≠ 0 := (Real.sqrt_pos.mpr hbase).ne'
  have hsz : Real.sqrt z ≠ 0 := (Real.sqrt_pos.mpr hz).ne'
  have hsZ : Real.sqrt Z ≠ 0 := (Real.sqrt_pos.mpr hZ).ne'
  have hr : Real.sqrt (A*p*n) / Real.sqrt (A*V*U) *
      (Real.sqrt Z/Real.sqrt z) = Real.sqrt ((p/V)*(n/U)/(z/Z)) := by
    rw [← Real.sqrt_div hnum, ← Real.sqrt_div hZ.le,
      ← Real.sqrt_mul (by positivity : 0 ≤ (A*p*n)/(A*V*U))]
    congr 1
    field_simp [hA.ne',hV.ne',hU.ne',hZ.ne',hz.ne']
  calc
    _ = (C/c) * (Real.sqrt (A*p*n) / Real.sqrt (A*V*U) *
        (Real.sqrt Z/Real.sqrt z)) := by
      unfold spectralArgument spectralScale
      field_simp [hC.ne',hc.ne',hsbase,hsz,hsZ,Real.pi_ne_zero]
    _ = (C/c) * Real.sqrt ((p/V)*(n/U)/(z/Z)) := by rw [hr]
    _ = _ := by
      unfold chartT
      field_simp [hc.ne',hC.ne']

/-- The full 4-coordinate object equals the physical q/Y0 chart. -/
theorem chart_eq_spectral_point {A V U Z C c p n z : ℝ}
    (hA : 0<A) (hV : 0<V) (hU : 0<U) (hZ : 0<Z) (hC : 0<C)
    (hc : 0<c) (hp : 0<p) (hn : 0<n) (hz : 0<z) :
    chart (c/C) (p/V) (n/U) (z/Z) =
      point (spectralArgument A p n z c / spectralScale A V U Z C)
        (p/V) (n/U) (z/Z) := by
  rw [spectral_argument_normalized hA hV hU hZ hC hc hp hn hz]
  rfl

/-- Exact product of the two advertised outside factors. -/
theorem outside_factors {D C Z : ℝ} (hC : C ≠ 0) :
    (D/C)*(C*Real.sqrt Z) = D*Real.sqrt Z := by
  rw [← mul_assoc, div_mul_cancel₀ _ hC]

/-- The original signed Fourier argument is preserved without a Fourier
parity hypothesis or any assumption that the transform is real-valued. -/
theorem signed_fourier_argument (sigma D c p : ℝ) :
    sigma*(D/c)*p = (D/c)*(sigma*p) := by ring

/-- Quadratic scale, with the full 16*pi^2 retained. -/
theorem spectralScale_sq {A V U Z C : ℝ} (hA : 0<A) (hV : 0<V)
    (hU : 0<U) (hZ : 0<Z) (hC : 0<C) :
    (spectralScale A V U Z C)^2 = 16*Real.pi^2*A*V*U/(C^2*Z) := by
  have _ := hC
  simp only [spectralScale, div_pow, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ A*V*U), Real.sq_sqrt hZ.le]
  ring

/-- Actual inverse variable and its derivative. Used only in continuous
transforms: it does not change a discrete sum over natural moduli. -/
theorem inverse_variable_derivative (K c : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun x : ℝ => K/x) (-K/c^2) c := by
  simpa only [zero_mul, mul_one, zero_sub] using
    (hasDerivAt_const c K).fun_div (hasDerivAt_id' c) hc

theorem inverse_variable_abs_jacobian {K q : ℝ} (hK : 0<K) (hq : 0<q) :
    |(-K/q^2)| = (K/q)/q := by
  rw [neg_div, abs_neg, abs_of_pos (div_pos hK (sq_pos_of_pos hq))]
  ring

theorem physical_normalized_jacobian {Y0 t : ℝ} (hY0 : 0<Y0) (ht : 0<t) :
    Y0/(Y0*t) = 1/t := by
  field_simp [hY0.ne',ht.ne']

/-- The actual normalized support, without enlarging a rough m carrier. -/
theorem actual_t_support (rho sigma t v w z : ℝ)
    (hf : normalizedF rho sigma (point t v w z) ≠ 0) :
    t ∈ Icc (Real.sqrt 10/25) (5*Real.sqrt 2) := by
  have hb := support_subset_fixedBox rho sigma hf
  have h0 := hb (0 : Fin 4)
  change t ∈ Icc (boxLo (0 : Fin 4)) (boxHi (0 : Fin 4)) at h0
  simpa only [boxLo, boxHi, if_true] using h0

theorem spectralArgument_sq {A p n z c : ℝ} (hA : 0<A) (hp : 0<p)
    (hn : 0<n) (hz : 0<z) (hc : 0<c) :
    (spectralArgument A p n z c)^2 = 16*Real.pi^2*A*p*n/(c^2*z) := by
  exact spectralScale_sq hA hp hn hz hc

/-- Applied derivative of the actual physical q(c), with its sign. -/
theorem spectralArgument_derivative (A p n z c : ℝ) (hc : c ≠ 0) :
    HasDerivAt (spectralArgument A p n z)
      (-(4*Real.pi*Real.sqrt (A*p*n)/Real.sqrt z)/c^2) c := by
  have hf : spectralArgument A p n z =
      (fun x : ℝ => (4*Real.pi*Real.sqrt (A*p*n)/Real.sqrt z)/x) := by
    funext x
    unfold spectralArgument
    ring
  rw [hf]
  exact inverse_variable_derivative _ _ hc

/-- Signed cusp conversion plus the coprime ABL oldform phase. This is
only their exact scalar cancellation, not an assumed packet spectral theorem. -/
theorem signed_cusp_phase_cancel (eta A nu n z : ℝ) :
    (-eta*A*(nu*n)/z) + (eta*n*(A*nu-1)/z) = -eta*n/z := by
  ring

/-- Exact quadratic prefactor algebra; no spectral inequality is assumed. -/
theorem quadratic_prefactor {A V U Z C : ℝ} (hA : 0<A) (hV : 0<V)
    (hU : 0<U) (hZ : 0<Z) (hC : 0<C) (D : ℝ) :
    (D/C)^2 * (V*C^4*Z/(A*V*U+C^2*Z)) =
      D^2*V*Z/(Z+A*V*U/C^2) := by
  have hd : A*V*U+C^2*Z ≠ 0 := (show 0 < A*V*U+C^2*Z by positivity).ne'
  have he : Z+A*V*U/C^2 ≠ 0 := (show 0 < Z+A*V*U/C^2 by positivity).ne'
  field_simp [hC.ne',hd,he]; ring

/-- No old slow-phase charge occurs in this local amplitude scaling. -/
theorem rho_pos {V D C : ℝ} (hV : 0<V) (hD : 0<D) (hC : 0<C) :
    0 < V*D/C := div_pos (mul_pos hV hD) hC

end
end ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
