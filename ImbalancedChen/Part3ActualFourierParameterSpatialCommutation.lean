import ImbalancedChen.Part3ActualKQOrderMixedDerivative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual complex-parameter derivatives of the literal Fourier spatial jets
are computed by Leibniz, using the honest common K-order/q integral. Their
spatial derivatives satisfy the same frequency/q-moment recurrences. The
proved Cauchy majorants for the ACTUAL parameter derivatives then justify
both spatial series exchanges. Thus parameter/x and parameter/y commute
for every actual spatial-moment series, with both frequency signs intact.
No mixed-derivative, normal-convergence or interchange assumption occurs.
-/

namespace ImbalancedChen.Part3.ActualFourierParameterSpatialCommutation20261026b
noncomputable section
open Set Complex Filter Topology
open ActualSpatialJetParameterSeries20261026b ActualKQOrderMixedDerivative20261026b
open ComplexOrderKQCalculus ContinuedFourierSpatialMoments ContinuedFourierMomentSeriesCalculus
open Part3ActualRamanujanBesselNormalConvergence

/-- Explicit ACTUAL Leibniz derivative, retaining the finite divisor
coefficient and the true K-order derivative integral. -/
def spatialParameterTerm (j k n : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  (deriv (spectralCoefficient n) s * qMoment k (s - 1 / 2) (frequency (n + 1) * y) +
    spectralCoefficient n s * qOrderIntegral k (s - 1 / 2) (frequency (n + 1) * y)) *
      (Complex.I * (frequency (n + 1) : ℂ)) ^ j * (frequency (n + 1) : ℂ) ^ k * phase (n + 1) x

theorem spatialMomentTerm_hasDerivAt_parameter_explicit (j k n : ℕ) (s : ℂ)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => spatialMomentTerm j k n w y x)
      (spatialParameterTerm j k n s y x) s := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have hK := (qMoment_hasDerivAt_order_integral k (s - 1 / 2) (mul_pos hw hy)).comp s
    ((hasDerivAt_id s).sub_const (1 / 2 : ℂ))
  have hC := (spectralCoefficient_parameter_differentiable n s).hasDerivAt
  have h := (((hC.mul_const ((Complex.I * (frequency (n + 1) : ℂ)) ^ j)).mul_const
    ((frequency (n + 1) : ℂ) ^ k)).mul hK).mul_const (phase (n + 1) x)
  convert h using 1 <;> simp only [spatialMomentTerm, spatialParameterTerm, sub_zero, mul_one] <;> ring

theorem spatialParameterTerm_eq_deriv (j k n : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    spatialParameterTerm j k n s y x = deriv (fun w : ℂ => spatialMomentTerm j k n w y x) s :=
  (spatialMomentTerm_hasDerivAt_parameter_explicit j k n s y x hy).deriv.symm

theorem spatialParameterTerm_hasDerivAt_x (j k n : ℕ) (s : ℂ) (y x : ℝ) :
    HasDerivAt (fun t : ℝ => spatialParameterTerm j k n s y t)
      (spatialParameterTerm (j + 1) k n s y x) x := by
  have h := (phase_hasDerivAt (n + 1) x).const_mul
    ((deriv (spectralCoefficient n) s * qMoment k (s - 1 / 2) (frequency (n + 1) * y) +
      spectralCoefficient n s * qOrderIntegral k (s - 1 / 2) (frequency (n + 1) * y)) *
        (Complex.I * (frequency (n + 1) : ℂ)) ^ j * (frequency (n + 1) : ℂ) ^ k)
  convert h using 1 <;> simp only [spatialParameterTerm, pow_succ] <;> ring

/-- The vertical recurrence is the proved q/order mixed-integral
identity, rather than a formally interchanged derivative. -/
theorem spatialParameterTerm_hasDerivAt_y (j k n : ℕ) (s : ℂ)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => spatialParameterTerm j k n s t x)
      (spatialParameterTerm j (k + 1) n s y x) y := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have hA := (qMoment_hasDerivAt k (s - 1 / 2) (mul_pos hw hy)).comp y
    ((hasDerivAt_id y).const_mul (frequency (n + 1)))
  have hB := (qOrderIntegral_hasDerivAt_q k (s - 1 / 2) (mul_pos hw hy)).comp y
    ((hasDerivAt_id y).const_mul (frequency (n + 1)))
  have h := ((((hA.const_mul (deriv (spectralCoefficient n) s)).add
    (hB.const_mul (spectralCoefficient n s))).mul_const
      ((Complex.I * (frequency (n + 1) : ℂ)) ^ j)).mul_const
        ((frequency (n + 1) : ℂ) ^ k)).mul_const (phase (n + 1) x)
  convert h using 1 <;>
    simp only [spatialParameterTerm, pow_succ, smul_eq_mul, Complex.ofReal_mul] <;> ring

theorem spatialParameterTerm_norm_bound (j k M n : ℕ) {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖spatialParameterTerm j k n s y x‖ ≤ 2 * spatialMajorant j k (M + 1) a n := by
  rw [spatialParameterTerm_eq_deriv j k n s y x (ha.trans_le hy)]
  exact spatialMomentTerm_parameter_derivative_bound j k M n ha hs hy x

theorem spatialParameterTerm_norm_summable (j k : ℕ) (s : ℂ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖spatialParameterTerm j k n s y x‖) := by
  simp_rw [spatialParameterTerm_eq_deriv j k _ s y x hy]
  exact spatialParameterDerivative_norm_summable j k s hy x

theorem momentParameterSum_eq_tsum (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    momentParameterSum j k s y x = ∑' n : ℕ, spatialParameterTerm j k n s y x := by
  unfold momentParameterSum
  apply tsum_congr
  intro n
  exact (spatialParameterTerm_eq_deriv j k n s y x hy).symm

/-- Genuine horizontal derivative exchange in the ACTUAL parameter jet. -/
theorem momentParameterSum_hasDerivAt_x (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => momentParameterSum j k s y t)
      (momentParameterSum (j + 1) k s y x) x := by
  let M : ℕ := Nat.ceil |s.re|
  have h := hasDerivAt_tsum
    (u := fun n => 2 * spatialMajorant (j + 1) k (M + 1) y n)
    ((spatialMajorant_summable (j + 1) k (M + 1) hy).const_mul 2)
    (fun n t => spatialParameterTerm_hasDerivAt_x j k n s y t)
    (fun n t => spatialParameterTerm_norm_bound (j + 1) k M n hy (Nat.le_ceil _) le_rfl t)
    (spatialParameterTerm_norm_summable j k s hy x).of_norm x
  have he : (fun t : ℝ => ∑' n : ℕ, spatialParameterTerm j k n s y t) =
      (fun t : ℝ => momentParameterSum j k s y t) :=
    funext (fun t => (momentParameterSum_eq_tsum j k s y t hy).symm)
  rw [he, ← momentParameterSum_eq_tsum (j + 1) k s y x hy] at h
  exact h

/-- Genuine vertical derivative exchange in the ACTUAL parameter jet. -/
theorem momentParameterSum_hasDerivAt_y (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => momentParameterSum j k s t x)
      (momentParameterSum j (k + 1) s y x) y := by
  let M : ℕ := Nat.ceil |s.re|
  have ha : 0 < y / 2 := half_pos hy
  have hyI : y ∈ Ioo (y / 2) (3 * y / 2) := by constructor <;> linarith
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun n => 2 * spatialMajorant j (k + 1) (M + 1) (y / 2) n)
    (t := Ioo (y / 2) (3 * y / 2))
    ((spatialMajorant_summable j (k + 1) (M + 1) ha).const_mul 2)
    isOpen_Ioo isPreconnected_Ioo
    (fun n t ht => spatialParameterTerm_hasDerivAt_y j k n s t x (ha.trans ht.1))
    (fun n t ht => spatialParameterTerm_norm_bound j (k + 1) M n ha (Nat.le_ceil _) ht.1.le x)
    hyI (spatialParameterTerm_norm_summable j k s hy x).of_norm hyI
  have he : (fun t : ℝ => momentParameterSum j k s t x) =ᶠ[𝓝 y]
      (fun t : ℝ => ∑' n : ℕ, spatialParameterTerm j k n s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact momentParameterSum_eq_tsum j k s t x ht
  rw [← momentParameterSum_eq_tsum j (k + 1) s y x hy] at h
  exact h.congr_of_eventuallyEq he

/-- HONEST parameter/x commutation of every actual spatial q-jet series. -/
theorem momentSum_parameter_x_commute (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => momentSum j k w y t) s) x =
      deriv (fun w : ℂ => deriv (fun t : ℝ => momentSum j k w y t) x) s := by
  have hL : (fun t : ℝ => deriv (fun w : ℂ => momentSum j k w y t) s) =
      (fun t : ℝ => momentParameterSum j k s y t) :=
    funext (fun t => momentSum_parameter_deriv j k s y t hy)
  have hR : (fun w : ℂ => deriv (fun t : ℝ => momentSum j k w y t) x) =
      (fun w : ℂ => momentSum (j + 1) k w y x) :=
    funext (fun w => (momentSum_hasDerivAt_x j k w y x hy).deriv)
  rw [hL, hR, (momentParameterSum_hasDerivAt_x j k s y x hy).deriv,
    momentSum_parameter_deriv (j + 1) k s y x hy]

/-- HONEST parameter/y commutation, with positive-height locality
explicit. The left derivative uses an eventually equal actual series. -/
theorem momentSum_parameter_y_commute (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => momentSum j k w t x) s) y =
      deriv (fun w : ℂ => deriv (fun t : ℝ => momentSum j k w t x) y) s := by
  have he : (fun t : ℝ => deriv (fun w : ℂ => momentSum j k w t x) s) =ᶠ[𝓝 y]
      (fun t : ℝ => momentParameterSum j k s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact momentSum_parameter_deriv j k s t x ht
  have hL := ((momentParameterSum_hasDerivAt_y j k s y x hy).congr_of_eventuallyEq he).deriv
  have hR : (fun w : ℂ => deriv (fun t : ℝ => momentSum j k w t x) y) =
      (fun w : ℂ => momentSum j (k + 1) w y x) :=
    funext (fun w => (momentSum_hasDerivAt_y j k w y x hy).deriv)
  rw [hR, momentSum_parameter_deriv j (k + 1) s y x hy]
  exact hL

def signedParameterSum (j k : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  momentParameterSum j k s y x + (-1 : ℂ) ^ j * momentParameterSum j k s y (-x)

theorem signedMomentSum_parameter_deriv (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun w : ℂ => signedMomentSum j k w y x) s = signedParameterSum j k s y x :=
  (signedMomentSum_hasDerivAt_parameter j k s y x hy).deriv

theorem signedParameterSum_hasDerivAt_x (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => signedParameterSum j k s y t)
      (signedParameterSum (j + 1) k s y x) x := by
  have hp := momentParameterSum_hasDerivAt_x j k s y x hy
  have hn := ((momentParameterSum_hasDerivAt_x j k s y (-x) hy).comp x
    ((hasDerivAt_id x).neg)).const_mul ((-1 : ℂ) ^ j)
  convert hp.add hn using 1 <;> simp only [signedParameterSum, pow_succ, smul_eq_mul] <;> ring

theorem signedParameterSum_hasDerivAt_y (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => signedParameterSum j k s t x)
      (signedParameterSum j (k + 1) s y x) y :=
  (momentParameterSum_hasDerivAt_y j k s y x hy).add
    ((momentParameterSum_hasDerivAt_y j k s y (-x) hy).const_mul ((-1 : ℂ) ^ j))

theorem signedMomentSum_parameter_x_commute (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => signedMomentSum j k w y t) s) x =
      deriv (fun w : ℂ => deriv (fun t : ℝ => signedMomentSum j k w y t) x) s := by
  have hL : (fun t : ℝ => deriv (fun w : ℂ => signedMomentSum j k w y t) s) =
      (fun t : ℝ => signedParameterSum j k s y t) :=
    funext (fun t => signedMomentSum_parameter_deriv j k s y t hy)
  have hR : (fun w : ℂ => deriv (fun t : ℝ => signedMomentSum j k w y t) x) =
      (fun w : ℂ => signedMomentSum (j + 1) k w y x) :=
    funext (fun w => (signedMomentSum_hasDerivAt_x j k w y x hy).deriv)
  rw [hL, hR, (signedParameterSum_hasDerivAt_x j k s y x hy).deriv,
    signedMomentSum_parameter_deriv (j + 1) k s y x hy]

theorem signedMomentSum_parameter_y_commute (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => signedMomentSum j k w t x) s) y =
      deriv (fun w : ℂ => deriv (fun t : ℝ => signedMomentSum j k w t x) y) s := by
  have he : (fun t : ℝ => deriv (fun w : ℂ => signedMomentSum j k w t x) s) =ᶠ[𝓝 y]
      (fun t : ℝ => signedParameterSum j k s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact signedMomentSum_parameter_deriv j k s t x ht
  have hL := ((signedParameterSum_hasDerivAt_y j k s y x hy).congr_of_eventuallyEq he).deriv
  have hR : (fun w : ℂ => deriv (fun t : ℝ => signedMomentSum j k w t x) y) =
      (fun w : ℂ => signedMomentSum j (k + 1) w y x) :=
    funext (fun w => (signedMomentSum_hasDerivAt_y j k w y x hy).deriv)
  rw [hR, signedMomentSum_parameter_deriv j (k + 1) s y x hy]
  exact hL

end
end ImbalancedChen.Part3.ActualFourierParameterSpatialCommutation20261026b
