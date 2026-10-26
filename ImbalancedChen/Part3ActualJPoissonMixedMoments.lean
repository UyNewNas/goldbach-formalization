import ImbalancedChen.Part3ActualJLocalOrderHolomorphic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Genuine mixed q/order differentiation at the actual Poisson-integral
level. Native q moments insert (i*u)^k and native order differentiation
inserts log(1-u^2). All derivative bounds and endpoint integrability are
proved from the actual Poisson/log envelope. These primitives precede,
and do not assume, the still-required full-J prefactor mixed-jet identity.
No critical kernel or held Mellin convergence source is imported.
-/

namespace ImbalancedChen.Part3.ActualJPoissonMixedMoments20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualJLocalOrderHolomorphic20261026a

def poissonQIntegrand (k : ℕ) (nu : ℂ) (q u : ℝ) : ℂ :=
  (I * (u : ℂ)) ^ k * orderPoissonIntegrand nu q u

def poissonQLogIntegrand (k : ℕ) (nu : ℂ) (q u : ℝ) : ℂ :=
  (I * (u : ℂ)) ^ k * orderPoissonDerivIntegrand nu q u

def poissonQMoment (k : ℕ) (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, poissonQIntegrand k nu q u

def poissonQLogMoment (k : ℕ) (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, poissonQLogIntegrand k nu q u

private theorem unit_power_norm_le (k : ℕ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖(I * (u : ℂ)) ^ k‖ ≤ 1 := by
  rw [norm_pow]
  apply pow_le_one₀ (norm_nonneg _)
  simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] using
    (abs_lt.mpr hu).le

private theorem poisson_phase_norm_eq (nu : ℂ) (q u : ℝ) :
    ‖orderPoissonIntegrand nu q u‖ = ‖orderPoissonIntegrand nu 0 u‖ := by
  unfold orderPoissonIntegrand
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

private theorem qIntegrand_measurable (k : ℕ) (nu : ℂ) (q : ℝ) :
    Measurable (poissonQIntegrand k nu q) := by
  unfold poissonQIntegrand orderPoissonIntegrand
  fun_prop

private theorem qLogIntegrand_measurable (k : ℕ) (nu : ℂ) (q : ℝ) :
    Measurable (poissonQLogIntegrand k nu q) := by
  unfold poissonQLogIntegrand orderPoissonDerivIntegrand orderPoissonIntegrand
  fun_prop

private theorem qIntegrand_norm_le (k : ℕ) (nu : ℂ) (q : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖poissonQIntegrand k nu q u‖ ≤ ‖orderPoissonIntegrand nu 0 u‖ := by
  rw [poissonQIntegrand, norm_mul, poisson_phase_norm_eq]
  exact mul_le_of_le_one_left (norm_nonneg _) (unit_power_norm_le k hu)

private theorem qLogIntegrand_norm_le (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    (q : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖poissonQLogIntegrand k nu q u‖ ≤ orderDerivativeEnvelope u := by
  rw [poissonQLogIntegrand, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (unit_power_norm_le k hu)).trans
    (orderPoissonDerivIntegrand_norm_le hnu q hu)

theorem poissonQIntegrand_integrable (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    IntegrableOn (poissonQIntegrand k nu q) (Ioo (-1 : ℝ) 1) := by
  have hn : -(1 / 2 : ℝ) < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  apply (orderPoisson_integrable hn 0).norm.mono' (qIntegrand_measurable k nu q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact qIntegrand_norm_le k nu q hu

theorem poissonQLogIntegrand_integrable (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    IntegrableOn (poissonQLogIntegrand k nu q) (Ioo (-1 : ℝ) 1) := by
  apply orderDerivativeEnvelope_integrable.mono' (qLogIntegrand_measurable k nu q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact qLogIntegrand_norm_le k hnu q hu

private theorem qIntegrand_q_hasDerivAt (k : ℕ) (nu : ℂ) (q u : ℝ) :
    HasDerivAt (fun x : ℝ => poissonQIntegrand k nu x u) (poissonQIntegrand (k + 1) nu q u) q := by
  have hp : HasDerivAt (fun x : ℝ => I * (x : ℂ) * (u : ℂ)) (I * (u : ℂ)) q := by
    convert ((hasDerivAt_id q).ofReal_comp.const_mul I).mul_const (u : ℂ) using 1 <;> ring
  have h := hp.cexp.mul_const
    (Complex.exp ((Real.log (1 - u ^ 2) : ℂ) * (nu - 1 / 2)))
  convert h.const_mul ((I * (u : ℂ)) ^ k) using 1 <;>
    simp only [poissonQIntegrand, orderPoissonIntegrand, pow_succ] <;> ring

private theorem qLogIntegrand_q_hasDerivAt (k : ℕ) (nu : ℂ) (q u : ℝ) :
    HasDerivAt (fun x : ℝ => poissonQLogIntegrand k nu x u)
      (poissonQLogIntegrand (k + 1) nu q u) q := by
  have h := (qIntegrand_q_hasDerivAt k nu q u).const_mul (Real.log (1 - u ^ 2) : ℂ)
  convert h using 1 <;>
    simp only [poissonQLogIntegrand, poissonQIntegrand, orderPoissonDerivIntegrand,
      mul_assoc, mul_comm, mul_left_comm] <;> ring

theorem poissonQMoment_q_hasDerivAt (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    HasDerivAt (poissonQMoment k nu) (poissonQMoment (k + 1) nu q) q := by
  have hn : -(1 / 2 : ℝ) < nu.re := by change -(1 / 4 : ℝ) < nu.re at hnu; linarith
  have hb : ∀ᵐ u ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ x ∈ (univ : Set ℝ),
      ‖poissonQIntegrand (k + 1) nu x u‖ ≤ ‖orderPoissonIntegrand nu 0 u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact fun x _ => qIntegrand_norm_le (k + 1) nu x hu
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun x u => poissonQIntegrand k nu x u)
    (F' := fun x u => poissonQIntegrand (k + 1) nu x u)
    (bound := fun u => ‖orderPoissonIntegrand nu 0 u‖)
    (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 q)
    (Eventually.of_forall (fun x => (qIntegrand_measurable k nu x).aestronglyMeasurable))
    (poissonQIntegrand_integrable k hnu q)
    (qIntegrand_measurable (k + 1) nu q).aestronglyMeasurable hb
    (orderPoisson_integrable hn 0).norm
    (Eventually.of_forall (fun u x _ => qIntegrand_q_hasDerivAt k nu x u))).2

theorem poissonQLogMoment_q_hasDerivAt (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    HasDerivAt (poissonQLogMoment k nu) (poissonQLogMoment (k + 1) nu q) q := by
  have hb : ∀ᵐ u ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ x ∈ (univ : Set ℝ),
      ‖poissonQLogIntegrand (k + 1) nu x u‖ ≤ orderDerivativeEnvelope u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact fun x _ => qLogIntegrand_norm_le (k + 1) hnu x hu
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun x u => poissonQLogIntegrand k nu x u)
    (F' := fun x u => poissonQLogIntegrand (k + 1) nu x u)
    (bound := orderDerivativeEnvelope) (Filter.univ_mem : (univ : Set ℝ) ∈ 𝓝 q)
    (Eventually.of_forall (fun x => (qLogIntegrand_measurable k nu x).aestronglyMeasurable))
    (poissonQLogIntegrand_integrable k hnu q)
    (qLogIntegrand_measurable (k + 1) nu q).aestronglyMeasurable hb orderDerivativeEnvelope_integrable
    (Eventually.of_forall (fun u x _ => qLogIntegrand_q_hasDerivAt k nu x u))).2

theorem poissonQMoment_order_hasDerivAt (k : ℕ) {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    HasDerivAt (fun z : ℂ => poissonQMoment k z q) (poissonQLogMoment k nu q) nu := by
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hb : ∀ᵐ u ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ z ∈ orderHalfPlane,
      ‖poissonQLogIntegrand k z q u‖ ≤ orderDerivativeEnvelope u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact fun z hz => qLogIntegrand_norm_le k hz q hu
  have hd : ∀ᵐ u ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ z ∈ orderHalfPlane,
      HasDerivAt (fun w : ℂ => poissonQIntegrand k w q u) (poissonQLogIntegrand k z q u) z :=
    Eventually.of_forall (fun u z _ =>
      (orderPoissonIntegrand_hasDerivAt z q u).const_mul ((I * (u : ℂ)) ^ k))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun z u => poissonQIntegrand k z q u)
    (F' := fun z u => poissonQLogIntegrand k z q u) (bound := orderDerivativeEnvelope)
    (hopen.mem_nhds hnu)
    (Eventually.of_forall (fun z => (qIntegrand_measurable k z q).aestronglyMeasurable))
    (poissonQIntegrand_integrable k hnu q)
    (qLogIntegrand_measurable k nu q).aestronglyMeasurable hb orderDerivativeEnvelope_integrable hd).2

/-- Actual native mixed derivatives commute for the Poisson moments.
This supplies the integral part of the full-J mixed-jet calculation. -/
theorem poissonQMoment_native_mixed_deriv (k : ℕ) {nu : ℂ}
    (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    deriv (fun x : ℝ => deriv (fun z : ℂ => poissonQMoment k z x) nu) q =
      deriv (fun z : ℂ => deriv (poissonQMoment k z) q) nu := by
  have heL : (fun x : ℝ => deriv (fun z : ℂ => poissonQMoment k z x) nu) =
      poissonQLogMoment k nu := by
    funext x
    exact (poissonQMoment_order_hasDerivAt k hnu x).deriv
  have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
  have heR : (fun z : ℂ => deriv (poissonQMoment k z) q) =ᶠ[𝓝 nu]
      (fun z : ℂ => poissonQMoment (k + 1) z q) := by
    filter_upwards [hopen.mem_nhds hnu] with z hz
    exact (poissonQMoment_q_hasDerivAt k hz q).deriv
  rw [heL, (poissonQLogMoment_q_hasDerivAt k hnu q).deriv]
  exact ((poissonQMoment_order_hasDerivAt (k + 1) hnu q).congr_of_eventuallyEq heR).deriv.symm

end
end ImbalancedChen.Part3.ActualJPoissonMixedMoments20261026b
