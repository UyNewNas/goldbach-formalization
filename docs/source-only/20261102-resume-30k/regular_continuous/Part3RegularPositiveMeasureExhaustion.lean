import ImbalancedChen.Part3RegularCumulativeShellPayment
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing positive-measure version of J's regular height payment.
Local L2 membership is explicit: a totalized, nonintegrable Bochner
integral cannot satisfy the cumulative premises vacuously. Global L1,
the exhaustion limit and the absolute regular integral are conclusions.
There is no assumption of Eq24, of a bilinear spectral estimate, or of
convergence of the full spectrum. The next module uses the actual finite
Gamma0 cusp-orbit carrier and dt/cosh(pi*t), with the 1/(4*pi) outside.
-/

namespace ImbalancedChen.Part3.RegularPositiveMeasureExhaustion20261102
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ComplexConjugate Topology
open RegularCumulativeShellPayment20261102

variable {α : Type*} [MeasurableSpace α]

def spectralCut (t : α → ℝ) (T : ℝ) : Set α := {x | |t x| ≤ T}

def spectralShell (t : α → ℝ) (K : ℝ) (j : ℕ) : Set α :=
  {x | (4 : ℝ)^j*K < |t x| ∧ |t x| ≤ (4 : ℝ)^(j+1)*K}

theorem measurableSet_spectralCut {t : α → ℝ} (ht : Measurable t) (T : ℝ) :
    MeasurableSet (spectralCut t T) := measurableSet_le ht.abs measurable_const

theorem measurableSet_spectralShell {t : α → ℝ} (ht : Measurable t) (K : ℝ) (j : ℕ) :
    MeasurableSet (spectralShell t K j) :=
  (measurableSet_lt measurable_const ht.abs).inter (measurableSet_spectralCut ht _)

theorem spectralShell_subset (t : α → ℝ) (K : ℝ) (j : ℕ) :
    spectralShell t K j ⊆ spectralCut t ((4 : ℝ)^(j+1)*K) := fun _ hx => hx.2

theorem spectralCut_mono (t : α → ℝ) : Monotone (spectralCut t) :=
  fun _ _ h _ hx => hx.trans h

theorem spectralCut_step (t : α → ℝ) {K : ℝ} (hK : 0 ≤ K) (j : ℕ) :
    spectralCut t ((4 : ℝ)^(j+1)*K) =
      spectralCut t ((4 : ℝ)^j*K) ∪ spectralShell t K j := by
  have hle : (4 : ℝ)^j*K ≤ (4 : ℝ)^(j+1)*K := by
    rw [pow_succ]
    have hp : 0 ≤ (4 : ℝ)^j*K := by positivity
    nlinarith
  ext x
  change |t x| ≤ (4 : ℝ)^(j+1)*K ↔
    |t x| ≤ (4 : ℝ)^j*K ∨ ((4 : ℝ)^j*K < |t x| ∧ |t x| ≤ (4 : ℝ)^(j+1)*K)
  constructor
  · intro hx
    by_cases hlo : |t x| ≤ (4 : ℝ)^j*K
    · exact Or.inl hlo
    · exact Or.inr ⟨lt_of_not_ge hlo,hx⟩
  · rintro (hx | hx)
    · exact hx.trans hle
    · exact hx.2

theorem spectralCut_disjoint_shell (t : α → ℝ) (K : ℝ) (j : ℕ) :
    Disjoint (spectralCut t ((4 : ℝ)^j*K)) (spectralShell t K j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_lt_of_ge hx) hy.1

theorem spectralCuts_monotone (t : α → ℝ) {K : ℝ} (hK : 0 ≤ K) :
    Monotone (fun j : ℕ => spectralCut t ((4 : ℝ)^j*K)) := by
  apply monotone_nat_of_le_succ
  intro j x hx
  rw [spectralCut_step t hK j]
  exact Or.inl hx

/-- Every finite real height is eventually included; no spectral
exhaustion or bounded-height premise is imported here. -/
theorem spectralCuts_iUnion (t : α → ℝ) {K : ℝ} (hK : 1 ≤ K) :
    (⋃ j : ℕ, spectralCut t ((4 : ℝ)^j*K)) = Set.univ := by
  have hgrowth (j : ℕ) : (j : ℝ)+1 ≤ (4 : ℝ)^j*K := by
    induction j with
    | zero => simpa using hK
    | succ j ih =>
      rw [pow_succ]
      push_cast
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
      nlinarith
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨j,hj⟩ := exists_nat_gt |t x|
  exact Set.mem_iUnion.mpr ⟨j,le_trans hj.le (by linarith [hgrowth j])⟩

/-- Ordinary integral Cauchy from two L2 norms. In particular, neither
functional itself is asserted globally L2 on the unbounded spectrum. -/
theorem integral_pair_budget (μ : Measure α) (A B : α → ℂ)
    {MA MB : ℝ} (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hA2 : MemLp A 2 μ) (hB2 : MemLp B 2 μ)
    (hA : ∫ x, ‖A x‖^2 ∂μ ≤ MA) (hB : ∫ x, ‖B x‖^2 ∂μ ≤ MB) :
    ∫ x, ‖A x‖*‖B x‖ ∂μ ≤ Real.sqrt (MA*MB) := by
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa only [ENNReal.ofReal_ofNat] using hA2)
    (by simpa only [ENNReal.ofReal_ofNat] using hB2)
  have hcs : (∫ x, ‖A x‖*‖B x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖A x‖^2 ∂μ)*Real.sqrt (∫ x, ‖B x‖^2 ∂μ) := by
    simpa only [Real.rpow_ofNat,← Real.sqrt_eq_rpow] using hh
  calc
    _ ≤ Real.sqrt (∫ x, ‖A x‖^2 ∂μ)*Real.sqrt (∫ x, ‖B x‖^2 ∂μ) := hcs
    _ ≤ Real.sqrt MA*Real.sqrt MB :=
      mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := (Real.sqrt_mul hMA MB).symm

/-- Bounded transform times the two local L2 functionals is L1.
The absolute integral estimate is derived, not supplied as a premise. -/
theorem integral_absolute_transform_budget (μ : Measure α) (H A B : α → ℂ)
    {d MA MB : ℝ} (hd : 0 ≤ d) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hF : AEStronglyMeasurable (fun x => H x*A x*conj (B x)) μ)
    (hA2 : MemLp A 2 μ) (hB2 : MemLp B 2 μ)
    (hH : ∀ᵐ x ∂μ, ‖H x‖ ≤ d)
    (hA : ∫ x, ‖A x‖^2 ∂μ ≤ MA) (hB : ∫ x, ‖B x‖^2 ∂μ ≤ MB) :
    Integrable (fun x => H x*A x*conj (B x)) μ ∧
      (∫ x, ‖H x*A x*conj (B x)‖ ∂μ) ≤ d*Real.sqrt (MA*MB) := by
  have hab : Integrable (fun x => ‖A x‖*‖B x‖) μ := by
    simpa only [Pi.mul_apply] using hA2.norm.integrable_mul hB2.norm
  have hmajor := hab.const_mul d
  have hpoint : ∀ᵐ x ∂μ, ‖H x*A x*conj (B x)‖ ≤ d*(‖A x‖*‖B x‖) := by
    filter_upwards [hH] with x hx
    calc
      _ = ‖H x‖*(‖A x‖*‖B x‖) := by rw [norm_mul,norm_mul,Complex.norm_conj]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (by positivity)
  have hint := hmajor.mono' hF hpoint
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ x, d*(‖A x‖*‖B x‖) ∂μ := integral_mono_ae hint.norm hmajor hpoint
    _ = d*(∫ x, ‖A x‖*‖B x‖ ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_pair_budget μ A B hMA hMB hA2 hB2 hA hB) hd

private theorem scalar_pair_scale {K p u v A2 B2 : ℝ} (hp : 1 ≤ p)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) :
    Real.sqrt ((((4*p*K)^2+u)*A2)*(((4*p*K)^2+v)*B2)) ≤
      (16*p^2)*pairBudget K u v A2 B2 := by
  have hp2 : 1 ≤ p^2 := by nlinarith
  have hs (w : ℝ) (hw : 0 ≤ w) : (4*p*K)^2+w ≤ (16*p^2)*(K^2+w) := by
    have hh : 0 ≤ (16*p^2-1)*w := mul_nonneg (by nlinarith) hw
    nlinarith only [hh]
  have ha := mul_le_mul_of_nonneg_right (hs u hu) hA2
  have hb := mul_le_mul_of_nonneg_right (hs v hv) hB2
  have hp' := mul_le_mul ha hb (show 0 ≤ ((4*p*K)^2+v)*B2 by positivity)
    (show 0 ≤ ((16*p^2)*(K^2+u))*A2 by positivity)
  have hl0 := Real.sqrt_nonneg ((((4*p*K)^2+u)*A2)*(((4*p*K)^2+v)*B2))
  have hls := Real.sq_sqrt (show 0 ≤ (((4*p*K)^2+u)*A2)*(((4*p*K)^2+v)*B2) by positivity)
  have hr0 : 0 ≤ (16*p^2)*pairBudget K u v A2 B2 := by positivity
  have hrs := pairBudget_sq (K := K) hu hv hA2 hB2
  have heq : (((16*p^2)*(K^2+u))*A2)*(((16*p^2)*(K^2+v))*B2) =
      ((16*p^2)*pairBudget K u v A2 B2)^2 := by rw [mul_pow,hrs]; ring
  rw [heq] at hp'
  nlinarith

private theorem sqrt_four_height {K : ℝ} (hK : 0 < K) (j : ℕ) :
    Real.sqrt ((4 : ℝ)^j*K) = (2 : ℝ)^j*Real.sqrt K := by
  have hp : (4 : ℝ)^j = ((2 : ℝ)^j)^2 := by
    calc
      (4 : ℝ)^j = ((2 : ℝ)^2)^j := by norm_num
      _ = ((2 : ℝ)^j)^2 := by rw [← pow_mul,← pow_mul]; congr 1; omega
  have hs := Real.sq_sqrt (show 0 ≤ (4 : ℝ)^j*K by positivity)
  have hKs := Real.sq_sqrt hK.le
  have hl0 := Real.sqrt_nonneg ((4 : ℝ)^j*K)
  have hr0 : 0 ≤ (2 : ℝ)^j*Real.sqrt K := by positivity
  have heq : ((2 : ℝ)^j*Real.sqrt K)^2 = (4 : ℝ)^j*K := by rw [mul_pow,hKs,← hp]
  nlinarith

/-- One genuine measurable shell, retaining all continuous fibres at
that height. Its local integrability is proved along with its payment. -/
theorem continuous_shell_payment (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ)
    (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x*A x*conj (B x)) μ)
    {K C Y u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖A x‖^2 ∂μ) ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖B x‖^2 ∂μ) ≤ (T^2+v)*B2)
    (hdecay : ∀ x, K ≤ |t x| → ‖H x‖ ≤ C*(1/(|t x|^2*Real.sqrt |t x|)+Y/|t x|^3))
    (j : ℕ) :
    IntegrableOn (fun x => H x*A x*conj (B x)) (spectralShell t K j) μ ∧
      (∫ x in spectralShell t K j, ‖H x*A x*conj (B x)‖ ∂μ) ≤
        16*C*pairBudget K u v A2 B2 *
          (((1 : ℝ)/2)^j/(K^2*Real.sqrt K)+Y*((1 : ℝ)/4)^j/K^3) := by
  classical
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hp : 1 ≤ (4 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hupper : 1 ≤ (4 : ℝ)^(j+1)*K := by
    have hp' : 1 ≤ (4 : ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hK (show 0 ≤ (4 : ℝ)^(j+1) by positivity)
    exact hp'.trans (by simpa only [mul_one] using hh)
  have hsub := Measure.restrict_mono (spectralShell_subset t K j) (le_refl μ)
  have ha := (hMA _ hupper).mono_measure hsub
  have hb := (hMB _ hupper).mono_measure hsub
  have hEA : (∫ x in spectralShell t K j, ‖A x‖^2 ∂μ) ≤ ((4*(4 : ℝ)^j*K)^2+u)*A2 := by
    calc
      _ ≤ ∫ x in spectralCut t ((4 : ℝ)^(j+1)*K), ‖A x‖^2 ∂μ :=
        integral_mono_measure hsub (Eventually.of_forall fun x => sq_nonneg _)
          (hMA _ hupper).norm.integrable_sq
      _ ≤ (((4 : ℝ)^(j+1)*K)^2+u)*A2 := hCumA _ hupper
      _ = _ := by rw [pow_succ]; ring
  have hEB : (∫ x in spectralShell t K j, ‖B x‖^2 ∂μ) ≤ ((4*(4 : ℝ)^j*K)^2+v)*B2 := by
    calc
      _ ≤ ∫ x in spectralCut t ((4 : ℝ)^(j+1)*K), ‖B x‖^2 ∂μ :=
        integral_mono_measure hsub (Eventually.of_forall fun x => sq_nonneg _)
          (hMB _ hupper).norm.integrable_sq
      _ ≤ (((4 : ℝ)^(j+1)*K)^2+v)*B2 := hCumB _ hupper
      _ = _ := by rw [pow_succ]; ring
  let d : ℝ := C*(1/(((4 : ℝ)^j*K)^2*Real.sqrt ((4 : ℝ)^j*K))+Y/((4 : ℝ)^j*K)^3)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hH : ∀ᵐ x ∂μ.restrict (spectralShell t K j), ‖H x‖ ≤ d := by
    filter_upwards [ae_restrict_mem (measurableSet_spectralShell ht K j)] with x hx
    exact transform_decay_on_shell {x} t H hK hC hY (fun i _ hi => hdecay i hi) j x
      (Finset.mem_filter.mpr ⟨Finset.mem_singleton_self x,hx⟩)
  obtain ⟨hint,hbound⟩ := integral_absolute_transform_budget
    (μ.restrict (spectralShell t K j)) H A B
      (MA := ((4*(4 : ℝ)^j*K)^2+u)*A2) (MB := ((4*(4 : ℝ)^j*K)^2+v)*B2)
      hd (by positivity) (by positivity)
      (hF.mono_measure Measure.restrict_le_self) ha hb hH hEA hEB
  refine ⟨hint,?_⟩
  calc
    _ ≤ d*Real.sqrt ((((4*(4 : ℝ)^j*K)^2+u)*A2)*(((4*(4 : ℝ)^j*K)^2+v)*B2)) := hbound
    _ ≤ d*((16*((4 : ℝ)^j)^2)*pairBudget K u v A2 B2) :=
      mul_le_mul_of_nonneg_left (scalar_pair_scale hp hu hv hA2 hB2) hd
    _ = _ := by
      dsimp [d]
      rw [sqrt_four_height hKpos j]
      have hp0 : (4 : ℝ)^j ≠ 0 := by positivity
      have hq0 : (2 : ℝ)^j ≠ 0 := by positivity
      have hs0 : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hKpos).ne'
      simp only [div_pow,one_pow]
      field_simp [hp0,hq0,hKpos.ne',hs0]
      ring

private theorem finite_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, r^j ≤ 1/(1-r) := by
  have hid : (∑ j ∈ Finset.range J, r^j)*(1-r) = 1-r^J := by
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith [ih]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [hid]
  exact sub_le_self _ (pow_nonneg hr0 _)

/-- Finite continuous cut with exact endpoint ownership. Both L1
membership and a bound uniform in J are conclusions. -/
theorem continuous_cutoff_payment (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ)
    (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x*A x*conj (B x)) μ)
    {K C Y E u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖A x‖^2 ∂μ) ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖B x‖^2 ∂μ) ≤ (T^2+v)*B2)
    (hlow : ∀ x ∈ spectralCut t K, ‖H x‖ ≤ E)
    (hdecay : ∀ x, K ≤ |t x| → ‖H x‖ ≤ C*(1/(|t x|^2*Real.sqrt |t x|)+Y/|t x|^3))
    (J : ℕ) :
    IntegrableOn (fun x => H x*A x*conj (B x)) (spectralCut t ((4 : ℝ)^J*K)) μ ∧
      (∫ x in spectralCut t ((4 : ℝ)^J*K), ‖H x*A x*conj (B x)‖ ∂μ) ≤
        (E+C*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3))*pairBudget K u v A2 B2 := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hlH : ∀ᵐ x ∂μ.restrict (spectralCut t K), ‖H x‖ ≤ E := by
    filter_upwards [ae_restrict_mem (measurableSet_spectralCut ht K)] with x hx
    exact hlow x hx
  obtain ⟨hli,hlb⟩ := integral_absolute_transform_budget (μ.restrict (spectralCut t K))
    H A B (MA := (K^2+u)*A2) (MB := (K^2+v)*B2) hE (by positivity) (by positivity)
      (hF.mono_measure Measure.restrict_le_self) (hMA K hK) (hMB K hK)
      hlH (hCumA K hK) (hCumB K hK)
  have hs := continuous_shell_payment μ t H A B ht hF hK hC hY hu hv hA2 hB2
    hMA hMB hCumA hCumB hdecay
  have hi (j : ℕ) : IntegrableOn (fun x => H x*A x*conj (B x))
      (spectralCut t ((4 : ℝ)^j*K)) μ := by
    induction j with
    | zero => simpa using hli
    | succ j ih =>
      rw [spectralCut_step t hK0 j]
      exact integrableOn_union.mpr ⟨ih,(hs j).1⟩
  have hdecomp (j : ℕ) :
      (∫ x in spectralCut t ((4 : ℝ)^j*K), ‖H x*A x*conj (B x)‖ ∂μ) =
        (∫ x in spectralCut t K, ‖H x*A x*conj (B x)‖ ∂μ) +
          ∑ l ∈ Finset.range j, ∫ x in spectralShell t K l, ‖H x*A x*conj (B x)‖ ∂μ := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [spectralCut_step t hK0 j,
        setIntegral_union (spectralCut_disjoint_shell t K j)
          (measurableSet_spectralShell ht K j) (hi j).norm (hs j).1.norm,
        ih,Finset.sum_range_succ]
      ring
  have hhalf : (∑ j ∈ Finset.range J, ((1 : ℝ)/2)^j) ≤ 2 := by
    convert finite_geometric_le (r := (1 : ℝ)/2) (by norm_num) (by norm_num) J using 1 <;> norm_num
  have hquarter : (∑ j ∈ Finset.range J, ((1 : ℝ)/4)^j) ≤ (4 : ℝ)/3 := by
    convert finite_geometric_le (r := (1 : ℝ)/4) (by norm_num) (by norm_num) J using 1 <;> norm_num
  have htail : (∑ j ∈ Finset.range J, ∫ x in spectralShell t K j, ‖H x*A x*conj (B x)‖ ∂μ) ≤
      C*pairBudget K u v A2 B2*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3) := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, 16*C*pairBudget K u v A2 B2 *
          (((1 : ℝ)/2)^j/(K^2*Real.sqrt K)+Y*((1 : ℝ)/4)^j/K^3) :=
        Finset.sum_le_sum (fun j _ => (hs j).2)
      _ = 16*C*pairBudget K u v A2 B2 *
          ((∑ j ∈ Finset.range J, ((1 : ℝ)/2)^j)/(K^2*Real.sqrt K)+
            Y*(∑ j ∈ Finset.range J, ((1 : ℝ)/4)^j)/K^3) := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_div]
      _ ≤ 16*C*pairBudget K u v A2 B2*(2/(K^2*Real.sqrt K)+Y*((4 : ℝ)/3)/K^3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add (div_le_div_of_nonneg_right hhalf (by positivity))
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquarter hY) (by positivity))
      _ = _ := by ring
  refine ⟨hi J,?_⟩
  rw [hdecomp J]
  calc
    _ ≤ E*pairBudget K u v A2 B2 +
        C*pairBudget K u v A2 B2*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3) := add_le_add hlb htail
    _ = _ := by ring

/-- Uniform bounds on honest L1 cuts imply global L1 and the integral
bound. The proof is monotone exhaustion of the nonnegative ENNReal
integral, so finiteness is established before using the full Bochner
integral. No convergence hypothesis is smuggled through totalization. -/
theorem integrable_exhaustion_of_cut_bound (μ : Measure α) (t : α → ℝ) (F : α → ℂ)
    {K L : ℝ} (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hF : AEStronglyMeasurable F μ)
    (hcut : ∀ j : ℕ, IntegrableOn F (spectralCut t ((4 : ℝ)^j*K)) μ ∧
      (∫ x in spectralCut t ((4 : ℝ)^j*K), ‖F x‖ ∂μ) ≤ L) :
    Integrable F μ ∧ (∫ x, ‖F x‖ ∂μ) ≤ L := by
  have hu := spectralCuts_iUnion t hK
  have hm := spectralCuts_monotone t ((by norm_num : (0 : ℝ) ≤ 1).trans hK)
  have he : (∫⁻ x, ‖F x‖ₑ ∂μ) ≤ ENNReal.ofReal L := by
    calc
      _ = ∫⁻ x in ⋃ j : ℕ, spectralCut t ((4 : ℝ)^j*K), ‖F x‖ₑ ∂μ := by rw [hu]; simp
      _ = ⨆ j : ℕ, ∫⁻ x in spectralCut t ((4 : ℝ)^j*K), ‖F x‖ₑ ∂μ :=
        setLIntegral_iUnion_of_directed _ hm.directed_le
      _ ≤ _ := by
        apply iSup_le
        intro j
        rw [← ofReal_integral_norm_eq_lintegral_enorm (hcut j).1]
        exact ENNReal.ofReal_le_ofReal (hcut j).2
  have hi : Integrable F μ :=
    ⟨hF,hasFiniteIntegral_iff_enorm.mpr (he.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi] at he
  exact (ENNReal.ofReal_le_ofReal_iff hL).mp he

/-- Full positive-measure regular return, with the SAME constant as
the finite J calculation. Applies to the continuous quadratic form,
and also to counting or weighted discrete measures. -/
theorem regular_R1_integrable (μ : Measure α) (t : α → ℝ) (H A B : α → ℂ)
    (ht : Measurable t)
    (hF : AEStronglyMeasurable (fun x => H x*A x*conj (B x)) μ)
    {C Y u v A2 B2 : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hMA : ∀ T : ℝ, 1 ≤ T → MemLp A 2 (μ.restrict (spectralCut t T)))
    (hMB : ∀ T : ℝ, 1 ≤ T → MemLp B 2 (μ.restrict (spectralCut t T)))
    (hCumA : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖A x‖^2 ∂μ) ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → (∫ x in spectralCut t T, ‖B x‖^2 ∂μ) ≤ (T^2+v)*B2)
    (hlow : ∀ x ∈ spectralCut t (regularBase Y), ‖H x‖ ≤ C*(1+|Real.log Y|)/(1+Y))
    (hdecay : ∀ x, regularBase Y ≤ |t x| →
      ‖H x‖ ≤ C*(1/(|t x|^2*Real.sqrt |t x|)+Y/|t x|^3)) :
    Integrable (fun x => H x*A x*conj (B x)) μ ∧
      (∫ x, ‖H x*A x*conj (B x)‖ ∂μ) ≤
        516*C*(1+|Real.log Y|)/(1+Y)*Real.sqrt (((1+Y^2+u)*A2)*((1+Y^2+v)*B2)) := by
  have hK : 1 ≤ regularBase Y := le_max_left _ _
  have hKY : 2*Y ≤ regularBase Y := le_max_right _ _
  have hE : 0 ≤ C*(1+|Real.log Y|)/(1+Y) := by positivity
  have htail := regular_tail_cost_le hK hY.le hKY
  have hpair := regularBase_pairBudget_le (Y := Y) hu hv hA2 hB2
  have hcoef : C*(1+|Real.log Y|)/(1+Y)+
      C*(32/((regularBase Y)^2*Real.sqrt (regularBase Y))+(64/3 : ℝ)*Y/(regularBase Y)^3) ≤
        129*C*(1+|Real.log Y|)/(1+Y) := by
    have ht' := mul_le_mul_of_nonneg_left htail hC
    have hcabs : 0 ≤ C*|Real.log Y| := mul_nonneg hC (abs_nonneg _)
    calc
      _ ≤ C*(1+|Real.log Y|)/(1+Y)+C*(128/(1+Y)) := add_le_add_left ht' _
      _ = (C*(1+|Real.log Y|)+128*C)/(1+Y) := by ring
      _ ≤ (129*C*(1+|Real.log Y|))/(1+Y) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  apply integrable_exhaustion_of_cut_bound μ t (fun x => H x*A x*conj (B x)) hK (by positivity) hF
  intro J
  obtain ⟨hi,hb⟩ := continuous_cutoff_payment μ t H A B ht hF hK hC hY.le hE hu hv hA2 hB2
    hMA hMB hCumA hCumB hlow hdecay J
  refine ⟨hi,?_⟩
  calc
    _ ≤ (C*(1+|Real.log Y|)/(1+Y)+
      C*(32/((regularBase Y)^2*Real.sqrt (regularBase Y))+(64/3 : ℝ)*Y/(regularBase Y)^3))*
        pairBudget (regularBase Y) u v A2 B2 := hb
    _ ≤ (129*C*(1+|Real.log Y|)/(1+Y))*
        (4*Real.sqrt (((1+Y^2+u)*A2)*((1+Y^2+v)*B2))) :=
      mul_le_mul hcoef hpair (pairBudget_nonneg _ _ _ _ _) (by positivity)
    _ = _ := by ring

/-- The genuine cutoff integrals converge to the full integral after
L1 was proved. This is the continuous spectral exhaustion port. -/
theorem regular_integral_exhaustion (μ : Measure α) (t : α → ℝ) (F : α → ℂ)
    (ht : Measurable t) (hF : Integrable F μ) {K : ℝ} (hK : 1 ≤ K) :
    Tendsto (fun j : ℕ => ∫ x in spectralCut t ((4 : ℝ)^j*K), F x ∂μ)
      atTop (𝓝 (∫ x, F x ∂μ)) := by
  have hu := spectralCuts_iUnion t hK
  have hi : IntegrableOn F (⋃ j : ℕ, spectralCut t ((4 : ℝ)^j*K)) μ := by
    simpa only [hu,integrableOn_univ] using hF
  have hh := tendsto_setIntegral_of_monotone (fun j => measurableSet_spectralCut ht _)
    (spectralCuts_monotone t ((by norm_num : (0 : ℝ) ≤ 1).trans hK)) hi
  simpa only [hu,Measure.restrict_univ] using hh

end
end ImbalancedChen.Part3.RegularPositiveMeasureExhaustion20261102
