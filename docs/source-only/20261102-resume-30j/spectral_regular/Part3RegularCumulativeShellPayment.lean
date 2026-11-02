import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Tactic

/-!
Source-only, uncompiled, zero formal credit.

Internal regular-spectrum height summation. The hypotheses are the two
positive cumulative quadratic-form bounds and the pointwise transform
bounds, not Eq24 or a bilinear spectral return. Heights grow by 4, so the
two summable tails have ratios 1/2 and 1/4. All constants and coefficient
norms remain explicit. This finite-cut theorem applies to discrete Maass
and holomorphic sums after their positive weights have been absorbed in
the two functionals. It does not claim the continuous Plancherel supplier.
-/

namespace ImbalancedChen.Part3.RegularCumulativeShellPayment20261102
noncomputable section
attribute [local instance] Classical.propDecidable
open Classical Finset
open scoped BigOperators ComplexConjugate

variable {ι : Type*}

def heightCut (S : Finset ι) (t : ι → ℝ) (T : ℝ) : Finset ι :=
  S.filter (fun i => |t i| ≤ T)

def heightShell (S : Finset ι) (t : ι → ℝ) (K : ℝ) (j : ℕ) : Finset ι :=
  S.filter (fun i => (4 : ℝ)^j*K < |t i| ∧ |t i| ≤ (4 : ℝ)^(j+1)*K)

def pairBudget (K u v A2 B2 : ℝ) : ℝ :=
  Real.sqrt (((K^2+u)*A2)*((K^2+v)*B2))

theorem pairBudget_nonneg (K u v A2 B2 : ℝ) : 0 ≤ pairBudget K u v A2 B2 :=
  Real.sqrt_nonneg _

theorem pairBudget_sq {K u v A2 B2 : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) :
    (pairBudget K u v A2 B2)^2 = ((K^2+u)*A2)*((K^2+v)*B2) := by
  unfold pairBudget
  exact Real.sq_sqrt (by positivity)

/-- Positive finite Cauchy, using only two quadratic-form budgets. -/
theorem finite_pair_budget (S : Finset ι) (A B : ι → ℂ)
    {MA MB : ℝ} (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hA : ∑ i ∈ S, ‖A i‖^2 ≤ MA) (hB : ∑ i ∈ S, ‖B i‖^2 ≤ MB) :
    ∑ i ∈ S, ‖A i‖*‖B i‖ ≤ Real.sqrt (MA*MB) := by
  have hsum : 0 ≤ ∑ i ∈ S, ‖A i‖*‖B i‖ :=
    sum_nonneg (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hB0 : 0 ≤ ∑ i ∈ S, ‖B i‖^2 := sum_nonneg (fun i hi => sq_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖A i‖) (fun i => ‖B i‖)
  have hp := mul_le_mul hA hB hB0 hMA
  have hs := Real.sq_sqrt (mul_nonneg hMA hMB)
  have hs0 := Real.sqrt_nonneg (MA*MB)
  nlinarith

theorem finite_absolute_transform_budget (S : Finset ι) (H A B : ι → ℂ)
    {d MA MB : ℝ} (hd : 0 ≤ d) (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hH : ∀ i ∈ S, ‖H i‖ ≤ d)
    (hA : ∑ i ∈ S, ‖A i‖^2 ≤ MA) (hB : ∑ i ∈ S, ‖B i‖^2 ≤ MB) :
    ∑ i ∈ S, ‖H i * A i * conj (B i)‖ ≤ d * Real.sqrt (MA*MB) := by
  calc
    _ = ∑ i ∈ S, ‖H i‖ * (‖A i‖*‖B i‖) := by
      apply sum_congr rfl
      intro i hi
      simp only [norm_mul, Complex.norm_conj]
      ring
    _ ≤ ∑ i ∈ S, d * (‖A i‖*‖B i‖) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hH i hi) (by positivity)
    _ = d * ∑ i ∈ S, ‖A i‖*‖B i‖ := by rw [mul_sum]
    _ ≤ d * Real.sqrt (MA*MB) :=
      mul_le_mul_of_nonneg_left (finite_pair_budget S A B hMA hMB hA hB) hd

private theorem cumulative_scale {K p u : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u) :
    (4*p*K)^2+u ≤ (16*p^2)*(K^2+u) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp2 : 1 ≤ p^2 := by nlinarith
  have hdiscard : 0 ≤ (16*p^2-1)*u := mul_nonneg (by nlinarith) hu
  nlinarith only [hdiscard]

/-- A shell costs 16*p^2 times the base positive norm product.  In
particular there is no extra loss of a full level count at this step. -/
theorem scaled_pair_budget (S : Finset ι) (A B : ι → ℂ)
    {K p u v A2 B2 : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hA : ∑ i ∈ S, ‖A i‖^2 ≤ ((4*p*K)^2+u)*A2)
    (hB : ∑ i ∈ S, ‖B i‖^2 ≤ ((4*p*K)^2+v)*B2) :
    ∑ i ∈ S, ‖A i‖*‖B i‖ ≤ (16*p^2)*pairBudget K u v A2 B2 := by
  have hA' : ∑ i ∈ S, ‖A i‖^2 ≤ (16*p^2)*((K^2+u)*A2) := by
    calc
      _ ≤ ((4*p*K)^2+u)*A2 := hA
      _ ≤ ((16*p^2)*(K^2+u))*A2 :=
        mul_le_mul_of_nonneg_right (cumulative_scale hp hu) hA2
      _ = _ := by ring
  have hB' : ∑ i ∈ S, ‖B i‖^2 ≤ (16*p^2)*((K^2+v)*B2) := by
    calc
      _ ≤ ((4*p*K)^2+v)*B2 := hB
      _ ≤ ((16*p^2)*(K^2+v))*B2 :=
        mul_le_mul_of_nonneg_right (cumulative_scale hp hv) hB2
      _ = _ := by ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖A i‖) (fun i => ‖B i‖)
  have hp' := mul_le_mul hA' hB' (sum_nonneg (fun i hi => sq_nonneg ‖B i‖))
    (show 0 ≤ (16*p^2)*((K^2+u)*A2) by positivity)
  have hs := pairBudget_sq (K := K) hu hv hA2 hB2
  have hs0 := pairBudget_nonneg K u v A2 B2
  have hsum0 : 0 ≤ ∑ i ∈ S, ‖A i‖*‖B i‖ := by positivity
  have hr0 : 0 ≤ (16*p^2)*pairBudget K u v A2 B2 := by positivity
  have hsq : (∑ i ∈ S, ‖A i‖*‖B i‖)^2 ≤
      ((16*p^2)*pairBudget K u v A2 B2)^2 := by
    calc
      _ ≤ (∑ i ∈ S, ‖A i‖^2)*(∑ i ∈ S, ‖B i‖^2) := hc
      _ ≤ ((16*p^2)*((K^2+u)*A2))*((16*p^2)*((K^2+v)*B2)) := hp'
      _ = ((16*p^2)*pairBudget K u v A2 B2)^2 := by rw [mul_pow, hs]; ring
  nlinarith

private theorem pow_four_eq_square_pow_two (j : ℕ) :
    (4 : ℝ)^j = ((2 : ℝ)^j)^2 := by
  calc
    (4 : ℝ)^j = ((2 : ℝ)^2)^j := by norm_num
    _ = ((2 : ℝ)^j)^2 := by rw [← pow_mul, ← pow_mul]; congr 1; omega

private theorem sqrt_four_height {K : ℝ} (hK : 0 < K) (j : ℕ) :
    Real.sqrt ((4 : ℝ)^j*K) = (2 : ℝ)^j*Real.sqrt K := by
  have hs := Real.sq_sqrt (show 0 ≤ (4 : ℝ)^j*K by positivity)
  have hKsq := Real.sq_sqrt hK.le
  have hpow := pow_four_eq_square_pow_two j
  have h0 := Real.sqrt_nonneg ((4 : ℝ)^j*K)
  have hr0 : 0 ≤ (2 : ℝ)^j*Real.sqrt K := by positivity
  have heq : ((2 : ℝ)^j*Real.sqrt K)^2 = (4 : ℝ)^j*K := by
    rw [mul_pow, hKsq, ← hpow]
  nlinarith

/-- The global high-height transform bound implies its shell supremum.
This is the t^(-5/2)+Y*t^(-3) estimate with positive denominators. -/
theorem transform_decay_on_shell (S : Finset ι) (t : ι → ℝ) (H : ι → ℂ)
    {K C Y : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3))
    (j : ℕ) (i : ι) (hi : i ∈ heightShell S t K j) :
    ‖H i‖ ≤ C*(1/(((4 : ℝ)^j*K)^2*Real.sqrt ((4 : ℝ)^j*K))+
      Y/((4 : ℝ)^j*K)^3) := by
  obtain ⟨hiS,hlo,hhi⟩ := mem_filter.mp hi
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hp : 1 ≤ (4 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hlower : K ≤ (4 : ℝ)^j*K := by nlinarith
  have hrpos : 0 < (4 : ℝ)^j*K := by positivity
  have htpos : 0 < |t i| := lt_trans hrpos hlo
  have hden1 : ((4 : ℝ)^j*K)^2*Real.sqrt ((4 : ℝ)^j*K) ≤
      |t i|^2*Real.sqrt |t i| :=
    mul_le_mul (pow_le_pow_left₀ hrpos.le hlo.le 2) (Real.sqrt_le_sqrt hlo.le)
      (Real.sqrt_nonneg _) (sq_nonneg _)
  have hden3 : ((4 : ℝ)^j*K)^3 ≤ |t i|^3 := pow_le_pow_left₀ hrpos.le hlo.le 3
  have hterm1 : 1/(|t i|^2*Real.sqrt |t i|) ≤
      1/(((4 : ℝ)^j*K)^2*Real.sqrt ((4 : ℝ)^j*K)) :=
    one_div_le_one_div_of_le (by positivity) hden1
  have hterm3 : Y/|t i|^3 ≤ Y/((4 : ℝ)^j*K)^3 := by
    exact div_le_div_of_nonneg_left hY (by positivity) hden3
  exact (hdecay i hiS (le_trans hlower hlo.le)).trans
    (mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm3) hC)

/-- A quantitative shell payment derived from cumulative quadratic forms.
Both norm factors grow like 4^j, while the transform leaves ratios 1/2
and 1/4.  No bilinear spectral-return inequality is a premise. -/
theorem regular_shell_absolute_payment (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {K C Y u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖A i‖^2 ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖B i‖^2 ≤ (T^2+v)*B2)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (j : ℕ) :
    ∑ i ∈ heightShell S t K j, ‖H i*A i*conj (B i)‖ ≤
      16*C*pairBudget K u v A2 B2 *
        (((1 : ℝ)/2)^j/(K^2*Real.sqrt K) + Y*((1 : ℝ)/4)^j/K^3) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hp : 1 ≤ (4 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hupper : 1 ≤ (4 : ℝ)^(j+1)*K := by
    have hp' : 1 ≤ (4 : ℝ)^(j+1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hsubset : heightShell S t K j ⊆ heightCut S t ((4 : ℝ)^(j+1)*K) := by
    intro i hi
    obtain ⟨hiS,hlo,hhi⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hiS,hhi⟩
  have hA : ∑ i ∈ heightShell S t K j, ‖A i‖^2 ≤
      ((4*(4 : ℝ)^j*K)^2+u)*A2 := by
    calc
      _ ≤ ∑ i ∈ heightCut S t ((4 : ℝ)^(j+1)*K), ‖A i‖^2 :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun i hi hnot => sq_nonneg _)
      _ ≤ (((4 : ℝ)^(j+1)*K)^2+u)*A2 := hCumA _ hupper
      _ = _ := by rw [pow_succ]; ring
  have hB : ∑ i ∈ heightShell S t K j, ‖B i‖^2 ≤
      ((4*(4 : ℝ)^j*K)^2+v)*B2 := by
    calc
      _ ≤ ∑ i ∈ heightCut S t ((4 : ℝ)^(j+1)*K), ‖B i‖^2 :=
        sum_le_sum_of_subset_of_nonneg hsubset (fun i hi hnot => sq_nonneg _)
      _ ≤ (((4 : ℝ)^(j+1)*K)^2+v)*B2 := hCumB _ hupper
      _ = _ := by rw [pow_succ]; ring
  let d : ℝ := C*(1/(((4 : ℝ)^j*K)^2*Real.sqrt ((4 : ℝ)^j*K))+
    Y/((4 : ℝ)^j*K)^3)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hpair := scaled_pair_budget (heightShell S t K j) A B hp hu hv hA2 hB2 hA hB
  calc
    _ = ∑ i ∈ heightShell S t K j, ‖H i‖*(‖A i‖*‖B i‖) := by
      apply sum_congr rfl
      intro i hi
      simp only [norm_mul,Complex.norm_conj]
      ring
    _ ≤ ∑ i ∈ heightShell S t K j, d*(‖A i‖*‖B i‖) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (transform_decay_on_shell S t H hK hC hY hdecay j i hi) (by positivity)
    _ = d*(∑ i ∈ heightShell S t K j, ‖A i‖*‖B i‖) := by rw [mul_sum]
    _ ≤ d*((16*((4 : ℝ)^j)^2)*pairBudget K u v A2 B2) :=
      mul_le_mul_of_nonneg_left hpair hd
    _ = 16*C*pairBudget K u v A2 B2 *
        (((1 : ℝ)/2)^j/(K^2*Real.sqrt K) + Y*((1 : ℝ)/4)^j/K^3) := by
      dsimp [d]
      rw [sqrt_four_height hKpos j]
      have hp0 : (4 : ℝ)^j ≠ 0 := by positivity
      have hq0 : (2 : ℝ)^j ≠ 0 := by positivity
      have hs0 : Real.sqrt K ≠ 0 := (Real.sqrt_pos.mpr hKpos).ne'
      simp only [div_pow, one_pow]
      field_simp [hp0,hq0,hKpos.ne',hs0]
      ring

private theorem finite_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℕ) :
    ∑ j ∈ range J, r^j ≤ 1/(1-r) := by
  have hid : (∑ j ∈ range J, r^j)*(1-r) = 1-r^J := by
    induction J with
    | zero => simp
    | succ J ih => rw [sum_range_succ, pow_succ]; nlinarith [ih]
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [hid]
  exact sub_le_self _ (pow_nonneg hr0 _)

/-- Summing arbitrarily many high shells has a constant cost.  This
explicit inequality is the missing convergent regular-height payment. -/
theorem finite_regular_shell_payment (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {K C Y u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖A i‖^2 ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖B i‖^2 ≤ (T^2+v)*B2)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (J : ℕ) :
    ∑ j ∈ range J, ∑ i ∈ heightShell S t K j, ‖H i*A i*conj (B i)‖ ≤
      C*pairBudget K u v A2 B2 *
        (32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hhalf : (∑ j ∈ range J, ((1 : ℝ)/2)^j) ≤ 2 := by
    convert finite_geometric_le (r := (1 : ℝ)/2) (by norm_num) (by norm_num) J using 1 <;> norm_num
  have hquarter : (∑ j ∈ range J, ((1 : ℝ)/4)^j) ≤ (4 : ℝ)/3 := by
    convert finite_geometric_le (r := (1 : ℝ)/4) (by norm_num) (by norm_num) J using 1 <;> norm_num
  calc
    _ ≤ ∑ j ∈ range J, 16*C*pairBudget K u v A2 B2 *
        (((1 : ℝ)/2)^j/(K^2*Real.sqrt K)+Y*((1 : ℝ)/4)^j/K^3) := by
      exact sum_le_sum (fun j hj => regular_shell_absolute_payment S t H A B
        hK hC hY hu hv hA2 hB2 hCumA hCumB hdecay j)
    _ = 16*C*pairBudget K u v A2 B2 *
        ((∑ j ∈ range J, ((1 : ℝ)/2)^j)/(K^2*Real.sqrt K)+
          Y*(∑ j ∈ range J, ((1 : ℝ)/4)^j)/K^3) := by
      rw [← mul_sum]
      congr 1
      simp only [mul_sum,sum_add_distrib,sum_div]
    _ ≤ 16*C*pairBudget K u v A2 B2 *
        (2/(K^2*Real.sqrt K)+Y*((4 : ℝ)/3)/K^3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (div_le_div_of_nonneg_right hhalf (by positivity))
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hquarter hY) (by positivity))
    _ = _ := by ring

/-- Low heights are paid by the uniform transform bound, independently
of the high-height estimate. Height zero is included in this exact cut. -/
theorem regular_low_absolute_payment (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {K E u v A2 B2 : ℝ} (hE : 0 ≤ E) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hA : ∑ i ∈ heightCut S t K, ‖A i‖^2 ≤ (K^2+u)*A2)
    (hB : ∑ i ∈ heightCut S t K, ‖B i‖^2 ≤ (K^2+v)*B2)
    (hH : ∀ i ∈ heightCut S t K, ‖H i‖ ≤ E) :
    ∑ i ∈ heightCut S t K, ‖H i*A i*conj (B i)‖ ≤ E*pairBudget K u v A2 B2 := by
  exact finite_absolute_transform_budget (heightCut S t K) H A B hE
    (by positivity) (by positivity) hH hA hB

private theorem heightCut_step (S : Finset ι) (t f : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (j : ℕ) :
    (∑ i ∈ heightCut S t ((4 : ℝ)^(j+1)*K), f i) =
      (∑ i ∈ heightCut S t ((4 : ℝ)^j*K), f i) +
        ∑ i ∈ heightShell S t K j, f i := by
  have hle : (4 : ℝ)^j*K ≤ (4 : ℝ)^(j+1)*K := by
    rw [pow_succ]
    have hp : 0 ≤ (4 : ℝ)^j*K := by positivity
    nlinarith
  simp only [heightCut,heightShell,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  by_cases hl : |t i| ≤ (4 : ℝ)^j*K
  · have hh : |t i| ≤ (4 : ℝ)^(j+1)*K := le_trans hl hle
    simp only [hl,hh,not_lt_of_ge hl,false_and,↓reduceIte,add_zero]
  · have hlt : (4 : ℝ)^j*K < |t i| := lt_of_not_ge hl
    by_cases hh : |t i| ≤ (4 : ℝ)^(j+1)*K <;>
      simp only [hl,hh,hlt,true_and,↓reduceIte,zero_add]

/-- Exact endpoint ownership in the height decomposition. -/
theorem heightCut_eq_low_add_shells (S : Finset ι) (t f : ι → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (J : ℕ) :
    (∑ i ∈ heightCut S t ((4 : ℝ)^J*K), f i) =
      (∑ i ∈ heightCut S t K, f i) +
        ∑ j ∈ range J, ∑ i ∈ heightShell S t K j, f i := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [heightCut_step S t f hK J, ih, sum_range_succ]
    ring

/-- Uniform in the truncation height. The LHS is the actual finite
spectral cut, not a newly defined list of disjoint shell placeholders. -/
theorem regular_cutoff_absolute_payment (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {K C Y E u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖A i‖^2 ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖B i‖^2 ≤ (T^2+v)*B2)
    (hlow : ∀ i ∈ heightCut S t K, ‖H i‖ ≤ E)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (J : ℕ) :
    ∑ i ∈ heightCut S t ((4 : ℝ)^J*K), ‖H i*A i*conj (B i)‖ ≤
      (E+C*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3))*pairBudget K u v A2 B2 := by
  rw [heightCut_eq_low_add_shells S t (fun i => ‖H i*A i*conj (B i)‖)
    (le_trans (by norm_num) hK) J]
  have hl := regular_low_absolute_payment S t H A B hE hu hv hA2 hB2
    (hCumA K hK) (hCumB K hK) hlow
  have hh := finite_regular_shell_payment S t H A B hK hC hY hu hv hA2 hB2
    hCumA hCumB hdecay J
  calc
    _ ≤ E*pairBudget K u v A2 B2 + C*pairBudget K u v A2 B2*
        (32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3) := add_le_add hl hh
    _ = _ := by ring

theorem regular_cutoff_norm_payment (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {K C Y E u v A2 B2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖A i‖^2 ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖B i‖^2 ≤ (T^2+v)*B2)
    (hlow : ∀ i ∈ heightCut S t K, ‖H i‖ ≤ E)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (J : ℕ) :
    ‖∑ i ∈ heightCut S t ((4 : ℝ)^J*K), H i*A i*conj (B i)‖ ≤
      (E+C*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3))*pairBudget K u v A2 B2 :=
  (norm_sum_le _ _).trans (regular_cutoff_absolute_payment S t H A B
    hK hC hY hE hu hv hA2 hB2 hCumA hCumB hlow hdecay J)

/-- The convergent tail has no positive power of Y. -/
theorem regular_tail_cost_le {K Y : ℝ} (hK : 1 ≤ K) (hY : 0 ≤ Y) (hKY : 2*Y ≤ K) :
    32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3 ≤ 128/(1+Y) := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hYpos : 0 < 1+Y := by positivity
  have hs0 := Real.sqrt_nonneg K
  have hs := Real.sq_sqrt hKpos.le
  have hs1 : 1 ≤ Real.sqrt K := by nlinarith
  have hK2 : K ≤ K^2 := by nlinarith
  have hden : K ≤ K^2*Real.sqrt K := by
    have hh := mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hs1)
    nlinarith
  have hone : 1/(K^2*Real.sqrt K) ≤ 1/K :=
    one_div_le_one_div_of_le hKpos hden
  have hsecond : Y/K^3 ≤ 1/K := by
    apply (div_le_div_iff₀ (pow_pos hKpos 3) hKpos).mpr
    have hY2 : Y ≤ K^2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hY2 hKpos.le
    nlinarith only [hprod]
  have hcompare : 1/K ≤ 2/(1+Y) := by
    apply (div_le_div_iff₀ hKpos hYpos).mpr
    nlinarith
  have h1 := hone.trans hcompare
  have h2 := hsecond.trans hcompare
  calc
    32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3 =
        32*(1/(K^2*Real.sqrt K))+(64/3 : ℝ)*(Y/K^3) := by ring
    _ ≤ 32*(2/(1+Y))+(64/3 : ℝ)*(2/(1+Y)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
        (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = ((320 : ℝ)/3)/(1+Y) := by ring
    _ ≤ 128/(1+Y) := div_le_div_of_nonneg_right (by norm_num) hYpos.le

def regularBase (Y : ℝ) : ℝ := max 1 (2*Y)

theorem regularBase_sq_le (Y : ℝ) : (regularBase Y)^2 ≤ 4*(1+Y^2) := by
  unfold regularBase
  by_cases h : 1 ≤ 2*Y
  · rw [max_eq_right h]
    nlinarith [sq_nonneg Y]
  · rw [max_eq_left (le_of_not_ge h)]
    nlinarith [sq_nonneg Y]

theorem regularBase_pairBudget_le {Y u v A2 B2 : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2) :
    pairBudget (regularBase Y) u v A2 B2 ≤
      4*Real.sqrt (((1+Y^2+u)*A2)*((1+Y^2+v)*B2)) := by
  have hbase := regularBase_sq_le Y
  have ha : ((regularBase Y)^2+u)*A2 ≤ 4*((1+Y^2+u)*A2) := by
    calc
      _ ≤ (4*(1+Y^2+u))*A2 := mul_le_mul_of_nonneg_right (by nlinarith) hA2
      _ = _ := by ring
  have hb : ((regularBase Y)^2+v)*B2 ≤ 4*((1+Y^2+v)*B2) := by
    calc
      _ ≤ (4*(1+Y^2+v))*B2 := mul_le_mul_of_nonneg_right (by nlinarith) hB2
      _ = _ := by ring
  have hp := mul_le_mul ha hb (show 0 ≤ ((regularBase Y)^2+v)*B2 by positivity)
    (show 0 ≤ 4*((1+Y^2+u)*A2) by positivity)
  have hs := pairBudget_sq (K := regularBase Y) hu hv hA2 hB2
  have hs0 := pairBudget_nonneg (regularBase Y) u v A2 B2
  have hr := Real.sq_sqrt (show 0 ≤ ((1+Y^2+u)*A2)*((1+Y^2+v)*B2) by positivity)
  have hr0 := Real.sqrt_nonneg (((1+Y^2+u)*A2)*((1+Y^2+v)*B2))
  nlinarith

/-- Explicit finite-cut R1. This derives the full regular Y dependence
from the primitive cumulative and transform estimates; 516 is absolute.
No parameter |a|, auxiliary nu, or spectral height is hidden in it. -/
theorem regular_R1_finite (S : Finset ι) (t : ι → ℝ) (H A B : ι → ℂ)
    {C Y u v A2 B2 : ℝ} (hC : 0 ≤ C) (hY : 0 < Y)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hA2 : 0 ≤ A2) (hB2 : 0 ≤ B2)
    (hCumA : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖A i‖^2 ≤ (T^2+u)*A2)
    (hCumB : ∀ T : ℝ, 1 ≤ T → ∑ i ∈ heightCut S t T, ‖B i‖^2 ≤ (T^2+v)*B2)
    (hlow : ∀ i ∈ heightCut S t (regularBase Y),
      ‖H i‖ ≤ C*(1+|Real.log Y|)/(1+Y))
    (hdecay : ∀ i ∈ S, regularBase Y ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (J : ℕ) :
    ‖∑ i ∈ heightCut S t ((4 : ℝ)^J*regularBase Y), H i*A i*conj (B i)‖ ≤
      516*C*(1+|Real.log Y|)/(1+Y)*
        Real.sqrt (((1+Y^2+u)*A2)*((1+Y^2+v)*B2)) := by
  have hK : 1 ≤ regularBase Y := le_max_left _ _
  have hKY : 2*Y ≤ regularBase Y := le_max_right _ _
  have hE : 0 ≤ C*(1+|Real.log Y|)/(1+Y) := by positivity
  have htail := regular_tail_cost_le hK hY.le hKY
  have hpair := regularBase_pairBudget_le (Y := Y) hu hv hA2 hB2
  have hcoef : C*(1+|Real.log Y|)/(1+Y)+
      C*(32/((regularBase Y)^2*Real.sqrt (regularBase Y))+
        (64/3 : ℝ)*Y/(regularBase Y)^3) ≤
      129*C*(1+|Real.log Y|)/(1+Y) := by
    have ht := mul_le_mul_of_nonneg_left htail hC
    have hcabs : 0 ≤ C*|Real.log Y| := mul_nonneg hC (abs_nonneg _)
    have hp : 0 < 1+Y := by positivity
    calc
      _ ≤ C*(1+|Real.log Y|)/(1+Y)+C*(128/(1+Y)) := add_le_add_left ht _
      _ = (C*(1+|Real.log Y|)+128*C)/(1+Y) := by ring
      _ ≤ (129*C*(1+|Real.log Y|))/(1+Y) :=
        div_le_div_of_nonneg_right (by nlinarith) hp.le
  have hc0 : 0 ≤ 129*C*(1+|Real.log Y|)/(1+Y) := by positivity
  calc
    _ ≤ (C*(1+|Real.log Y|)/(1+Y)+
        C*(32/((regularBase Y)^2*Real.sqrt (regularBase Y))+
          (64/3 : ℝ)*Y/(regularBase Y)^3))*pairBudget (regularBase Y) u v A2 B2 :=
      regular_cutoff_norm_payment S t H A B hK hC hY.le hE hu hv hA2 hB2
        hCumA hCumB hlow hdecay J
    _ ≤ (129*C*(1+|Real.log Y|)/(1+Y))*
        (4*Real.sqrt (((1+Y^2+u)*A2)*((1+Y^2+v)*B2))) :=
      mul_le_mul hcoef hpair (pairBudget_nonneg _ _ _ _ _) hc0
    _ = _ := by ring

open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)

variable {ρ : Type*}

def originalMFunctional (P : PacketData ρ) (k : D4 → ℤ)
    (R : ι → ℕ → ℂ) (i : ι) : ℂ :=
  ∑ m ∈ P.mCarrier, (P.completed k).weight m * R i m

def originalNFunctional (P : PacketData ρ) (k : D4 → ℤ) (r : ρ)
    (R : ι → ℕ → ℂ) (i : ι) : ℂ :=
  ∑ n ∈ P.nCarrier r,
    signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n * R i n

def originalNEnergy (P : PacketData ρ) (r : ρ) : ℝ :=
  ∑ n ∈ P.nCarrier r, ‖(P.packet r).transformedCoefficient n‖^2

theorem originalM_coefficient_norm (P : PacketData ρ) (k : D4 → ℤ) :
    ∑ m ∈ P.mCarrier, ‖(P.completed k).weight m‖^2 = (P.mCarrier.card : ℝ) := by
  calc
    _ = ∑ _m ∈ P.mCarrier, (1 : ℝ) := by
      apply sum_congr rfl
      intro m hm
      rw [P.completed_weight_norm_mem k m hm]
      norm_num
    _ = _ := by simp

theorem originalN_coefficient_norm (P : PacketData ρ) (k : D4 → ℤ) (r : ρ) :
    ∑ n ∈ P.nCarrier r,
      ‖signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n‖^2 =
        originalNEnergy P r := by
  apply sum_congr rfl
  intro n hn
  rw [norm_signedCoefficient_modePacket]

/-- Row Cauchy retains the actual row count. The following theorem pays
the level count only after injectivity at a fixed auxiliary label. -/
theorem original_level_cauchy (P : PacketData ρ) :
    ∑ r ∈ P.rows, Real.sqrt (originalNEnergy P r) ≤
      Real.sqrt ((P.rows.card : ℝ)*(∑ r ∈ P.rows, originalNEnergy P r)) := by
  have he (r : ρ) : 0 ≤ originalNEnergy P r := by
    exact sum_nonneg (fun n hn => sq_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq P.rows (fun _ => (1 : ℝ))
    (fun r => Real.sqrt (originalNEnergy P r))
  have heq : (∑ r ∈ P.rows, Real.sqrt (originalNEnergy P r)^2) =
      ∑ r ∈ P.rows, originalNEnergy P r := by
    apply sum_congr rfl
    intro r hr
    exact Real.sq_sqrt (he r)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,heq] at hc
  have hs := Real.sq_sqrt (show 0 ≤ (P.rows.card : ℝ)*
    (∑ r ∈ P.rows, originalNEnergy P r) by positivity)
  have hs0 := Real.sqrt_nonneg ((P.rows.card : ℝ)*(∑ r ∈ P.rows, originalNEnergy P r))
  have hleft : 0 ≤ ∑ r ∈ P.rows, Real.sqrt (originalNEnergy P r) := by positivity
  nlinarith

/-- A genuine level average for a fixed-nu row family: the level map must
be injective. This prevents counting arbitrary (nu,z) rows as just z.
Positive integer levels bounded by 2Z give at most 2Z levels, also for
1/2 <= Z < 1. No rounded Z >= 1 assumption is used. -/
theorem original_level_average (P : PacketData ρ) {Z : ℝ} (hZ : (1 : ℝ)/2 ≤ Z)
    (hinj : Set.InjOn (fun r => (P.packet r).level) (P.rows : Set ρ))
    (hlevels : ∀ r ∈ P.rows, ((P.packet r).level : ℝ) ≤ 2*Z) :
    ∑ r ∈ P.rows, Real.sqrt (originalNEnergy P r) ≤
      Real.sqrt ((2*Z)*(∑ r ∈ P.rows, originalNEnergy P r)) := by
  have himage : (P.rows.image (fun r => (P.packet r).level)).card = P.rows.card :=
    Finset.card_image_of_injOn hinj
  have hsub : P.rows.image (fun r => (P.packet r).level) ⊆ Icc 1 (Nat.floor (2*Z)) := by
    intro z hz
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hz
    exact mem_Icc.mpr ⟨(P.packet r).level_pos, Nat.le_floor (hlevels r hr)⟩
  have hcard : P.rows.card ≤ Nat.floor (2*Z) := by
    have h := card_le_card hsub
    simpa only [himage,Nat.card_Icc,Nat.add_sub_cancel] using h
  have hcardR : (P.rows.card : ℝ) ≤ 2*Z := by
    calc
      (P.rows.card : ℝ) ≤ (Nat.floor (2*Z) : ℝ) := by exact_mod_cast hcard
      _ ≤ 2*Z := Nat.floor_le (by linarith)
  have he : 0 ≤ ∑ r ∈ P.rows, originalNEnergy P r :=
    sum_nonneg (fun r hr => sum_nonneg (fun n hn => sq_nonneg _))
  exact (original_level_cauchy P).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hcardR he))

/-- Consumer at the literal common-interval/common-phase packet. The
two cumulative hypotheses are the fixed-level primitive quadratic-form
inputs; they are not a regular bilinear bound or Eq24. The theorem keeps
their exact original coefficient norms until the proved norm identities
above replace them. Automorphic R/measure identification remains upstream. -/
theorem original_packet_regular_cutoff (P : PacketData ρ) (k : D4 → ℤ) (r : ρ)
    (S : Finset ι) (t : ι → ℝ) (H : ι → ℂ) (Rinf Rone : ι → ℕ → ℂ)
    {K C Y E u v C1 C2 : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hY : 0 ≤ Y) (hE : 0 ≤ E)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hCumM : ∀ T : ℝ, 1 ≤ T →
      ∑ i ∈ heightCut S t T, ‖originalMFunctional P k Rinf i‖^2 ≤
        (T^2+u)*(C1*∑ m ∈ P.mCarrier, ‖(P.completed k).weight m‖^2))
    (hCumN : ∀ T : ℝ, 1 ≤ T →
      ∑ i ∈ heightCut S t T, ‖originalNFunctional P k r Rone i‖^2 ≤
        (T^2+v)*(C2*∑ n ∈ P.nCarrier r,
          ‖signedCoefficient P.negativeCusp (modePacket (P.packet r) k P.U P.Z) n‖^2))
    (hlow : ∀ i ∈ heightCut S t K, ‖H i‖ ≤ E)
    (hdecay : ∀ i ∈ S, K ≤ |t i| →
      ‖H i‖ ≤ C*(1/(|t i|^2*Real.sqrt |t i|)+Y/|t i|^3)) (J : ℕ) :
    ‖∑ i ∈ heightCut S t ((4 : ℝ)^J*K), H i*originalMFunctional P k Rinf i*
        conj (originalNFunctional P k r Rone i)‖ ≤
      (E+C*(32/(K^2*Real.sqrt K)+(64/3 : ℝ)*Y/K^3))*
        pairBudget K u v (C1*(P.mCarrier.card : ℝ)) (C2*originalNEnergy P r) := by
  have he : 0 ≤ originalNEnergy P r := sum_nonneg (fun n hn => sq_nonneg _)
  apply regular_cutoff_norm_payment S t H (originalMFunctional P k Rinf)
    (originalNFunctional P k r Rone) hK hC hY hE hu hv (by positivity) (by positivity)
    _ _ hlow hdecay J
  · intro T hT
    simpa only [originalM_coefficient_norm] using hCumM T hT
  · intro T hT
    simpa only [originalN_coefficient_norm] using hCumN T hT

end
end ImbalancedChen.Part3.RegularCumulativeShellPayment20261102
