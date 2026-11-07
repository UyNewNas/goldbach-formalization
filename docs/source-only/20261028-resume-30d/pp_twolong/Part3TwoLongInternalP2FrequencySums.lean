import Mathlib
import ImbalancedChen.Part3SmoothProgressionError

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual INTERNAL P2 frequency-sum deductions. The existing exact
Poisson-decay telescoping theorem is reused; no P2 bound is a premise.
The literal nonzero frequencies are j=d*k with k in Z\{0}. These
estimates hold for EVERY H>0, including H<1, before a modulus sum.
-/
namespace ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
noncomputable section
open Classical Set
open scoped BigOperators
open ImbalancedChen.Part3.CommonSmoothCutoff

/-- Literal Fourier decay at the nonzero d-multiples j=d*k. -/
def multipleDecay (H : ℝ) (d : ℕ) (k : ℤ) : ℝ :=
  if k=0 then 0 else 1 / (1 + |(d : ℝ)*(k : ℝ)|/H)^2

theorem multipleDecay_nonneg (H : ℝ) (d : ℕ) (k : ℤ) : 0 ≤ multipleDecay H d k := by
  unfold multipleDecay
  split_ifs <;> positivity

/-- Exact scale conversion to the already formalized telescoping kernel. -/
theorem multipleDecay_eq {H : ℝ} (hH : 0 < H) {d : ℕ} (hd : 0 < d) (k : ℤ) :
    multipleDecay H d k = (H/(d : ℝ)) * poissonNonzeroDecay ((d : ℝ)/H) k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hk : k=0
  · simp [multipleDecay,poissonNonzeroDecay,hk]
  · have hab : |((d : ℝ)/H)*(k : ℝ)| = |(d : ℝ)*(k : ℝ)|/H := by
      rw [div_mul_eq_mul_div,abs_div,abs_of_pos hH]
    simp only [multipleDecay,poissonNonzeroDecay,if_neg hk,hab]
    have hc : (H/(d : ℝ))*((d : ℝ)/H)=1 := by field_simp [hH.ne',hdR.ne']
    rw [← mul_div_assoc,hc]

/-- The manuscript's all-H nonzero divisible-frequency bound, with the
actual positive and negative frequency contributions both present. -/
theorem multipleDecay_summable_tsum_le {H : ℝ} (hH : 0 < H) {d : ℕ} (hd : 0 < d) :
    Summable (multipleDecay H d) ∧
      (∑' k : ℤ, multipleDecay H d k) ≤ 2*H/(d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hS,hB⟩ := poissonNonzeroDecay_summable_tsum_le (div_pos hdR hH)
  have heq : multipleDecay H d = fun k =>
      (H/(d : ℝ))*poissonNonzeroDecay ((d : ℝ)/H) k :=
    funext (multipleDecay_eq hH hd)
  rw [heq]
  refine ⟨hS.mul_left _,?_⟩
  rw [tsum_mul_left]
  calc
    _ ≤ (H/(d : ℝ))*2 := mul_le_mul_of_nonneg_left hB (div_pos hH hdR).le
    _ = _ := by ring

/-- Both nonzero frequency coordinates are paid BEFORE divisor expansion.
No missing coordinate axis is hidden inside the sum. -/
theorem double_multipleDecay_le {H K : ℝ} (hH : 0 < H) (hK : 0 < K)
    {d : ℕ} (hd : 0 < d) :
    (∑' j : ℤ, ∑' k : ℤ, multipleDecay H d j * multipleDecay K d k) ≤
      4*H*K/(d : ℝ)^2 := by
  obtain ⟨hSH,hBH⟩ := multipleDecay_summable_tsum_le hH hd
  obtain ⟨hSK,hBK⟩ := multipleDecay_summable_tsum_le hK hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    _ = (∑' j : ℤ, multipleDecay H d j) * (∑' k : ℤ, multipleDecay K d k) := by
      simp_rw [tsum_mul_left]
      rw [tsum_mul_right]
    _ ≤ (2*H/(d : ℝ))*(2*K/(d : ℝ)) :=
      mul_le_mul hBH hBK (tsum_nonneg (multipleDecay_nonneg K d)) (by positivity)
    _ = _ := by field_simp [hdR.ne']; ring

/-- The exact finite divisor moment left by the composite Weil expansion.
The q-independent bound is proved below from the existing p-series test. -/
def weilDivisorMoment (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, Real.sqrt (d : ℝ) / (d : ℝ)^2

theorem weil_divisor_frequency_mass {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    (∑ d ∈ q.divisors, Real.sqrt (d : ℝ) *
      (∑' j : ℤ, ∑' k : ℤ, multipleDecay H d j * multipleDecay K d k)) ≤
        (4*H*K) * weilDivisorMoment q := by
  calc
    _ ≤ ∑ d ∈ q.divisors, Real.sqrt (d : ℝ) * (4*H*K/(d : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (double_multipleDecay_le hH hK (Nat.pos_of_mem_divisors hd)) (Real.sqrt_nonneg _)
    _ = _ := by
      unfold weilDivisorMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring


/-- The uniform Weil divisor constant is an existing convergent p-series,
not a q-dependent divisor-count loss. -/
def weilWeight (d : ℕ) : ℝ := Real.sqrt (d : ℝ)/(d : ℝ)^2

theorem weilWeight_eq_rpow (d : ℕ) : weilWeight d = (d : ℝ)^(-3/2 : ℝ) := by
  by_cases hd : d=0
  · simp [weilWeight,hd,Real.zero_rpow (by norm_num : (-3/2 : ℝ) ≠ 0)]
  · have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    unfold weilWeight
    symm
    calc
      (d : ℝ)^(-3/2 : ℝ) = (d : ℝ)^((1/2 : ℝ)-(2 : ℝ)) := by norm_num
      _ = (d : ℝ)^(1/2 : ℝ)/(d : ℝ)^(2 : ℝ) := Real.rpow_sub hdR _ _
      _ = _ := by rw [← Real.sqrt_eq_rpow,Real.rpow_natCast]

theorem weilWeight_summable : Summable weilWeight := by
  have h := Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)
  simpa only [← weilWeight_eq_rpow] using h

def weilConstant : ℝ := ∑' d : ℕ, weilWeight d

theorem weilConstant_nonneg : 0 ≤ weilConstant :=
  tsum_nonneg (fun d => by unfold weilWeight; positivity)

theorem weilDivisorMoment_le_constant (q : ℕ) : weilDivisorMoment q ≤ weilConstant :=
  weilWeight_summable.sum_le_tsum q.divisors (fun d hd => by unfold weilWeight; positivity)

/-- The q-independent composite-Weil frequency budget in the original P2
argument, now derived without assuming P2. -/
theorem uniform_weil_frequency_mass {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    (∑ d ∈ q.divisors, Real.sqrt (d : ℝ) *
      (∑' j : ℤ, ∑' k : ℤ, multipleDecay H d j * multipleDecay K d k)) ≤
        (4*H*K)*weilConstant :=
  (weil_divisor_frequency_mass hH hK q).trans
    (mul_le_mul_of_nonneg_left (weilDivisorMoment_le_constant q) (by positivity))

/-- The gcd^(1/2) factor from composite Weil is dominated by the literal
finite sum of common divisors; its gcd itself is one of those divisors. -/
theorem sqrt_gcd_le_divisor_sum (q : ℕ) (hq : 0 < q) (j k : ℤ) :
    Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) ≤
      ∑ d ∈ q.divisors.filter (fun d => d ∣ j.natAbs ∧ d ∣ k.natAbs), Real.sqrt (d : ℝ) := by
  let g := Nat.gcd (Nat.gcd j.natAbs k.natAbs) q
  have hgj : g ∣ j.natAbs :=
    (Nat.gcd_dvd_left (Nat.gcd j.natAbs k.natAbs) q).trans
      (Nat.gcd_dvd_left j.natAbs k.natAbs)
  have hgk : g ∣ k.natAbs :=
    (Nat.gcd_dvd_left (Nat.gcd j.natAbs k.natAbs) q).trans
      (Nat.gcd_dvd_right j.natAbs k.natAbs)
  have hgq : g ∈ q.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _,hq.ne'⟩
  exact Finset.single_le_sum (fun d hd => Real.sqrt_nonneg (d : ℝ))
    (Finset.mem_filter.mpr ⟨hgq,hgj,hgk⟩)

/-- The separate elementary Ramanujan divisor mass from the original P2
proof. It uses actual totient<=d, not an assumed modulus budget. -/
theorem totient_divisor_mass_le (q : ℕ) :
    (∑ d ∈ q.divisors, (Nat.totient d : ℝ)/(d : ℝ)) ≤ (q.divisors.card : ℝ) := by
  calc
    _ ≤ ∑ _d ∈ q.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      apply (div_le_iff₀ hdR).2
      exact_mod_cast Nat.totient_le d
    _ = _ := by simp

def ramanujanFrequencyMass (H : ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, (Nat.totient d : ℝ) * ∑' k : ℤ, multipleDecay H d k

theorem ramanujanFrequencyMass_nonneg (H : ℝ) (q : ℕ) :
    0 ≤ ramanujanFrequencyMass H q := by
  unfold ramanujanFrequencyMass
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (by positivity) (tsum_nonneg (multipleDecay_nonneg H d))

theorem ramanujan_frequency_mass_le {H : ℝ} (hH : 0 < H) (q : ℕ) :
    ramanujanFrequencyMass H q ≤ 2*H*(q.divisors.card : ℝ) := by
  unfold ramanujanFrequencyMass
  calc
    _ ≤ ∑ d ∈ q.divisors, (Nat.totient d : ℝ) * (2*H/(d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (multipleDecay_summable_tsum_le hH (Nat.pos_of_mem_divisors hd)).2 (by positivity)
    _ = (2*H) * ∑ d ∈ q.divisors, (Nat.totient d : ℝ)/(d : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (totient_divisor_mass_le q) (by positivity)

/-- The two Ramanujan frequency coordinates give the original tau(q)^2
factor, without using the unproved INTERNAL P2 interface. -/
theorem double_ramanujan_mass_le {H K : ℝ} (hH : 0 < H) (hK : 0 < K) (q : ℕ) :
    ramanujanFrequencyMass H q * ramanujanFrequencyMass K q ≤
      4*H*K*(q.divisors.card : ℝ)^2 := by
  calc
    _ ≤ (2*H*(q.divisors.card : ℝ))*(2*K*(q.divisors.card : ℝ)) :=
      mul_le_mul (ramanujan_frequency_mass_le hH q) (ramanujan_frequency_mass_le hK q)
        (ramanujanFrequencyMass_nonneg K q) (by positivity)
    _ = _ := by ring

end
end ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
