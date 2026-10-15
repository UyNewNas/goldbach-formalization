import ImbalancedChen.CurrentChenUpsilon9ProductCoefficient
import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.TotientReciprocalBudget
import MathlibNt.SieveTheory.Arithmetic.LiuLogarithmicIntegral

/-!
# Paying the actual ninth coprimality gate

The Pan main term contains `Coprime a d`.  The actual coefficient is the
zero-one image of the original ninth selector, rather than a new arbitrary
bounded sequence.  This file pays the defect from replacing that gated
main term by its full mass, for the actual signed upper Rosser weight.

The finite divisor estimate uses the genuine supermultiplicativity of
Euler's totient.  Each selected multiplier has two prime factors at least
`N^(19/125)`.  The resulting signed correction is bounded in absolute value
by a constant times `N^(106/125) * (log N)^2`, hence by every positive
multiple of the original singular normalization.  No Pan estimate, count
mean, density constant, or main-term asymptotic is a premise.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight

/-- A crude linear bound used only to pay an error.  The actual
normalization of li is retained, and no leading constant is changed. -/
theorem currentChenUpsilon9_li_le_linear {x : ℝ} (hx : 2 ≤ x) :
    liuLogarithmicIntegral (2 / Real.log 2) x ≤ x / Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hint : (∫ t in (2 : ℝ)..x, 1 / Real.log t) ≤
      (x - 2) / Real.log 2 := by
    calc
      _ ≤ ∫ _t in (2 : ℝ)..x, 1 / Real.log 2 := by
        apply intervalIntegral.integral_mono_on hx
          (liuLogarithmicIntegrand_intervalIntegrable hx) intervalIntegrable_const
        intro t ht
        exact one_div_le_one_div_of_le hlog2
          (Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht.1)
      _ = _ := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
  unfold liuLogarithmicIntegral
  linarith

/-- A prime-divisible positive-modulus sum loses a factor `phi p`.
The cofactor need not be coprime to p: totient is supermultiplicative. -/
theorem currentChenUpsilon9_dvd_reciprocalTotient_sum_le
    (S : Finset ℕ) (Q p : ℕ) (hp : Nat.Prime p)
    (hS : S ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ S, if p ∣ d then 1 / (Nat.totient d : ℝ) else 0) ≤
      (4 / ((p : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))) := by
  let T := S.filter (fun d => p ∣ d)
  have hT : ∀ d ∈ T, 0 < d ∧ p ∣ d := by
    intro d hd
    obtain ⟨hdS, hpd⟩ := Finset.mem_filter.mp hd
    exact ⟨lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp (hS hdS)).1, hpd⟩
  have hquotpos : ∀ d ∈ T, 0 < d / p := by
    intro d hd
    apply Nat.pos_of_ne_zero
    intro hz
    have heq := Nat.mul_div_cancel' (hT d hd).2
    rw [hz, mul_zero] at heq
    exact (hT d hd).1.ne' heq.symm
  have hinj : Set.InjOn (fun d : ℕ => d / p) (T : Set ℕ) := by
    intro d hd e he hde
    calc
      d = p * (d / p) := (Nat.mul_div_cancel' (hT d hd).2).symm
      _ = p * (e / p) := by rw [hde]
      _ = e := Nat.mul_div_cancel' (hT e he).2
  have hquot : T.image (fun d => d / p) ⊆ Finset.Icc 1 Q := by
    intro m hm
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Icc.mpr ⟨hquotpos d hd,
      (Nat.div_le_self d p).trans (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hd).1)).2⟩
  have hpφ : (0 : ℝ) < Nat.totient p := by
    exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hterm : ∀ d ∈ T, 1 / (Nat.totient d : ℝ) ≤
      (1 / (Nat.totient p : ℝ)) * (1 / (Nat.totient (d / p) : ℝ)) := by
    intro d hd
    have hmφ : (0 : ℝ) < Nat.totient (d / p) := by
      exact_mod_cast Nat.totient_pos.mpr (hquotpos d hd)
    have hsuper : (Nat.totient p : ℝ) * (Nat.totient (d / p) : ℝ) ≤
        (Nat.totient d : ℝ) := by
      have h := Nat.totient_super_multiplicative p (d / p)
      rw [Nat.mul_div_cancel' (hT d hd).2] at h
      exact_mod_cast h
    calc
      _ ≤ 1 / ((Nat.totient p : ℝ) * (Nat.totient (d / p) : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos hpφ hmφ) hsuper
      _ = _ := by simp only [one_div, mul_inv_rev]; ring
  have hpcast : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  calc
    _ = ∑ d ∈ T, 1 / (Nat.totient d : ℝ) := by simp only [T, Finset.sum_filter]
    _ ≤ ∑ d ∈ T,
        (1 / (Nat.totient p : ℝ)) * (1 / (Nat.totient (d / p) : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (1 / (Nat.totient p : ℝ)) *
        ∑ m ∈ T.image (fun d => d / p), 1 / (Nat.totient m : ℝ) := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
    _ ≤ (1 / (Nat.totient p : ℝ)) *
        (4 * (1 + Real.log (max 1 (Q : ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_totient_subset_le_log _ Q hquot)
        (one_div_nonneg.mpr hpφ.le)
    _ = _ := by rw [hpcast]; ring

private theorem currentChenUpsilon9_prime_inverse_totient_le
    {p : ℕ} (hp : Nat.Prime p) {H : ℝ} (hH : 0 < H) (hHp : H ≤ p) :
    1 / ((p : ℝ) - 1) ≤ 2 / H := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hh : H / 2 ≤ (p : ℝ) - 1 := by linarith
  calc
    _ ≤ 1 / (H / 2) := one_div_le_one_div_of_le (half_pos hH) hh
    _ = _ := by field_simp [hH.ne']

/-- The actual product label pays the whole non-coprime divisor mass.
No equality between the Pan coprime gate and the presieve is assumed. -/
theorem currentChenUpsilon9_noncoprime_reciprocalTotient_sum_le
    {N a : ℕ} (hN : (1 : ℝ) ≤ N)
    (ha : a ∈ currentChenUpsilon9PrefixProducts N)
    (S : Finset ℕ) (Q : ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ S, if Nat.Coprime a d then 0 else 1 / (Nat.totient d : ℝ)) ≤
      (16 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hp₁, hp₂, horder⟩ := chenY9PrimeSelector_ordered_prime_data ht
  have hH := (Finset.mem_filter.mp ht).2.1
  have hH₂ : (N : ℝ) ^ (19 / 125 : ℝ) ≤ t.2 :=
    hH.trans (by exact_mod_cast horder.le)
  have hHpos : 0 < (N : ℝ) ^ (19 / 125 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _
  have hinv₁ := currentChenUpsilon9_prime_inverse_totient_le hp₁ hHpos hH
  have hinv₂ := currentChenUpsilon9_prime_inverse_totient_le hp₂ hHpos hH₂
  have hlog : 0 ≤ 1 + Real.log (max 1 (Q : ℝ)) := by
    have := Real.log_nonneg (le_max_left 1 (Q : ℝ))
    linarith
  have hpoint : ∀ d ∈ S,
      (if Nat.Coprime (t.1 * t.2) d then (0 : ℝ) else 1 / (Nat.totient d : ℝ)) ≤
        (if t.1 ∣ d then 1 / (Nat.totient d : ℝ) else 0) +
          (if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := by
    intro d _
    by_cases hc : Nat.Coprime (t.1 * t.2) d
    · rw [if_pos hc]
      positivity
    · have hd : t.1 ∣ d ∨ t.2 ∣ d := by
        by_contra hn
        push_neg at hn
        exact hc (Nat.coprime_mul_iff_left.mpr
          ⟨hp₁.coprime_iff_not_dvd.mpr hn.1, hp₂.coprime_iff_not_dvd.mpr hn.2⟩)
      rw [if_neg hc]
      rcases hd with hd | hd
      · rw [if_pos hd]
        have hh : 0 ≤ (if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := by positivity
        linarith
      · rw [if_pos hd]
        have hh : 0 ≤ (if t.1 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := by positivity
        linarith
  have hbudget₁ := currentChenUpsilon9_dvd_reciprocalTotient_sum_le S Q t.1 hp₁ hS
  have hbudget₂ := currentChenUpsilon9_dvd_reciprocalTotient_sum_le S Q t.2 hp₂ hS
  have hsum := (Finset.sum_le_sum hpoint).trans (by
    rw [Finset.sum_add_distrib]
    exact add_le_add hbudget₁ hbudget₂)
  have hinv := mul_le_mul_of_nonneg_right (add_le_add hinv₁ hinv₂) hlog
  nlinarith only [hsum, hinv]

/-- The literal ungated li main mass of the same actual product image. -/
def currentChenUpsilon9LiMainMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))

/-- The exact non-coprime part of that main mass, before applying the
same signed upper Rosser coefficient as in the count sieve. -/
def currentChenUpsilon9CoprimeMainDefect (N d : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    if Nat.Coprime a d then 0 else
      liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))

def currentChenUpsilon9CoprimeGateError (N cap : ℕ) (z L : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, actualSmallRosserPlus N cap z L d *
    (currentChenUpsilon9CoprimeMainDefect N d / (Nat.totient d : ℝ))

/-- The defect is the same zero-one coefficient in the actual Pan source
window.  Its coprimality gate is visible and unchanged. -/
theorem currentChenUpsilon9CoprimeMainDefect_eq_same_coefficient {N : ℕ}
    (hN : (1 : ℝ) ≤ N) (d : ℕ) :
    currentChenUpsilon9CoprimeMainDefect N d =
      ∑ a ∈ Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N),
        currentChenUpsilon9ProductCoefficient N a *
          (if Nat.Coprime a d then 0 else
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))) := by
  exact (currentChenUpsilon9ProductCoefficient_sum hN _).symm

/-- Finite payment with the actual signed Rosser coefficient.  Positivity
is used only for the genuine li mass, never imposed on the coefficient. -/
theorem currentChenUpsilon9_abs_coprimeGateError_le_mass
    {N : ℕ} (hN : (1 : ℝ) ≤ N)
    (hquot : ∀ a ∈ currentChenUpsilon9PrefixProducts N, 2 ≤ (N : ℝ) / (a : ℝ))
    (cap : ℕ) (z L : ℝ) (S : Finset ℕ) (Q : ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    |currentChenUpsilon9CoprimeGateError N cap z L S| ≤
      ((16 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) *
        currentChenUpsilon9LiMainMass N := by
  have hli : ∀ a ∈ currentChenUpsilon9PrefixProducts N,
      0 ≤ liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) := by
    intro a ha
    exact liuLogarithmicIntegral_nonneg _ (by positivity) (hquot a ha)
  have hdef : ∀ d, 0 ≤ currentChenUpsilon9CoprimeMainDefect N d := by
    intro d
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact le_refl 0
    · exact hli a ha
  have habs : |currentChenUpsilon9CoprimeGateError N cap z L S| ≤
      ∑ d ∈ S, currentChenUpsilon9CoprimeMainDefect N d / (Nat.totient d : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d _
    rw [abs_mul, abs_of_nonneg (div_nonneg (hdef d) (Nat.cast_nonneg _))]
    exact mul_le_of_le_one_left (div_nonneg (hdef d) (Nat.cast_nonneg _))
      (actualSmallRosserPlus_abs_le_one N cap z L d)
  have hswap : (∑ d ∈ S,
      currentChenUpsilon9CoprimeMainDefect N d / (Nat.totient d : ℝ)) =
      ∑ a ∈ currentChenUpsilon9PrefixProducts N,
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) *
          ∑ d ∈ S, if Nat.Coprime a d then 0 else 1 / (Nat.totient d : ℝ) := by
    simp only [currentChenUpsilon9CoprimeMainDefect, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hc : Nat.Coprime a d <;> simp only [hc, if_true, if_false, zero_div, mul_zero]
    ring
  rw [hswap] at habs
  apply habs.trans
  rw [currentChenUpsilon9LiMainMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (currentChenUpsilon9_noncoprime_reciprocalTotient_sum_le hN ha S Q hS) (hli a ha)

/-- The actual product powers put every li argument above two eventually. -/
theorem eventually_currentChenUpsilon9_li_arguments_two :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ currentChenUpsilon9PrefixProducts N,
      2 ≤ (N : ℝ) / (a : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (191 / 500 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 191 / 500)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlarge hN
  intro a ha
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hap : (0 : ℝ) < a := by exact_mod_cast (currentChenUpsilon9PrefixProducts_data ha).1
  have hprod : (N : ℝ) ^ (191 / 500 : ℝ) * (a : ℝ) ≤ (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) ^ (191 / 500 : ℝ) * (N : ℝ) ^ (309 / 500 : ℝ) :=
        mul_le_mul_of_nonneg_left (currentChenUpsilon9PrefixProducts_power_bounds hNr ha).2.le
          (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp, show (191 / 500 : ℝ) + 309 / 500 = 1 by norm_num,
          Real.rpow_one]
  exact hlarge.trans ((le_div_iff₀ hap).mpr hprod)

/-- A crude proved main-mass bound is sufficient for the gate error. -/
theorem currentChenUpsilon9_liMainMass_le_linear_log {N : ℕ}
    (hN : (1 : ℝ) ≤ N)
    (hquot : ∀ a ∈ currentChenUpsilon9PrefixProducts N, 2 ≤ (N : ℝ) / (a : ℝ)) :
    currentChenUpsilon9LiMainMass N ≤
      (4 / Real.log 2) * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsubset : currentChenUpsilon9PrefixProducts N ⊆ Finset.Icc 1 N := by
    intro a ha
    have hap := (currentChenUpsilon9PrefixProducts_data ha).1
    have haN : (a : ℝ) ≤ N :=
      (currentChenUpsilon9PrefixProducts_power_bounds hN ha).2.le.trans
        (Real.rpow_le_self_of_one_le hN (by norm_num))
    exact Finset.mem_Icc.mpr ⟨hap, by exact_mod_cast haN⟩
  have hweight : ∀ a ∈ currentChenUpsilon9PrefixProducts N,
      1 / (a : ℝ) ≤ 1 / (Nat.totient a : ℝ) := by
    intro a ha
    have hphi : (0 : ℝ) < Nat.totient a := by
      exact_mod_cast Nat.totient_pos.mpr (currentChenUpsilon9PrefixProducts_data ha).1
    exact one_div_le_one_div_of_le hphi (by exact_mod_cast Nat.totient_le a)
  calc
    _ ≤ ∑ a ∈ currentChenUpsilon9PrefixProducts N,
        ((N : ℝ) / (a : ℝ)) / Real.log 2 :=
      Finset.sum_le_sum (fun a ha => currentChenUpsilon9_li_le_linear (hquot a ha))
    _ = ((N : ℝ) / Real.log 2) *
        ∑ a ∈ currentChenUpsilon9PrefixProducts N, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ((N : ℝ) / Real.log 2) *
        ∑ a ∈ currentChenUpsilon9PrefixProducts N, 1 / (Nat.totient a : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hweight) (div_nonneg (Nat.cast_nonneg N) hlog2.le)
    _ ≤ ((N : ℝ) / Real.log 2) * (4 * (1 + Real.log (N : ℝ))) := by
      have h := sum_reciprocal_totient_subset_le_log _ N hsubset
      rw [max_eq_right hN] at h
      exact mul_le_mul_of_nonneg_left h (div_nonneg (Nat.cast_nonneg N) hlog2.le)
    _ = _ := by ring

/-- Every actual signed upper Rosser coprimality correction, on arbitrary
positive moduli through N chosen after N, has negligible normalized cost. -/
theorem eventually_currentChenUpsilon9_abs_coprimeGateError_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, ∀ z L : ℝ, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N →
      |currentChenUpsilon9CoprimeGateError N cap z L S| ≤
        ε * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    (256 / Real.log 2) (106 / 125) 2 (by norm_num) ε hε
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpower, hlog, eventually_currentChenUpsilon9_li_arguments_two,
    eventually_ge_atTop (1 : ℕ)] with N hpower hlog hquot hN
  intro cap z L S hS
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hH : 0 < (N : ℝ) ^ (19 / 125 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfactor : 0 ≤ (16 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (N : ℝ)) := by positivity
  have hfinite := currentChenUpsilon9_abs_coprimeGateError_le_mass hNr hquot cap z L S N hS
  rw [max_eq_right hNr] at hfinite
  have hmass := mul_le_mul_of_nonneg_left
    (currentChenUpsilon9_liMainMass_le_linear_log hNr hquot) hfactor
  have halgebra :
      ((16 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (N : ℝ))) *
        ((4 / Real.log 2) * (N : ℝ) * (1 + Real.log (N : ℝ))) =
      (64 / Real.log 2) * (N : ℝ) ^ (106 / 125 : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
    rw [show (106 / 125 : ℝ) = 1 - 19 / 125 by norm_num,
      Real.rpow_sub hNp, Real.rpow_one]
    ring
  have hlogs : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]
  have hcost := mul_le_mul_of_nonneg_left hlogs
    (show 0 ≤ (64 / Real.log 2) * (N : ℝ) ^ (106 / 125 : ℝ) by positivity)
  rw [halgebra] at hmass
  calc
    _ ≤ (64 / Real.log 2) * (N : ℝ) ^ (106 / 125 : ℝ) *
        (1 + Real.log (N : ℝ)) ^ 2 := hfinite.trans hmass
    _ ≤ (256 / Real.log 2) * (N : ℝ) ^ (106 / 125 : ℝ) * Real.log (N : ℝ) ^ 2 := by
      nlinarith only [hcost]
    _ ≤ _ := hpower

end

end ImbalancedChen
