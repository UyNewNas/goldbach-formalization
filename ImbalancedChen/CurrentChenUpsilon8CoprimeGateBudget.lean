import ImbalancedChen.CurrentChenUpsilon8ProductPan

/-!
# Paying the literal eighth coprimality gate

The actual eighth zero-one product coefficient is independent of the
sieve modulus. Its Pan main term keeps the true `Coprime a d` gate.
The two genuine prime factors are both at least N^(417/5000), so the
proved reciprocal-totient divisor estimate pays their non-coprime mass.
The cofactor need not be coprime to either prime.

The same signed upper Rosser coefficient is retained throughout. Its
absolute gate correction costs O(N^(4583/5000) (log N)^2), paid by the
existing power error budget. All li positivity and moving-argument
conditions are established from the actual eighth source before the
final threshold; they are not caller hypotheses. That threshold precedes
cap, z, L and the positive-modulus set chosen through N.

This leaf supplies no count majorant, density value, harmonic mean or
adopted upper constant. The already owned generic prime-divisor estimate
and the crude true-li bound are reused rather than reproved.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight

private theorem currentChenUpsilon8_prime_inverse_totient_le
    {p : ℕ} (hp : Nat.Prime p) {H : ℝ} (hH : 0 < H) (hHp : H ≤ p) :
    1 / ((p : ℝ) - 1) ≤ 2 / H := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hh : H / 2 ≤ (p : ℝ) - 1 := by linarith
  calc
    _ ≤ 1 / (H / 2) := one_div_le_one_div_of_le (half_pos hH) hh
    _ = _ := by field_simp [hH.ne']

/-- The literal eighth product label pays the whole non-coprime divisor mass.
No equality between the Pan coprime gate and the presieve is assumed. -/
theorem currentChenUpsilon8_noncoprime_reciprocalTotient_sum_le
    {N a : ℕ} (hN : (1 : ℝ) ≤ N)
    (ha : a ∈ currentChenUpsilon8PrefixProducts N)
    (S : Finset ℕ) (Q : ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ S, if Nat.Coprime a d then 0 else 1 / (Nat.totient d : ℝ)) ≤
      (16 / (N : ℝ) ^ (417 / 5000 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hp₁, hp₂, horder⟩ := chenY9PrimeSelector_ordered_prime_data
    (show t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) from ht)
  have hH := (Finset.mem_filter.mp ht).2.1
  have hH₂ : (N : ℝ) ^ (417 / 5000 : ℝ) ≤ t.2 :=
    hH.trans (by exact_mod_cast horder.le)
  have hHpos : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _
  have hinv₁ := currentChenUpsilon8_prime_inverse_totient_le hp₁ hHpos hH
  have hinv₂ := currentChenUpsilon8_prime_inverse_totient_le hp₂ hHpos hH₂
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
        push Not at hn
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
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  have hsumBudget := hsum.trans (add_le_add hbudget₁ hbudget₂)
  have hinv := mul_le_mul_of_nonneg_right (add_le_add hinv₁ hinv₂) hlog
  calc
    _ ≤ (4 / ((t.1 : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))) +
        (4 / ((t.2 : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))) := hsumBudget
    _ = 4 * ((1 / ((t.1 : ℝ) - 1) + 1 / ((t.2 : ℝ) - 1)) *
        (1 + Real.log (max 1 (Q : ℝ)))) := by ring
    _ ≤ 4 * ((2 / (N : ℝ) ^ (417 / 5000 : ℝ) + 2 / (N : ℝ) ^ (417 / 5000 : ℝ)) *
        (1 + Real.log (max 1 (Q : ℝ)))) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

/-- The literal ungated li main mass of the same actual product image. -/
def currentChenUpsilon8LiMainMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon8PrefixProducts N,
    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))

/-- The exact non-coprime part of that main mass, before applying the
same signed upper Rosser coefficient as in the count sieve. -/
def currentChenUpsilon8CoprimeMainDefect (N d : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon8PrefixProducts N,
    if Nat.Coprime a d then 0 else
      liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))

def currentChenUpsilon8CoprimeGateError (N cap : ℕ) (z L : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, actualSmallRosserPlus N cap z L d *
    (currentChenUpsilon8CoprimeMainDefect N d / (Nat.totient d : ℝ))

/-- The defect is the same zero-one coefficient in the actual Pan source
window.  Its coprimality gate is visible and unchanged. -/
theorem currentChenUpsilon8CoprimeMainDefect_eq_same_coefficient {N : ℕ}
    (hN : (1 : ℝ) ≤ N) (d : ℕ) :
    currentChenUpsilon8CoprimeMainDefect N d =
      ∑ a ∈ Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N),
        currentChenUpsilon8ProductCoefficient N a *
          (if Nat.Coprime a d then 0 else
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ))) := by
  exact (currentChenUpsilon8ProductCoefficient_sum hN _).symm

/-- Finite payment with the actual signed Rosser coefficient.  Positivity
is used only for the genuine li mass, never imposed on the coefficient. -/
theorem currentChenUpsilon8_abs_coprimeGateError_le_mass
    {N : ℕ} (hN : (1 : ℝ) ≤ N)
    (hquot : ∀ a ∈ currentChenUpsilon8PrefixProducts N, 2 ≤ (N : ℝ) / (a : ℝ))
    (cap : ℕ) (z L : ℝ) (S : Finset ℕ) (Q : ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    |currentChenUpsilon8CoprimeGateError N cap z L S| ≤
      ((16 / (N : ℝ) ^ (417 / 5000 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) *
        currentChenUpsilon8LiMainMass N := by
  have hli : ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      0 ≤ liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) := by
    intro a ha
    exact liuLogarithmicIntegral_nonneg _ (by positivity) (hquot a ha)
  have hdef : ∀ d, 0 ≤ currentChenUpsilon8CoprimeMainDefect N d := by
    intro d
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact le_refl 0
    · exact hli a ha
  have habs : |currentChenUpsilon8CoprimeGateError N cap z L S| ≤
      ∑ d ∈ S, currentChenUpsilon8CoprimeMainDefect N d / (Nat.totient d : ℝ) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d _
    rw [abs_mul, abs_of_nonneg (div_nonneg (hdef d) (Nat.cast_nonneg _))]
    exact mul_le_of_le_one_left (div_nonneg (hdef d) (Nat.cast_nonneg _))
      (actualSmallRosserPlus_abs_le_one N cap z L d)
  have hswap : (∑ d ∈ S,
      currentChenUpsilon8CoprimeMainDefect N d / (Nat.totient d : ℝ)) =
      ∑ a ∈ currentChenUpsilon8PrefixProducts N,
        liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) *
          ∑ d ∈ S, if Nat.Coprime a d then 0 else 1 / (Nat.totient d : ℝ) := by
    simp only [currentChenUpsilon8CoprimeMainDefect, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> ring
  rw [hswap] at habs
  apply habs.trans
  rw [currentChenUpsilon8LiMainMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (currentChenUpsilon8_noncoprime_reciprocalTotient_sum_le hN ha S Q hS) (hli a ha)

/-- The actual product powers put every li argument above two eventually. -/
theorem eventually_currentChenUpsilon8_li_arguments_two :
    ∀ᶠ N : ℕ in atTop, ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      2 ≤ (N : ℝ) / (a : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlarge hN
  intro a ha
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact hlarge.trans (currentChenUpsilon8_li_argument_power_lower hNr ha)

/-- A crude proved main-mass bound is sufficient for the gate error. -/
theorem currentChenUpsilon8_liMainMass_le_linear_log {N : ℕ}
    (hN : (1 : ℝ) ≤ N)
    (hquot : ∀ a ∈ currentChenUpsilon8PrefixProducts N, 2 ≤ (N : ℝ) / (a : ℝ)) :
    currentChenUpsilon8LiMainMass N ≤
      (4 / Real.log 2) * (N : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsubset : currentChenUpsilon8PrefixProducts N ⊆ Finset.Icc 1 N := by
    intro a ha
    have hap := (currentChenUpsilon8PrefixProducts_data ha).1
    have haN : (a : ℝ) ≤ N :=
      (currentChenUpsilon8PrefixProducts_power_bounds hN ha).2.le.trans
        (Real.rpow_le_self_of_one_le hN (by norm_num))
    exact Finset.mem_Icc.mpr ⟨hap, by exact_mod_cast haN⟩
  have hweight : ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      1 / (a : ℝ) ≤ 1 / (Nat.totient a : ℝ) := by
    intro a ha
    have hphi : (0 : ℝ) < Nat.totient a := by
      exact_mod_cast Nat.totient_pos.mpr (currentChenUpsilon8PrefixProducts_data ha).1
    exact one_div_le_one_div_of_le hphi (by exact_mod_cast Nat.totient_le a)
  calc
    _ ≤ ∑ a ∈ currentChenUpsilon8PrefixProducts N,
        ((N : ℝ) / (a : ℝ)) / Real.log 2 :=
      Finset.sum_le_sum (fun a ha => currentChenUpsilon9_li_le_linear (hquot a ha))
    _ = ((N : ℝ) / Real.log 2) *
        ∑ a ∈ currentChenUpsilon8PrefixProducts N, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ((N : ℝ) / Real.log 2) *
        ∑ a ∈ currentChenUpsilon8PrefixProducts N, 1 / (Nat.totient a : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hweight) (div_nonneg (Nat.cast_nonneg N) hlog2.le)
    _ ≤ ((N : ℝ) / Real.log 2) * (4 * (1 + Real.log (N : ℝ))) := by
      have h := sum_reciprocal_totient_subset_le_log _ N hsubset
      rw [max_eq_right hN] at h
      exact mul_le_mul_of_nonneg_left h (div_nonneg (Nat.cast_nonneg N) hlog2.le)
    _ = _ := by ring

/-- Every actual signed upper Rosser coprimality correction, on arbitrary
positive moduli through N chosen after N, has negligible normalized cost. -/
theorem eventually_currentChenUpsilon8_abs_coprimeGateError_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, ∀ z L : ℝ, ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N →
      |currentChenUpsilon8CoprimeGateError N cap z L S| ≤
        ε * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    (256 / Real.log 2) (4583 / 5000) 2 (by norm_num) ε hε
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpower, hlog, eventually_currentChenUpsilon8_li_arguments_two,
    eventually_ge_atTop (1 : ℕ)] with N hpower hlog hquot hN
  intro cap z L S hS
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hH : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfactor : 0 ≤ (16 / (N : ℝ) ^ (417 / 5000 : ℝ)) * (1 + Real.log (N : ℝ)) := by positivity
  have hfinite := currentChenUpsilon8_abs_coprimeGateError_le_mass hNr hquot cap z L S N hS
  rw [max_eq_right hNr] at hfinite
  have hmass := mul_le_mul_of_nonneg_left
    (currentChenUpsilon8_liMainMass_le_linear_log hNr hquot) hfactor
  have halgebra :
      ((16 / (N : ℝ) ^ (417 / 5000 : ℝ)) * (1 + Real.log (N : ℝ))) *
        ((4 / Real.log 2) * (N : ℝ) * (1 + Real.log (N : ℝ))) =
      (64 / Real.log 2) * (N : ℝ) ^ (4583 / 5000 : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
    rw [show (4583 / 5000 : ℝ) = 1 - 417 / 5000 by norm_num,
      Real.rpow_sub hNp, Real.rpow_one]
    ring
  have hlogs : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]
  have hcost := mul_le_mul_of_nonneg_left hlogs
    (show 0 ≤ (64 / Real.log 2) * (N : ℝ) ^ (4583 / 5000 : ℝ) by positivity)
  rw [halgebra] at hmass
  calc
    _ ≤ (64 / Real.log 2) * (N : ℝ) ^ (4583 / 5000 : ℝ) *
        (1 + Real.log (N : ℝ)) ^ 2 := hfinite.trans hmass
    _ ≤ (256 / Real.log 2) * (N : ℝ) ^ (4583 / 5000 : ℝ) * Real.log (N : ℝ) ^ 2 := by
      calc
        _ ≤ (64 / Real.log 2) * (N : ℝ) ^ (4583 / 5000 : ℝ) *
            (4 * Real.log (N : ℝ) ^ 2) := hcost
        _ = _ := by ring
    _ ≤ _ := hpower

end

end ImbalancedChen
