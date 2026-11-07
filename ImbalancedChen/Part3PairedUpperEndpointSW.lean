import ImbalancedChen.Part3TransposedDispersion

/-!
# The actual paired SW estimate at upper endpoint 2U

The supplied SW constants originally apply only after a threshold in the
complete scale X=UV and use log X. This module proves a global family
estimate with the upper support endpoint T=2U and denominator log(2T).
Small X is paid by the actual finite one-bounded-alpha norm budget 4U.
The fixed auxiliary order is explicitly 2^C0. No external SW-family or
analytic-estimate import chain is added.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace PairedUpperEndpointSW

private theorem alpha_card_le_twice_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : (d.alphaCarrier.card : ℝ) ≤ 2 * d.U := by
  have hsub : d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
    intro n hn
    obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hd.1.trans (Nat.le_ceil d.U)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show (d.alphaCarrier.card : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
    exact_mod_cast hcard).trans (Nat.floor_le (by linarith [hd.1]))

private theorem alpha_sum_ite_norm_le_card
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (p : ℕ → Prop) :
    ‖∑ n ∈ d.alphaCarrier, if p n then d.alpha n else 0‖ ≤ (d.alphaCarrier.card : ℝ) := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier, ‖if p n then d.alpha n else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ d.alphaCarrier, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      split_ifs
      · exact hAlpha n hn
      · norm_num
    _ = _ := by simp

theorem auxSWError_norm_le_four_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k q b : ℕ) :
    ‖d.auxSWError k q b‖ ≤ 4 * d.U := by
  have hfirst := alpha_sum_ite_norm_le_card hd
    (fun n ↦ Nat.ModEq q n b ∧ Nat.Coprime n k)
  have hsecond := alpha_sum_ite_norm_le_card hd (fun n ↦ Nat.Coprime n (k * q))
  have hmean : ‖(∑ n ∈ d.alphaCarrier,
      if Nat.Coprime n (k * q) then d.alpha n else 0) / (Nat.totient q : ℂ)‖ ≤
        (d.alphaCarrier.card : ℝ) := by
    by_cases hphi : q.totient = 0
    · simp only [hphi, Nat.cast_zero, div_zero, norm_zero]
      positivity
    · have hphiR : (1 : ℝ) ≤ q.totient := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hphi
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_self (norm_nonneg _) hphiR).trans hsecond
  calc
    _ ≤ ‖∑ n ∈ d.alphaCarrier,
        if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0‖ +
        ‖(∑ n ∈ d.alphaCarrier,
          if Nat.Coprime n (k * q) then d.alpha n else 0) / (Nat.totient q : ℂ)‖ :=
      norm_sub_le _ _
    _ ≤ (d.alphaCarrier.card : ℝ) + (d.alphaCarrier.card : ℝ) := add_le_add hfirst hmean
    _ ≤ _ := by linarith [alpha_card_le_twice_U hd]

private theorem aux_tau_bound (C0 : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (k.divisors.card : ℝ) ^ C0 ≤ (fouvryTau (2 ^ C0) k : ℝ) := by
  rw [← fouvryTau_two]
  exact_mod_cast fouvryTau_pow_le 2 C0 (by omega : k ≠ 0)

private theorem one_le_aux_tau (C0 : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) ≤ fouvryTau (2 ^ C0) k := by
  have hcard : 1 ≤ k.divisors.card := Finset.one_le_card.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, by omega⟩⟩
  have hp : (1 : ℝ) ≤ (k.divisors.card : ℝ) ^ C0 := by
    exact_mod_cast Nat.one_le_pow C0 _ hcard
  exact hp.trans (aux_tau_bound C0 hk)

end PairedUpperEndpointSW

/-- Global, family-uniform SW on the actual paired coefficient of the new
transposed W. The constant precedes every atom and arithmetic parameter.
This complex estimate dominates either real component required externally. -/
theorem uniformAuxiliarySW_transposedPaired_upperEndpoint
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i : ι, ∀ k q b : ℕ,
      1 ≤ k → 1 ≤ q → Nat.Coprime b q →
      ‖(F i).transposedPairedSWError k q b‖ ≤
        C * (2 * (F i).U) * (fouvryTau (2 ^ C0) k : ℝ) /
          Real.log (4 * (F i).U) ^ N := by
  intro N
  obtain ⟨C, hC, x0, _hx0, hbound⟩ := hSW ((N + 1 : ℕ) : ℝ) (by positivity)
  let K : ℝ := max x0 (Real.exp 1)
  have hKexp : Real.exp 1 ≤ K := le_max_right _ _
  have hK1 : 1 < K := (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hKexp
  have hlogK : 0 < Real.log (4 * K) := Real.log_pos (by linarith)
  let C' : ℝ := C * 4 ^ N + 2 * Real.log (4 * K) ^ N + 1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hC1 : C * 4 ^ N ≤ C' := by
    dsimp [C']
    have hnonneg : 0 ≤ 2 * Real.log (4 * K) ^ N + 1 := by positivity
    linarith
  have hC2 : 2 * Real.log (4 * K) ^ N ≤ C' := by
    dsimp [C']
    have hnonneg : 0 ≤ C * 4 ^ N := by positivity
    linarith
  refine ⟨C', hC', ?_⟩
  intro i k q b hk hq hb
  rw [(F i).transposedPairedSWError_eq_auxSWError]
  have hd := hadmissible i
  have hU : 1 ≤ (F i).U := hd.1
  have hV : 1 ≤ (F i).V := hd.2.1
  have hU0 : 0 ≤ (F i).U := by linarith
  have hUpos : 0 < (F i).U := by linarith
  have hUx : (F i).U ≤ (F i).scale := by
    unfold MediumAtom.scale
    nlinarith
  have hlog4U : 0 < Real.log (4 * (F i).U) := Real.log_pos (by linarith)
  have hden : 0 < Real.log (4 * (F i).U) ^ N := pow_pos hlog4U N
  have htau : 0 ≤ (fouvryTau (2 ^ C0) k : ℝ) := Nat.cast_nonneg _
  by_cases hlarge : K ≤ (F i).scale
  · have hx0i : x0 ≤ (F i).scale := (le_max_left _ _).trans hlarge
    have hlogx : 1 ≤ Real.log (F i).scale := by
      have h := Real.log_le_log (Real.exp_pos 1) (hKexp.trans hlarge)
      simpa only [Real.log_exp] using h
    have hlogxpos : 0 < Real.log (F i).scale := zero_lt_one.trans_le hlogx
    have hraw := hbound i hx0i k q b hk hq hb
    rw [Real.rpow_natCast] at hraw
    have hnum : C * (F i).U * (k.divisors.card : ℝ) ^ C0 ≤
        C * (F i).U * (fouvryTau (2 ^ C0) k : ℝ) :=
      mul_le_mul_of_nonneg_left (PairedUpperEndpointSW.aux_tau_bound C0 hk) (by positivity)
    have hraw' : ‖(F i).auxSWError k q b‖ ≤
        C * (F i).U * (fouvryTau (2 ^ C0) k : ℝ) / Real.log (F i).scale ^ (N + 1) :=
      hraw.trans (div_le_div_of_nonneg_right hnum (by positivity))
    have hlog4 : Real.log 4 ≤ 3 := by
      simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    have hlogU := Real.log_le_log hUpos hUx
    have hlogs : Real.log (4 * (F i).U) ≤ 4 * Real.log (F i).scale := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hUpos.ne']
      linarith
    have hpN : Real.log (F i).scale ^ N ≤ Real.log (F i).scale ^ (N + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hlogxpos.le N]
    have hp : Real.log (4 * (F i).U) ^ N ≤
        4 ^ N * Real.log (F i).scale ^ (N + 1) := by
      calc
        _ ≤ (4 * Real.log (F i).scale) ^ N := pow_le_pow_left₀ hlog4U.le hlogs N
        _ = 4 ^ N * Real.log (F i).scale ^ N := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hpN (by positivity)
    have hpayment : C * (F i).U * (fouvryTau (2 ^ C0) k : ℝ) /
        Real.log (F i).scale ^ (N + 1) ≤
          (C * 4 ^ N) * (2 * (F i).U) * (fouvryTau (2 ^ C0) k : ℝ) /
            Real.log (4 * (F i).U) ^ N := by
      apply (div_le_div_iff₀ (pow_pos hlogxpos _) hden).mpr
      calc
        _ ≤ (C * (F i).U * (fouvryTau (2 ^ C0) k : ℝ)) *
            (4 ^ N * Real.log (F i).scale ^ (N + 1)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ ≤ _ := by
          have hz : 0 ≤ C * 4 ^ N * (F i).U * (fouvryTau (2 ^ C0) k : ℝ) *
              Real.log (F i).scale ^ (N + 1) := by positivity
          nlinarith
    apply (hraw'.trans hpayment).trans
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC1 (by positivity)) htau
  · have hsmall : (F i).U ≤ K := hUx.trans (le_of_lt (lt_of_not_ge hlarge))
    have hlogsmall : Real.log (4 * (F i).U) ≤ Real.log (4 * K) :=
      Real.log_le_log (by positivity) (by linarith)
    have hp : Real.log (4 * (F i).U) ^ N ≤ Real.log (4 * K) ^ N :=
      pow_le_pow_left₀ hlog4U.le hlogsmall N
    have htau1 := PairedUpperEndpointSW.one_le_aux_tau C0 hk
    have hpayment : 4 * (F i).U ≤
        (2 * Real.log (4 * K) ^ N) * (2 * (F i).U) *
          (fouvryTau (2 ^ C0) k : ℝ) / Real.log (4 * (F i).U) ^ N := by
      apply (le_div_iff₀ hden).mpr
      calc
        _ ≤ 4 * (F i).U * Real.log (4 * K) ^ N :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = (2 * Real.log (4 * K) ^ N) * (2 * (F i).U) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left htau1 (by positivity)
    apply ((PairedUpperEndpointSW.auxSWError_norm_le_four_U hd k q b).trans hpayment).trans
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 (by positivity)) htau

end

end ImbalancedChen.Part3
