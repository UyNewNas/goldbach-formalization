import ImbalancedChen.CurrentChenP5U9OrderedPhysicalPP
import ImbalancedChen.P5zUpsilon9SourceMass
import ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget

/-!
# Elementary payment of the actual marked U9 coprimality correction

SOURCE ONLY / UNCOMPILED. The first two imports are source-only candidates.
Each actual source label has three prime factors at least N^(19/125).
The installed reciprocal-totient divisor estimate charges noncoprime d
to one of these primes, with no squarefree assumption on d or the source.

The complete signed correction is reindexed before taking its absolute
value. For a fixed M>=0 and |rho(d)|<=M its finite cost is at most
  M*(24/N^(19/125))*(1+log(max 1 Q))*card(T)
for every literal subfamily T of the actual marked source. The sibling's
unconditional source-mass theorem then pays it on every fixed power-modulus
scope Q<=N^nu. No correction, distribution, density or adopted-K estimate
is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

private theorem p5z_u9_prime_reciprocal_phi_le
    {p : ℕ} (hp : Nat.Prime p) {H : ℝ} (hH : 0 < H) (hHp : H ≤ (p : ℝ)) :
    1 / ((p : ℝ) - 1) ≤ 2 / H := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hh : H / 2 ≤ (p : ℝ) - 1 := by linarith only [hHp, hp2]
  calc
    _ ≤ 1 / (H / 2) := one_div_le_one_div_of_le (half_pos hH) hh
    _ = _ := by field_simp [hH.ne']

/-- The actual pair-product budget costs sixteen; the actual third prime
costs eight. Both are proved divisor/totient budgets on the same moduli. -/
theorem p5z_u9_noncoprime_product_reciprocalTotient_sum_le
    {N : ℕ} {t : P5zU9Triple} (hN : (1 : ℝ) ≤ N)
    (ht : t ∈ p5z_u9_switchedLabels N) (D : Finset ℕ) (Q : ℕ)
    (hD : D ⊆ Finset.Icc 1 Q) :
    (∑ d ∈ D, if Nat.Coprime (p5z_u9_product t) d then (0 : ℝ)
      else 1 / (Nat.totient d : ℝ)) ≤
      (24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) := by
  have hd := p5z_u9_order_source_data ht
  have hqprime : Nat.Prime t.2 := hd.2.2.1
  have hqlo : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (t.2 : ℝ) := by
    simpa [p5z_u9_orderedNat] using
      p5z_u9_orderedNat_lower_power (0 : Fin 3) hN ht (0 : Fin 3)
  have hH : 0 < (N : ℝ) ^ (19 / 125 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _
  have hL : 0 ≤ 1 + Real.log (max 1 (Q : ℝ)) := by
    have hlog := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith only [hlog]
  have hpoint : ∀ d ∈ D,
      (if Nat.Coprime (p5z_u9_product t) d then (0 : ℝ)
        else 1 / (Nat.totient d : ℝ)) ≤
      (if Nat.Coprime (t.1.1 * t.1.2) d then 0 else 1 / (Nat.totient d : ℝ)) +
        (if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := by
    intro d _hd
    by_cases hc : Nat.Coprime (p5z_u9_product t) d
    · rw [if_pos hc]
      positivity
    · have hbad : ¬ Nat.Coprime (t.1.1 * t.1.2) d ∨ t.2 ∣ d := by
        by_cases ha : Nat.Coprime (t.1.1 * t.1.2) d
        · right
          by_contra hnq
          exact hc (Nat.coprime_mul_iff_left.mpr
            ⟨ha, hqprime.coprime_iff_not_dvd.mpr hnq⟩)
        · exact Or.inl ha
      rw [if_neg hc]
      rcases hbad with ha | hq
      · rw [if_neg ha]
        have hrest : 0 ≤ (if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := by
          positivity
        linarith only [hrest]
      · rw [if_pos hq]
        have hrest : 0 ≤ (if Nat.Coprime (t.1.1 * t.1.2) d then (0 : ℝ)
            else 1 / (Nat.totient d : ℝ)) := by positivity
        linarith only [hrest]
  have hpair := currentChenUpsilon9_noncoprime_reciprocalTotient_sum_le
    hN (p5z_u9_order_pair_product_mem ht) D Q hD
  have hq := currentChenUpsilon9_dvd_reciprocalTotient_sum_le D Q t.2 hqprime hD
  have hqinv := p5z_u9_prime_reciprocal_phi_le hqprime hH hqlo
  have hqbudget : (∑ d ∈ D, if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) ≤
      (8 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) := by
    apply hq.trans
    calc
      _ = 4 * ((1 / ((t.2 : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ)))) := by ring
      _ ≤ 4 * ((2 / (N : ℝ) ^ (19 / 125 : ℝ)) *
          (1 + Real.log (max 1 (Q : ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqinv hL) (by norm_num)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  calc
    _ ≤ (∑ d ∈ D, if Nat.Coprime (t.1.1 * t.1.2) d then (0 : ℝ)
          else 1 / (Nat.totient d : ℝ)) +
        (∑ d ∈ D, if t.2 ∣ d then 1 / (Nat.totient d : ℝ) else 0) := hsum
    _ ≤ (16 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) +
        (8 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) :=
      add_le_add hpair hqbudget
    _ = _ := by ring

/-- Exact finite Fubini for the SAME signed rho on literal marked labels.
The correction is the negative noncoprime divisor mass before absolute values. -/
theorem p5z_u9_labelledCoprimeCorrection_eq_neg_sum
    (T : Finset P5zU9Triple) (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho =
      -(∑ t ∈ T, ∑ d ∈ D, rho d *
        (if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ))) := by
  unfold p5z_labelledCoprimeCorrection p5z_labelledCoprimeMass p5z_labelledMass
  simp only [← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ T, ∑ d ∈ D, -(rho d *
        (if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ))) := by
      apply Finset.sum_congr rfl
      intro t _ht
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hc : Nat.Coprime (p5z_u9_product t) d <;>
        simp only [hc, if_true, if_false] <;> ring
    _ = _ := by simp only [Finset.sum_neg_distrib]

/-- Unconditional finite payment for every actual marked subfamily. The
only coefficient premise is |rho(d)|<=1 on the actual positive moduli. -/
theorem p5z_u9_abs_labelledCoprimeCorrection_le_mass
    {N : ℕ} (hN : (1 : ℝ) ≤ N) (T : Finset P5zU9Triple)
    (hT : T ⊆ p5z_u9_switchedLabels N) (D : Finset ℕ) (Q : ℕ)
    (hD : D ⊆ Finset.Icc 1 Q) (rho : ℕ → ℝ) (hrho : ∀ d ∈ D, |rho d| ≤ 1) :
    |p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho| ≤
      ((24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) *
        (T.card : ℝ) := by
  rw [p5z_u9_labelledCoprimeCorrection_eq_neg_sum, abs_neg]
  calc
    _ ≤ ∑ t ∈ T, |∑ d ∈ D, rho d *
        (if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ T, ∑ d ∈ D,
        if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum
      intro t _ht
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      have hterm : 0 ≤ (if Nat.Coprime (p5z_u9_product t) d then (0 : ℝ)
          else 1 / (Nat.totient d : ℝ)) := by positivity
      rw [abs_mul, abs_of_nonneg hterm]
      exact mul_le_of_le_one_left hterm (hrho d hd)
    _ ≤ ∑ _t ∈ T,
        (24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ))) :=
      Finset.sum_le_sum (fun t ht =>
        p5z_u9_noncoprime_product_reciprocalTotient_sum_le hN (hT ht) D Q hD)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A fixed signed-coefficient bound M is retained quantitatively. This
does not borrow the literal raw builder's bound one for another rho. -/
theorem p5z_u9_abs_labelledCoprimeCorrection_le_scaled_mass
    {N : ℕ} (hN : (1 : ℝ) ≤ N) (T : Finset P5zU9Triple)
    (hT : T ⊆ p5z_u9_switchedLabels N) (D : Finset ℕ) (Q : ℕ)
    (hD : D ⊆ Finset.Icc 1 Q) (rho : ℕ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hrho : ∀ d ∈ D, |rho d| ≤ M) :
    |p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho| ≤
      M * ((24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) *
        (T.card : ℝ) := by
  rw [p5z_u9_labelledCoprimeCorrection_eq_neg_sum, abs_neg]
  calc
    _ ≤ ∑ t ∈ T, |∑ d ∈ D, rho d *
        (if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ T, ∑ d ∈ D, M *
        (if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ)) := by
      apply Finset.sum_le_sum
      intro t _ht
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro d hd
      have hterm : 0 ≤ (if Nat.Coprime (p5z_u9_product t) d then (0 : ℝ)
          else 1 / (Nat.totient d : ℝ)) := by positivity
      rw [abs_mul, abs_of_nonneg hterm]
      exact mul_le_mul_of_nonneg_right (hrho d hd) hterm
    _ = M * (∑ t ∈ T, ∑ d ∈ D,
        if Nat.Coprime (p5z_u9_product t) d then 0 else 1 / (Nat.totient d : ℝ)) := by
      simp only [Finset.mul_sum]
    _ ≤ M * (∑ _t ∈ T,
        (24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact Finset.sum_le_sum (fun t ht =>
        p5z_u9_noncoprime_product_reciprocalTotient_sum_le hN (hT ht) D Q hD)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem p5z_u9_coprimeCorrection_const_mul_rho
    (T : Finset P5zU9Triple) (D : Finset ℕ) (rho : ℕ → ℝ) (c : ℝ) :
    p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D (fun d => c * rho d) =
      c * p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho := by
  unfold p5z_labelledCoprimeCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  ring

/-- One threshold precedes every literal source subfamily, every finite
modulus carrier, and every signed rho. The only scope restrictions are the
actual positive moduli through a fixed power of N and |rho|<=1. -/
theorem eventually_p5z_u9_abs_coprimeCorrection_le_singularNormalization
    (nu : ℝ) (hnu : 0 ≤ nu) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : Finset P5zU9Triple,
      T ⊆ p5z_u9_switchedLabels N → ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho| ≤
        ε * singularNormalization N := by
  let J := currentChenUpsilon9HarmonicIntegral
  let c := 24 * (nu + 1) * (J + 1)
  have hJ : 0 ≤ J := p5z_u9_HarmonicIntegral_nonneg
  have hpower := eventually_powerLog_le_singularNormalization
    c (106 / 125) 0 (by norm_num) ε hε
  have hmass := p5z_eventually_u9_switchedLabels_mass_le_harmonicIntegral 1 (by norm_num)
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpower, hmass, hlog, eventually_ge_atTop (2 : ℕ)]
    with N hpower hmass hlog hN
  intro T hT D Q rho hD hQ hrho
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hH : 0 < (N : ℝ) ^ (19 / 125 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hmax : max (1 : ℝ) (Q : ℝ) ≤ (N : ℝ) ^ nu :=
    max_le (Real.one_le_rpow hNr.le hnu) hQ
  have hmaxpos : (0 : ℝ) < max 1 (Q : ℝ) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ nu * Real.log (N : ℝ) := by
    have h := Real.log_le_log hmaxpos hmax
    rwa [Real.log_rpow hNp] at h
  have hL : 1 + Real.log (max 1 (Q : ℝ)) ≤ (nu + 1) * Real.log (N : ℝ) := by
    nlinarith only [hlogQ, hlog]
  have hcard : (T.card : ℝ) ≤ (J + 1) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have hsub : (T.card : ℝ) ≤ ((p5z_u9_switchedLabels N).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hT
    exact hsub.trans hmass
  have hfinite := p5z_u9_abs_labelledCoprimeCorrection_le_mass
    hNr.le T hT D Q hD rho hrho
  have hpaid :
      ((24 / (N : ℝ) ^ (19 / 125 : ℝ)) * (1 + Real.log (max 1 (Q : ℝ)))) * (T.card : ℝ) ≤
        ((24 / (N : ℝ) ^ (19 / 125 : ℝ)) * ((nu + 1) * Real.log (N : ℝ))) *
          ((J + 1) * ((N : ℝ) / Real.log (N : ℝ))) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hL (by positivity)
    · exact hcard
    · exact Nat.cast_nonneg _
    · positivity
  have halgebra :
      ((24 / (N : ℝ) ^ (19 / 125 : ℝ)) * ((nu + 1) * Real.log (N : ℝ))) *
          ((J + 1) * ((N : ℝ) / Real.log (N : ℝ))) = c * (N : ℝ) ^ (106 / 125 : ℝ) := by
    dsimp only [c]
    rw [show (106 / 125 : ℝ) = 1 - 19 / 125 by norm_num,
      Real.rpow_sub hNp, Real.rpow_one]
    field_simp [hH.ne', hlogpos.ne'] <;> ring
  rw [halgebra] at hpaid
  apply (hfinite.trans hpaid).trans
  simpa only [pow_zero, mul_one] using hpower

/-- Fixed M>=0 is allowed uniformly. Normalizing by M+1 also covers M=0
without division by a possibly vanishing coefficient bound. -/
theorem eventually_p5z_u9_abs_coprimeCorrection_of_abs_le
    (nu : ℝ) (hnu : 0 ≤ nu) (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ T : Finset P5zU9Triple,
      T ⊆ p5z_u9_switchedLabels N → ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
      (∀ d ∈ D, |rho d| ≤ M) →
      |p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho| ≤
        ε * singularNormalization N := by
  have hMp : 0 < M + 1 := by linarith only [hM]
  let delta := ε / (M + 1)
  have hdelta : 0 < delta := div_pos hε hMp
  filter_upwards [eventually_p5z_u9_abs_coprimeCorrection_le_singularNormalization
    nu hnu delta hdelta] with N hN
  intro T hT D Q rho hD hQ hrho
  let sigma := fun d : ℕ => rho d / (M + 1)
  have hsigma : ∀ d ∈ D, |sigma d| ≤ 1 := by
    intro d hd
    dsimp only [sigma]
    rw [abs_div, abs_of_pos hMp, div_le_one hMp]
    exact (hrho d hd).trans (by linarith)
  have hbound := hN T hT D Q sigma hD hQ hsigma
  have hrhoeq : rho = fun d => (M + 1) * sigma d := by
    funext d
    dsimp only [sigma]
    field_simp [hMp.ne'] <;> ring
  have hid : p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D rho =
      (M + 1) * p5z_labelledCoprimeCorrection T p5z_u9_product (fun _ => 1) D sigma := by
    rw [hrhoeq, p5z_u9_coprimeCorrection_const_mul_rho]
  rw [hid, abs_mul, abs_of_pos hMp]
  calc
    _ ≤ (M + 1) * (delta * singularNormalization N) :=
      mul_le_mul_of_nonneg_left hbound hMp.le
    _ = ε * singularNormalization N := by
      dsimp only [delta]
      field_simp [hMp.ne'] <;> ring

/-- The full source is the actual same-rho correction in the U9 finite bridge. -/
theorem eventually_p5z_u9_full_coprimeCorrection_le_singularNormalization
    (nu : ℝ) (hnu : 0 ≤ nu) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) D rho| ≤ ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_abs_coprimeCorrection_le_singularNormalization nu hnu ε hε]
    with N hN
  intro D Q rho hD hQ hrho
  exact hN _ (fun _ ht => ht) D Q rho hD hQ hrho

/-- The original multiplicity weight receives exactly the same payment. -/
theorem eventually_p5z_u9_productWeight_coprimeCorrection_le_singularNormalization
    (nu : ℝ) (hnu : 0 ≤ nu) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N) D rho| ≤
        ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_full_coprimeCorrection_le_singularNormalization nu hnu ε hε]
    with N hN
  intro D Q rho hD hQ hrho
  rw [p5z_u9_switched_correction_eq_labels]
  exact hN D Q rho hD hQ hrho

/-- Direct physical-scope form: no auxiliary natural cutoff need be
provided by the caller. The exact floor is constructed inside the proof. -/
theorem eventually_p5z_u9_productWeight_correction_of_real_modulus_scope
    (nu : ℝ) (hnu : 0 ≤ nu) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, ∀ rho : ℕ → ℝ,
      (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ nu) →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N) D rho| ≤
        ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_productWeight_coprimeCorrection_le_singularNormalization
    nu hnu ε hε] with N hN
  intro D rho hD hrho
  apply hN D (Nat.floor ((N : ℝ) ^ nu)) rho _
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hrho
  intro d hd
  exact Finset.mem_Icc.mpr ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩

/-- Assembly-ready fixed-M version on the original product-fibre weight. -/
theorem eventually_p5z_u9_productWeight_correction_of_real_scope_abs_le
    (nu : ℝ) (hnu : 0 ≤ nu) (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : Finset ℕ, ∀ rho : ℕ → ℝ,
      (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ nu) →
      (∀ d ∈ D, |rho d| ≤ M) →
      |p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N) D rho| ≤
        ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_abs_coprimeCorrection_of_abs_le nu hnu M hM ε hε]
    with N hN
  intro D rho hD hrho
  rw [p5z_u9_switched_correction_eq_labels]
  apply hN _ (fun _ ht => ht) D (Nat.floor ((N : ℝ) ^ nu)) rho _
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hrho
  intro d hd
  exact Finset.mem_Icc.mpr ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩

theorem p5z_u9_orderedPhysical_mass_eq (j : Fin 3) (N : ℕ) :
    p5z_labelledMass (p5z_u9_orderBranch j N) (fun _ => 1) =
      p5z_labelledMass (Part3.labelledPrimeTuples 3 N) (p5z_u9_orderedPhysicalWeight j N) := by
  simpa only [p5z_labelledMass, mul_one] using
    p5z_u9_orderedPhysicalWeight_sum j N (fun _ => 1)

theorem p5z_u9_orderedPhysical_correction_eq (j : Fin 3) (N : ℕ)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledCoprimeCorrection (p5z_u9_orderBranch j N) p5z_u9_product (fun _ => 1) D rho =
      p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) D rho := by
  unfold p5z_labelledCoprimeCorrection
  simp_rw [p5z_u9_orderedPhysical_coprimeMass, p5z_u9_orderedPhysical_mass_eq]

/-- The same threshold also covers all three concrete physical branch
coefficients, without a new family-dependent correction premise. -/
theorem eventually_p5z_u9_orderedPhysical_correction_le_singularNormalization
    (nu : ℝ) (hnu : 0 ≤ nu) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin 3, ∀ D : Finset ℕ, ∀ Q : ℕ, ∀ rho : ℕ → ℝ,
      D ⊆ Finset.Icc 1 Q → (Q : ℝ) ≤ (N : ℝ) ^ nu →
      (∀ d ∈ D, |rho d| ≤ 1) →
      |p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) D rho| ≤ ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_abs_coprimeCorrection_le_singularNormalization nu hnu ε hε]
    with N hN
  intro j D Q rho hD hQ hrho
  rw [← p5z_u9_orderedPhysical_correction_eq]
  apply hN (p5z_u9_orderBranch j N) _ D Q rho hD hQ hrho
  intro t ht
  exact (Finset.mem_filter.mp ht).1

/-- All three physical branch coefficients also allow any fixed actual
bound M on rho, with the same threshold and original physical scope. -/
theorem eventually_p5z_u9_orderedPhysical_correction_of_real_scope_abs_le
    (nu : ℝ) (hnu : 0 ≤ nu) (M : ℝ) (hM : 0 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin 3, ∀ D : Finset ℕ, ∀ rho : ℕ → ℝ,
      (∀ d ∈ D, 1 ≤ d ∧ (d : ℝ) ≤ (N : ℝ) ^ nu) →
      (∀ d ∈ D, |rho d| ≤ M) →
      |p5z_labelledCoprimeCorrection (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) D rho| ≤ ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_abs_coprimeCorrection_of_abs_le nu hnu M hM ε hε]
    with N hN
  intro j D rho hD hrho
  rw [← p5z_u9_orderedPhysical_correction_eq]
  apply hN _ _ D (Nat.floor ((N : ℝ) ^ nu)) rho _
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hrho
  · intro t ht
    exact (Finset.mem_filter.mp ht).1
  · intro d hd
    exact Finset.mem_Icc.mpr ⟨(hD d hd).1, Nat.le_floor (hD d hd).2⟩

end

end ImbalancedChen
