import ImbalancedChen.Part3TransposedDispersion

/-!
# The actual transposed zero mode and its original-alpha covariance

All scales and coefficients below come from one original MediumAtom.
The common scalar is original V times the local Fourier-zero cutoffMass.
No equality with an external integral normalization is presumed.

The finite reduced-class algebra is adapted to complex coefficients and
conjugation from fixed goldbach 09b97db5764ade1246bfb77206baa1b124760958,
LiLiuPrereqFouvryBetaCovariance.lean. No module from its unbuilt smoothing
or zero-mode import chain is imported here. The lcm harmonic supplier is
the already reachable narrow LcmWeightBounds module, whose only direct
supplier is the existing DivisorMean module.

The primitive zero main term is defined by the actual coprime mass and
totient density. It is not identified with literal smoothed V or U.
Those two differences remain explicit in the centered-energy identity.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace TransposedZeroCovariance

def reducedResidues (delta : ℕ) : Finset ℕ :=
  (Finset.range delta).filter (fun b ↦ b.Coprime delta)

theorem card_reducedResidues (delta : ℕ) :
    (reducedResidues delta).card = delta.totient := by
  simp only [reducedResidues, Nat.totient_eq_card_coprime, Nat.coprime_comm]

def coprimeMass {R : Type*} [AddCommMonoid R]
    (N : Finset ℕ) (beta : ℕ → R) (q : ℕ) : R :=
  ∑ n ∈ N, if n.Coprime q then beta n else 0

def residueMass {R : Type*} [AddCommMonoid R]
    (N : Finset ℕ) (beta : ℕ → R) (q delta b : ℕ) : R :=
  ∑ n ∈ N, if n.Coprime q ∧ Nat.ModEq delta n b then beta n else 0

private theorem sum_reduced_indicator {R : Type*} [AddCommMonoid R]
    {delta n : ℕ} (hdelta : 0 < delta) (hn : n.Coprime delta) (z : R) :
    (∑ b ∈ reducedResidues delta, if Nat.ModEq delta n b then z else 0) = z := by
  have hm : n % delta ∈ reducedResidues delta := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hdelta), ?_⟩
    change (n % delta).gcd delta = 1
    rw [(Nat.mod_modEq n delta).gcd_eq, hn.gcd_eq_one]
  rw [Finset.sum_eq_single (n % delta)]
  · simp [Nat.ModEq]
  · intro b hb hne
    apply if_neg
    intro he
    have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have he' : n % delta = b := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hb'] using he
    exact hne he'.symm
  · exact fun h ↦ (h hm).elim

theorem sum_residueMass {R : Type*} [AddCommMonoid R]
    (N : Finset ℕ) (beta : ℕ → R) {q delta : ℕ}
    (hdelta : 0 < delta) (hdq : delta ∣ q) :
    (∑ b ∈ reducedResidues delta, residueMass N beta q delta b) =
      coprimeMass N beta q := by
  unfold residueMass coprimeMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Coprime q
  · have hn' := hn
    simp only [Nat.Coprime] at hn ⊢
    simp only [hn, true_and, if_true]
    exact sum_reduced_indicator hdelta (hn'.of_dvd_right hdq) _
  · simp [hn]

private theorem pair_indicator {q r n₁ n₂ : ℕ} (hq : 0 < q) (z₁ z₂ : ℂ) :
    (∑ b ∈ reducedResidues (q.gcd r),
      (if n₁.Coprime q ∧ Nat.ModEq (q.gcd r) n₁ b then z₁ else 0) *
        star (if n₂.Coprime r ∧ Nat.ModEq (q.gcd r) n₂ b then z₂ else 0)) =
      if ComplexCRT.Compatible q r n₁ n₂ then z₁ * star z₂ else 0 := by
  by_cases h₁ : n₁.Coprime q
  · by_cases h₂ : n₂.Coprime r
    · have h₁' := h₁
      simp only [Nat.Coprime] at h₁ h₂
      simp only [ComplexCRT.Compatible, Nat.Coprime, h₁, h₂, true_and]
      by_cases hc : Nat.ModEq (q.gcd r) n₁ n₂
      · rw [if_pos hc]
        have he (b : ℕ) :
            Nat.ModEq (q.gcd r) n₁ b ↔ Nat.ModEq (q.gcd r) n₂ b :=
          ⟨fun h ↦ hc.symm.trans h, fun h ↦ hc.trans h⟩
        simp_rw [← he]
        have hterm (b : ℕ) :
            (if Nat.ModEq (q.gcd r) n₁ b then z₁ else 0) *
              star (if Nat.ModEq (q.gcd r) n₁ b then z₂ else 0) =
            if Nat.ModEq (q.gcd r) n₁ b then z₁ * star z₂ else 0 := by
          by_cases hb : Nat.ModEq (q.gcd r) n₁ b <;> simp [hb]
        simp_rw [hterm]
        exact sum_reduced_indicator (Nat.gcd_pos_of_pos_left r hq)
          (h₁'.of_dvd_right (Nat.gcd_dvd_left q r)) _
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro b _
        by_cases hb : Nat.ModEq (q.gcd r) n₁ b
        · have hb' : ¬Nat.ModEq (q.gcd r) n₂ b := fun h ↦ hc (hb.trans h.symm)
          simp [hb']
        · simp [hb]
    · simp [h₂, ComplexCRT.Compatible]
  · simp [h₁, ComplexCRT.Compatible]

def compatibleMass (N : Finset ℕ) (beta : ℕ → ℂ) (q r : ℕ) : ℂ :=
  ∑ n₁ ∈ N, ∑ n₂ ∈ N,
    if ComplexCRT.Compatible q r n₁ n₂ then beta n₁ * star (beta n₂) else 0

theorem compatibleMass_eq_residue_products (N : Finset ℕ) (beta : ℕ → ℂ)
    {q r : ℕ} (hq : 0 < q) :
    compatibleMass N beta q r =
      ∑ b ∈ reducedResidues (q.gcd r),
        residueMass N beta q (q.gcd r) b * star (residueMass N beta r (q.gcd r) b) := by
  unfold compatibleMass residueMass
  simp only [star_sum, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₂ _
  exact (pair_indicator hq (beta n₁) (beta n₂)).symm

def covariance (N : Finset ℕ) (beta : ℕ → ℂ) (q r : ℕ) : ℂ :=
  ∑ b ∈ reducedResidues (q.gcd r),
    (residueMass N beta q (q.gcd r) b - coprimeMass N beta q / ((q.gcd r).totient : ℂ)) *
      star (residueMass N beta r (q.gcd r) b -
        coprimeMass N beta r / ((q.gcd r).totient : ℂ))

theorem covariance_identity (N : Finset ℕ) (beta : ℕ → ℂ) {q r : ℕ} (hq : 0 < q) :
    compatibleMass N beta q r -
      coprimeMass N beta q * star (coprimeMass N beta r) / ((q.gcd r).totient : ℂ) =
        covariance N beta q r := by
  have hdelta := Nat.gcd_pos_of_pos_left r hq
  have hphi : ((q.gcd r).totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hdelta).ne'
  rw [compatibleMass_eq_residue_products N beta hq]
  unfold covariance
  simp only [star_sub, star_div₀, star_natCast, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← star_sum, Finset.sum_const, nsmul_eq_mul, card_reducedResidues,
    sum_residueMass N beta hdelta (Nat.gcd_dvd_left q r),
    sum_residueMass N beta hdelta (Nat.gcd_dvd_right q r)]
  field_simp
  ring

theorem totient_pair_density_eq_lcm {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
    ((q * r).totient : ℂ) /
      ((q.totient : ℂ) * (r.totient : ℂ) * (q * r : ℕ)) =
        1 / ((q.lcm r : ℂ) * ((q.gcd r).totient : ℂ)) := by
  have hphiq : (q.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have hphir : (r.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr)).ne'
  have hqr : ((q * r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (mul_ne_zero hq hr)
  have hlcm : (q.lcm r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcm_ne_zero hq hr)
  have hphidelta : ((q.gcd r).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left r (Nat.pos_of_ne_zero hq))).ne'
  have ht : ((q.gcd r).totient : ℂ) * ((q * r).totient : ℂ) =
      (q.totient : ℂ) * (r.totient : ℂ) * (q.gcd r : ℂ) := by
    exact_mod_cast Nat.totient_gcd_mul_totient_mul q r
  have hg : (q.gcd r : ℂ) * (q.lcm r : ℂ) = (q * r : ℕ) := by
    exact_mod_cast Nat.gcd_mul_lcm q r
  apply (div_eq_div_iff (mul_ne_zero (mul_ne_zero hphiq hphir) hqr)
    (mul_ne_zero hlcm hphidelta)).mpr
  calc
    _ = (((q.gcd r).totient : ℂ) * ((q * r).totient : ℂ)) * (q.lcm r : ℂ) := by ring
    _ = _ := by rw [ht, mul_assoc _ (q.gcd r : ℂ), hg, one_mul]

private theorem residueMass_norm_le (N : Finset ℕ) (beta : ℕ → ℂ) (q delta b : ℕ) :
    ‖residueMass N beta q delta b‖ ≤ residueMass N (fun n ↦ ‖beta n‖) q delta b := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  split_ifs <;> simp

private theorem coprimeMass_norm_le (N : Finset ℕ) (beta : ℕ → ℂ) (q : ℕ) :
    ‖coprimeMass N beta q‖ ≤ ∑ n ∈ N, ‖beta n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  split_ifs <;> simp

private theorem coprimeMass_of_norm_le (N : Finset ℕ) (beta : ℕ → ℂ) (q : ℕ) :
    coprimeMass N (fun n ↦ ‖beta n‖) q ≤ ∑ n ∈ N, ‖beta n‖ := by
  apply Finset.sum_le_sum
  intro n _
  split_ifs <;> simp [norm_nonneg]

theorem sum_norm_centered_mass_le (N : Finset ℕ) (beta : ℕ → ℂ)
    {q delta : ℕ} (hdelta : 0 < delta) (hdq : delta ∣ q) :
    (∑ b ∈ reducedResidues delta,
      ‖residueMass N beta q delta b - coprimeMass N beta q / (delta.totient : ℂ)‖) ≤
        2 * ∑ n ∈ N, ‖beta n‖ := by
  have hphi : (delta.totient : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hdelta).ne'
  calc
    _ ≤ ∑ b ∈ reducedResidues delta,
        (residueMass N (fun n ↦ ‖beta n‖) q delta b +
          ‖coprimeMass N beta q‖ / (delta.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro b _
      exact (norm_sub_le _ _).trans (add_le_add (residueMass_norm_le N beta q delta b)
        (by rw [norm_div, Complex.norm_natCast]))
    _ = coprimeMass N (fun n ↦ ‖beta n‖) q + ‖coprimeMass N beta q‖ := by
      rw [Finset.sum_add_distrib, sum_residueMass N _ hdelta hdq]
      simp only [Finset.sum_const, nsmul_eq_mul, card_reducedResidues]
      rw [mul_div_cancel₀ _ hphi]
    _ ≤ _ := by
      linarith [coprimeMass_of_norm_le N beta q, coprimeMass_norm_le N beta q]

theorem covariance_norm_le_lone (N : Finset ℕ) (beta : ℕ → ℂ)
    {q r : ℕ} (hq : 0 < q) {E : ℝ} (hE : 0 ≤ E)
    (hAP : ∀ b ∈ reducedResidues (q.gcd r),
      ‖residueMass N beta q (q.gcd r) b -
        coprimeMass N beta q / ((q.gcd r).totient : ℂ)‖ ≤ E) :
    ‖covariance N beta q r‖ ≤ 2 * E * ∑ n ∈ N, ‖beta n‖ := by
  unfold covariance
  calc
    _ ≤ ∑ b ∈ reducedResidues (q.gcd r), E *
        ‖residueMass N beta r (q.gcd r) b -
          coprimeMass N beta r / ((q.gcd r).totient : ℂ)‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro b hb
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hAP b hb) (norm_nonneg _)
    _ ≤ E * (2 * ∑ n ∈ N, ‖beta n‖) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_norm_centered_mass_le N beta (Nat.gcd_pos_of_pos_left r hq)
          (Nat.gcd_dvd_right q r)) hE
    _ = _ := by ring

/-- On a reduced gcd class the complete sieve q equals the quotient sieve
q/delta together with the displayed AP. This is an exact coefficient bridge. -/
theorem actual_centered_mass_eq_auxSWError (d : MediumAtom) {q delta b : ℕ}
    (hdq : delta ∣ q) (hb : b.Coprime delta) :
    residueMass d.alphaCarrier d.alpha q delta b -
      coprimeMass d.alphaCarrier d.alpha q / (delta.totient : ℂ) =
        d.auxSWError (q / delta) delta b := by
  have hsieve : delta * (q / delta) = q := Nat.mul_div_cancel' hdq
  unfold MediumAtom.auxSWError residueMass coprimeMass
  rw [show q / delta * delta = q by simpa only [mul_comm] using hsieve]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have he : (n.Coprime q ∧ Nat.ModEq delta n b) ↔
      (Nat.ModEq delta n b ∧ n.Coprime (q / delta)) := by
    constructor
    · exact fun h ↦ ⟨h.2, h.1.of_dvd_right (Nat.div_dvd_of_dvd hdq)⟩
    · rintro ⟨hc, hn⟩
      have hndelta : n.Coprime delta := by
        change n.gcd delta = 1
        rw [hc.gcd_eq, hb.gcd_eq_one]
      exact ⟨by rw [← hsieve]; exact hndelta.mul_right hn, hc⟩
  exact if_congr he rfl rfl

private theorem alpha_l1_le_twice_U
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ n ∈ d.alphaCarrier, ‖d.alpha n‖) ≤ 2 * d.U := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  have hsub : d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
    intro n hn
    obtain ⟨hn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hd.1.trans (Nat.le_ceil d.U)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  calc
    _ ≤ ∑ _n ∈ d.alphaCarrier, (1 : ℝ) := Finset.sum_le_sum hAlpha
    _ = (d.alphaCarrier.card : ℝ) := by simp
    _ ≤ (Nat.floor (2 * d.U) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := Nat.floor_le (by linarith [hd.1])

/-- Uniform SW is consumed at every actual gcd and its quotient sieve.
The saving constant and threshold precede the atom and both moduli. -/
theorem actual_covariance_SW_bound {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (sigma kappa c0 A : ℝ) (hA : 0 < A)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale → ∀ q r : ℕ, 0 < q →
        ‖covariance (F i).alphaCarrier (F i).alpha q r‖ ≤
          C * (F i).U ^ 2 * (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) /
            Real.log (F i).scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ := hSW A hA
  refine ⟨4 * C, by positivity, x0, hx0, ?_⟩
  intro i hx q r hq
  have hdelta : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hquot : 0 < q / q.gcd r :=
    Nat.div_pos (Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)) hdelta
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  have hU : 0 ≤ (F i).U := by linarith [(hadmissible i).1]
  have htau : ((q / q.gcd r).divisors.card : ℝ) ^ C0 ≤
      (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) := by
    rw [← fouvryTau_two]
    exact_mod_cast fouvryTau_pow_le 2 C0 hquot.ne'
  have hAP : ∀ b ∈ reducedResidues (q.gcd r),
      ‖residueMass (F i).alphaCarrier (F i).alpha q (q.gcd r) b -
        coprimeMass (F i).alphaCarrier (F i).alpha q / ((q.gcd r).totient : ℂ)‖ ≤
      C * (F i).U * (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) /
        Real.log (F i).scale ^ A := by
    intro b hb
    rw [actual_centered_mass_eq_auxSWError (F i) (Nat.gcd_dvd_left q r)
      (Finset.mem_filter.mp hb).2]
    exact (hbound i hx (q / q.gcd r) (q.gcd r) b (by omega) (by omega)
      (Finset.mem_filter.mp hb).2).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htau (by positivity)) (by positivity))
  have hcov := covariance_norm_le_lone (F i).alphaCarrier (F i).alpha hq
    (show 0 ≤ C * (F i).U * (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) /
      Real.log (F i).scale ^ A by positivity) hAP
  calc
    _ ≤ 2 * (C * (F i).U * (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) /
        Real.log (F i).scale ^ A) * (2 * (F i).U) :=
      hcov.trans (mul_le_mul_of_nonneg_left (alpha_l1_le_twice_U (hadmissible i))
        (by positivity))
    _ = _ := by ring

private theorem sum_transposedBeta_star_mul (d : MediumAtom) (f : ℕ → ℂ) :
    (∑ n ∈ d.transposedAtom.betaCarrier, star (d.transposedAtom.beta n) * f n) =
      ∑ n ∈ d.alphaCarrier, star (d.alpha n) * f n := by
  simpa only [star_sum, star_mul, star_star, mul_comm] using
    congrArg star (d.sum_transposedBeta_mul (fun n ↦ star (f n)))

theorem sum_transposedBeta_pairs (d : MediumAtom) (f : ℕ → ℕ → ℂ) :
    (∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
      d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) * f n₁ n₂) =
        ∑ n₁ ∈ d.alphaCarrier, ∑ n₂ ∈ d.alphaCarrier,
          d.alpha n₁ * star (d.alpha n₂) * f n₁ n₂ := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [d.sum_transposedBeta_mul]
  apply Finset.sum_congr rfl
  intro n₁ _
  rw [sum_transposedBeta_star_mul]

/-- Exact summation by physical modulus is performed before taking norms. -/
theorem factor_pair_sum_eq_grouped (d : MediumAtom) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
      d.complexFactorGamma a * star (d.complexFactorGamma b) *
        f (complexFactorModulus a) (complexFactorModulus b)) =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        d.groupedFactorGamma q * star (d.groupedFactorGamma r) * f q r := by
  have hstar (g : ℕ → ℂ) :
      (∑ a ∈ d.complexFactorLabels, star (d.complexFactorGamma a) *
        g (complexFactorModulus a)) =
      ∑ q ∈ d.physicalFactorModuli, star (d.groupedFactorGamma q) * g q := by
    simpa only [star_sum, star_mul, star_star, mul_comm] using
      congrArg star (d.sum_factorLabels_eq_grouped (fun q ↦ star (g q)))
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [d.sum_factorLabels_eq_grouped (fun q ↦
    ∑ b ∈ d.complexFactorLabels,
      star (d.complexFactorGamma b) * f q (complexFactorModulus b))]
  apply Finset.sum_congr rfl
  intro q _
  rw [hstar (fun r ↦ f q r)]

/-- The complete local Poisson zero term, with the original alpha pair
and the original full complex factor labels. No residue sign is changed. -/
theorem actual_rawZero_eq_compatibleMass (d : MediumAtom) :
    d.transposedAtom.complexCRTSmoothZeroPart =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
        ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
          d.complexFactorGamma a * star (d.complexFactorGamma b) *
            compatibleMass d.alphaCarrier d.alpha
              (complexFactorModulus a) (complexFactorModulus b) /
                ((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ) := by
  unfold MediumAtom.complexCRTSmoothZeroPart
  simp only [MediumAtom.complexRowLabels, Finset.sum_product,
    MediumAtom.complexBetaCoefficient, star_mul]
  simp_rw [Finset.sum_comm (s := d.transposedAtom.betaCarrier)
    (t := d.transposedAtom.complexFactorLabels)]
  change (∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
    ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
      d.complexFactorGamma a * d.transposedAtom.beta n₁ *
        (star (d.transposedAtom.beta n₂) * star (d.complexFactorGamma b)) *
          (if ComplexCRT.Compatible (complexFactorModulus a)
            (complexFactorModulus b) n₁ n₂ then
              ((d.V / (complexFactorModulus a).lcm (complexFactorModulus b)) *
                CommonSmoothCutoff.cutoffMass : ℝ) else 0 : ℝ)) = _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  let q := complexFactorModulus a
  let r := complexFactorModulus b
  have hp := sum_transposedBeta_pairs d (fun n₁ n₂ ↦
    if ComplexCRT.Compatible q r n₁ n₂ then (1 : ℂ) else 0)
  unfold compatibleMass
  calc
    _ = (d.complexFactorGamma a * star (d.complexFactorGamma b) *
        (((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) / (q.lcm r : ℂ))) *
        ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
          d.transposedAtom.beta n₁ * star (d.transposedAtom.beta n₂) *
            (if ComplexCRT.Compatible q r n₁ n₂ then (1 : ℂ) else 0) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      dsimp only [q, r]
      by_cases hc : ComplexCRT.Compatible
          (complexFactorModulus a) (complexFactorModulus b) n₁ n₂
      · simp only [hc, if_true, mul_one]
        push_cast
        ring
      · simp [hc]
    _ = _ := by
      rw [hp]
      simp only [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n₁ _
      apply Finset.sum_congr rfl
      intro n₂ _
      dsimp only [q, r]
      by_cases hc : ComplexCRT.Compatible
          (complexFactorModulus a) (complexFactorModulus b) n₁ n₂
      · simp only [hc, if_true, mul_one]
        ring
      · simp [hc]

/-- The actual primitive density at zero frequency. Its normalization is
the local Fourier-zero cutoffMass, not an imported integral constant. -/
def primitiveZeroMain (d : MediumAtom) : ℂ :=
  ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
    ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
      d.complexFactorGamma a * star (d.complexFactorGamma b) *
        coprimeMass d.alphaCarrier d.alpha (complexFactorModulus a) *
          star (coprimeMass d.alphaCarrier d.alpha (complexFactorModulus b)) *
            (((complexFactorModulus a * complexFactorModulus b).totient : ℂ) /
              (((complexFactorModulus a).totient : ℂ) *
                ((complexFactorModulus b).totient : ℂ) *
                  (complexFactorModulus a * complexFactorModulus b : ℕ)))

/-- Zero-mode discrepancy is exactly the original-alpha covariance,
with each original complex factor fiber retained by an exact identity. -/
theorem actual_rawZero_sub_primitive_eq_covariance
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain d =
      ((d.V * CommonSmoothCutoff.cutoffMass : ℝ) : ℂ) *
        ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
          d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
            covariance d.alphaCarrier d.alpha q r / (q.lcm r : ℂ) := by
  have hpos {a : ℕ × ℕ × ℕ} (ha : a ∈ d.complexFactorLabels) :
      0 < complexFactorModulus a := by
    exact (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
      (Finset.mem_image_of_mem _ ha))).1
  rw [actual_rawZero_eq_compatibleMass, primitiveZeroMain, ← mul_sub,
    ← Finset.sum_sub_distrib]
  have hfinite :
      (∑ a ∈ d.complexFactorLabels,
        ((∑ b ∈ d.complexFactorLabels,
          d.complexFactorGamma a * star (d.complexFactorGamma b) *
            compatibleMass d.alphaCarrier d.alpha (complexFactorModulus a)
              (complexFactorModulus b) /
                ((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ)) -
        (∑ b ∈ d.complexFactorLabels,
          d.complexFactorGamma a * star (d.complexFactorGamma b) *
            coprimeMass d.alphaCarrier d.alpha (complexFactorModulus a) *
            star (coprimeMass d.alphaCarrier d.alpha (complexFactorModulus b)) *
              (((complexFactorModulus a * complexFactorModulus b).totient : ℂ) /
                (((complexFactorModulus a).totient : ℂ) *
                  ((complexFactorModulus b).totient : ℂ) *
                    (complexFactorModulus a * complexFactorModulus b : ℕ)))))) =
      ∑ a ∈ d.complexFactorLabels, ∑ b ∈ d.complexFactorLabels,
        d.complexFactorGamma a * star (d.complexFactorGamma b) *
          (covariance d.alphaCarrier d.alpha (complexFactorModulus a)
            (complexFactorModulus b) /
              ((complexFactorModulus a).lcm (complexFactorModulus b) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [totient_pair_density_eq_lcm (hpos ha).ne' (hpos hb).ne',
      ← covariance_identity _ _ (hpos ha)]
    ring
  rw [hfinite, factor_pair_sum_eq_grouped d (fun q r ↦
    covariance d.alphaCarrier d.alpha q r / (q.lcm r : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  ring

private theorem one_le_tau_succ (k : ℕ) {q : ℕ} (hq : q ≠ 0) :
    1 ≤ fouvryTau (k + 1) q := by
  rw [fouvryTau_succ]
  calc
    1 = fouvryTau k 1 := (fouvryTau_one k).symm
    _ ≤ _ := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Nat.mem_divisors.mpr ⟨one_dvd q, hq⟩)

private theorem tau_div_le_succ (k : ℕ) {q delta : ℕ}
    (hq : q ≠ 0) (hdq : delta ∣ q) :
    fouvryTau k (q / delta) ≤ fouvryTau (k + 1) q := by
  rw [fouvryTau_succ]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdq, hq⟩)

/-- Every gcd is summed. The three original factor fibers cost tau_3;
the SW quotient sieve adds tau_(k+1), and the existing lcm second moment
pays the displayed fixed logarithm exponent. -/
theorem actual_weighted_lcm_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : ℕ) :
    (∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ / (q.lcm r : ℝ) *
        (fouvryTau k (q / q.gcd r) : ℝ)) ≤
          (1 + Real.log d.physicalFactorCap) ^ (2 * (3 * (k + 1)) ^ 2 + 1) := by
  let w : ℕ → ℝ := fun q ↦ ‖d.groupedFactorGamma q‖ * (fouvryTau (k + 1) q : ℝ)
  have hQ := d.physicalFactorModuli_subset_cap hd
  have hw (q : ℕ) (_hq : q ∈ d.physicalFactorModuli) :
      |w q| ≤ (fouvryTau (3 * (k + 1)) q : ℝ) := by
    rw [abs_of_nonneg (by dsimp [w]; positivity)]
    exact (mul_le_mul_of_nonneg_right (d.groupedFactorGamma_norm_le_tauThree hd q)
      (Nat.cast_nonneg _)).trans (by exact_mod_cast fouvryTau_mul_le 3 (k + 1) q)
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        |w q * w r / (q.lcm r : ℝ)| := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hq0 := (Finset.mem_Ioc.mp (hQ hq)).1.ne'
      have hr0 := (Finset.mem_Ioc.mp (hQ hr)).1.ne'
      have htq : (fouvryTau k (q / q.gcd r) : ℝ) ≤
          (fouvryTau (k + 1) q : ℝ) := by
        exact_mod_cast tau_div_le_succ k hq0 (Nat.gcd_dvd_left q r)
      have htr : (1 : ℝ) ≤ (fouvryTau (k + 1) r : ℝ) := by
        exact_mod_cast one_le_tau_succ k hr0
      rw [abs_of_nonneg (by dsimp [w]; positivity)]
      calc
        _ ≤ ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ /
            (q.lcm r : ℝ) * (fouvryTau (k + 1) q : ℝ) :=
          mul_le_mul_of_nonneg_left htq (by positivity)
        _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ /
            (q.lcm r : ℝ) * (fouvryTau (k + 1) q : ℝ)) *
              (fouvryTau (k + 1) r : ℝ) :=
          le_mul_of_one_le_right (by positivity) htr
        _ = _ := by dsimp [w]; ring
    _ ≤ _ :=
      MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_abs_lcm_weight_le_log
        (3 * (k + 1)) (d.one_le_physicalFactorCap hd) d.physicalFactorModuli hQ w hw

private theorem covariance_sum_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (k : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hpoint : ∀ q ∈ d.physicalFactorModuli, ∀ r ∈ d.physicalFactorModuli,
      ‖covariance d.alphaCarrier d.alpha q r‖ ≤ D * (fouvryTau k (q / q.gcd r) : ℝ)) :
    ‖∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
      d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
        covariance d.alphaCarrier d.alpha q r / (q.lcm r : ℂ)‖ ≤
          D * (1 + Real.log d.physicalFactorCap) ^ (2 * (3 * (k + 1)) ^ 2 + 1) := by
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        D * (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ /
          (q.lcm r : ℝ) * (fouvryTau k (q / q.gcd r) : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_div, norm_mul, norm_mul, norm_star, Complex.norm_natCast]
      calc
        _ ≤ (‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ *
            (D * (fouvryTau k (q / q.gcd r) : ℝ))) / (q.lcm r : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpoint q hq r hr) (by positivity))
            (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = D * ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        ‖d.groupedFactorGamma q‖ * ‖d.groupedFactorGamma r‖ /
          (q.lcm r : ℝ) * (fouvryTau k (q / q.gcd r) : ℝ) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_weighted_lcm_sum_le hd k) hD

/-- Actual original-alpha SW pays the full transposed zero-mode
discrepancy. No zero-mode budget is assumed: the conclusion includes all
physical moduli, the true U squared, original V and the local cutoffMass.
The V/U primitive-center differences and all nonzero frequencies remain
in `actual_centered_identity_with_primitive`. -/
theorem actual_rawZero_sub_primitive_SW_bound {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (sigma kappa c0 A : ℝ) (hA : 0 < A)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale →
        ‖(F i).transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain (F i)‖ ≤
          C * |(F i).V * CommonSmoothCutoff.cutoffMass| * (F i).U ^ 2 *
            (1 + Real.log (F i).physicalFactorCap) ^
              (2 * (3 * (2 ^ C0 + 1)) ^ 2 + 1) / Real.log (F i).scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ :=
    actual_covariance_SW_bound F B C0 sigma kappa c0 A hA hadmissible hSW
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro i hx
  have hlog : 0 < Real.log (F i).scale := Real.log_pos (hx0.trans_le hx)
  rw [actual_rawZero_sub_primitive_eq_covariance (hadmissible i), norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hpoint : ∀ q ∈ (F i).physicalFactorModuli, ∀ r ∈ (F i).physicalFactorModuli,
      ‖covariance (F i).alphaCarrier (F i).alpha q r‖ ≤
        (C * (F i).U ^ 2 / Real.log (F i).scale ^ A) *
          (fouvryTau (2 ^ C0) (q / q.gcd r) : ℝ) := by
    intro q hq r _
    have hq0 := (Finset.mem_Ioc.mp ((F i).physicalFactorModuli_subset_cap
      (hadmissible i) hq)).1
    calc
      _ ≤ _ := hbound i hx q r hq0
      _ = _ := by ring
  calc
    _ ≤ |(F i).V * CommonSmoothCutoff.cutoffMass| *
        ((C * (F i).U ^ 2 / Real.log (F i).scale ^ A) *
          (1 + Real.log (F i).physicalFactorCap) ^
            (2 * (3 * (2 ^ C0 + 1)) ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left (covariance_sum_norm_le (hadmissible i) (2 ^ C0)
        (by positivity) hpoint) (abs_nonneg _)
    _ = _ := by ring

/-- The original beta L2 factor is paid by its proved divisor moment.
The complete convolution scale is X=U*V; every logarithm cost is explicit. -/
theorem actual_betaL2_mul_rawZero_SW_bound {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (sigma kappa c0 A : ℝ) (hA : 0 < A)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i, x0 ≤ (F i).scale →
        (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
          ‖(F i).transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain (F i)‖ ≤
            C * |CommonSmoothCutoff.cutoffMass| * (F i).scale ^ 2 *
              (1 + Real.log (2 * (F i).V)) ^ ((2 ^ B) ^ 2 - 1) *
                (1 + Real.log (F i).physicalFactorCap) ^
                  (2 * (3 * (2 ^ C0 + 1)) ^ 2 + 1) /
                    Real.log (F i).scale ^ A := by
  obtain ⟨C, hC, x0, hx0, hbound⟩ :=
    actual_rawZero_sub_primitive_SW_bound F B C0 sigma kappa c0 A hA hadmissible hSW
  refine ⟨2 * C, by positivity, x0, hx0, ?_⟩
  intro i hx
  have hV : 0 ≤ (F i).V := by linarith [(hadmissible i).2.1]
  have hlogV : 0 ≤ Real.log (2 * (F i).V) :=
    Real.log_nonneg (by linarith [(hadmissible i).2.1])
  calc
    _ ≤ (2 * (F i).V *
        (1 + Real.log (2 * (F i).V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (C * |(F i).V * CommonSmoothCutoff.cutoffMass| * (F i).U ^ 2 *
          (1 + Real.log (F i).physicalFactorCap) ^
            (2 * (3 * (2 ^ C0 + 1)) ^ 2 + 1) / Real.log (F i).scale ^ A) :=
      mul_le_mul (mediumAdmissible_beta_norm_sq_sum_le (hadmissible i))
        (hbound i hx) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [abs_mul, abs_of_nonneg hV]
      unfold MediumAtom.scale
      ring

/-- Literal smoothed V and U remain present after isolating the paid
covariance discrepancy; this identity pays neither of their differences. -/
theorem actual_centered_identity_with_primitive
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ n ∈ d.transposedAtom.commonSmoothCarrier,
      d.transposedAtom.commonSmoothWeight n *
        ‖d.transposedAtom.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain d) -
        2 * ((d.transposedAtom.complexDispersionV
          d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
            primitiveZeroMain d) +
        ((d.transposedAtom.complexDispersionU
          d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight : ℂ) -
            primitiveZeroMain d) + d.transposedAtom.complexCRTSmoothNonzeroPart := by
  rw [d.transposed_dispersion_identity_with_commonPoisson hd]
  ring

end TransposedZeroCovariance

end

end ImbalancedChen.Part3
