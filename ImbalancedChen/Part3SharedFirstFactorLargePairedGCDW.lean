import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3SharedFirstFactorPairCount

/-!
# The actual shared-first-factor W at large paired gcd

The full primitive p carrier is unchanged. The original cleaned alpha
supplies the nonzero signed differences; the primitive p gate and the
actual product congruences separately supply coprimality with p.

Only the whole W under the actual ordered paired-gcd mask is bounded.
No raw-zero, nonzero, centered energy or logarithmic payment is asserted.
The original beta is absent from this energy and is not assumed bounded
by one. Its outside factor stays in the preceding finite Cauchy bridge.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def MediumAtom.sharedLargePairedGCDW (d : MediumAtom) (Y : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (d.q1SliceAtom p).transposedAtom.commonLargeBetaGCDW Y

namespace SharedFirstFactorLargePairedGCDW

/- The auxiliary beta=1 record has the original geometry. The row proof
uses the public owned tau-four bound, never a mangled private name. -/
private theorem absoluteRow_le_tauFour_of_not_dvd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hn : ¬(n : ℤ) ∣ d.residue) :
    d.absoluteFactorModulusRow m n ≤
      (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) := by
  let e : MediumAtom := { d with beta := fun _ ↦ 1 }
  have he : MediumAdmissible 0 sigma kappa c0 e := by
    obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, _hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
    refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
    intro k _
    change ‖(1 : ℂ)‖ ≤ (k.divisors.card : ℝ) ^ 0
    norm_num
  have hgood : e.cleanedBeta n ≠ 0 := by
    change (if (n : ℤ) ∣ d.residue then (0 : ℂ) else 1) ≠ 0
    simpa only [if_neg hn] using (one_ne_zero : (1 : ℂ) ≠ 0)
  exact e.absoluteFactorModulusRow_le_tauFour he m n hgood

/- These three private polynomial-difference and subpower proofs are
literal extractions from the already owned TransposedLargeGCDFourier. -/
private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

private theorem actual_difference_le_polynomial
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m n : ℕ}
    (hn : n ∈ d.transposedAtom.betaCarrier)
    (hm : d.transposedAtom.commonSmoothWeight m ≠ 0) :
    (((m : ℤ) * n - d.residue).natAbs : ℝ) ≤
      7 * d.scale ^ (max 1 (1 + kappa)) := by
  have hx := one_le_scale hd
  obtain ⟨hU, hV, _, _, _, _, _, ha, _⟩ := hd
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + kappa))
  have haK : |(d.residue : ℝ)| ≤ d.scale ^ (max 1 (1 + kappa)) := by
    have ha' : |(d.residue : ℝ)| ≤ d.scale ^ (1 + kappa) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
    exact ha'.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hms : (m : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.V) :=
    subset_closure hm
  have hmhi := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset
    (lt_of_lt_of_le zero_lt_one hV) hms).2
  have hnhi : (n : ℝ) ≤ 2 * d.U :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))
  have hmn : (m : ℝ) * n ≤ 6 * d.scale := by
    calc
      _ ≤ (3 * d.V) * (2 * d.U) :=
        mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith)
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ = |(m : ℝ) * n - d.residue| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(d.residue : ℝ)| := abs_sub _ _
    _ ≤ 6 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]
      exact add_le_add hmn haK
    _ ≤ _ := by linarith

private theorem tauFour_difference_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m n : ℕ,
        n ∈ d.transposedAtom.betaCarrier → d.transposedAtom.commonSmoothWeight m ≠ 0 →
          ¬(n : ℤ) ∣ d.residue →
            (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤
              C * d.scale ^ (epsilon / 2) := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let eta : ℝ := epsilon / (2 * K)
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hKpos)
  have hKeta : K * eta = epsilon / 2 := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨D, hD, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 4) (by norm_num) heta
  refine ⟨D * (7 : ℝ) ^ eta, by positivity, fun B sigma c0 d hd m n hn hm hndiv ↦ ?_⟩
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact hndiv ⟨m, by nlinarith⟩
  have hx := one_le_scale hd
  calc
    _ ≤ D * (((m : ℤ) * n - d.residue).natAbs : ℝ) ^ eta :=
      hbound _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
    _ ≤ D * (7 * d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (actual_difference_le_polynomial hd hn hm) heta.le) hD.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]
      ring


private theorem p_pos_lower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) : 0 < p ∧ d.Q1 ≤ (p : ℝ) := by
  have hlo := (mem_Icc.mp (mem_filter.mp hp).1).1
  have hlower : d.Q1 ≤ (p : ℝ) := (Nat.le_ceil d.Q1).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < p := (zero_lt_one.trans_le hd.2.2.1).trans_le hlower
  exact ⟨by exact_mod_cast hpos, hlower⟩

private theorem p_coprime_residue
    {d : MediumAtom} {p : ℕ} (hp : p ∈ d.primitiveFirstFactorCarrier) :
    Int.gcd d.residue p = 1 := by
  simpa only [Int.gcd, Int.natAbs_natCast] using (mem_filter.mp hp).2.symm

private theorem slice_gamma (d : MediumAtom) (p : ℕ) (r : ℕ × ℕ × ℕ) :
    (d.q1SliceAtom p).transposedAtom.complexFactorGamma r =
      (if r.1 = p then (1 : ℂ) else 0) * d.gamma2 r.2.1 * d.gamma3 r.2.2 := rfl

/-- This is the actual p-divisibility support, with all complex labels. -/
private theorem absoluteRow_eq_zero_of_not_product (d : MediumAtom) (p m n : ℕ)
    (hnot : ¬Int.ModEq p ((m : ℤ) * n) d.residue) :
    (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n = 0 := by
  unfold MediumAtom.absoluteFactorModulusRow
  rw [show (d.q1SliceAtom p).transposedAtom.residue = d.residue from rfl]
  apply sum_eq_zero
  intro r _
  by_cases hq : r.1 = p
  · by_cases hr : Int.ModEq (complexFactorModulus r) ((m : ℤ) * n) d.residue
    · have hdiv : (p : ℤ) ∣ (complexFactorModulus r : ℤ) := by
        refine ⟨((r.2.1 * r.2.2 : ℕ) : ℤ), ?_⟩
        simp only [complexFactorModulus]
        rw [hq]
        push_cast
        ring
      exact (hnot (hr.of_dvd hdiv)).elim
    · simp only [if_neg hr]
  · simp only [slice_gamma, if_neg hq, zero_mul, norm_zero, ite_self]

/- Exact primitive-product and congruence cancellation from the owned
ComplexCRTConsumer, specialized to the same p. The original numerator
is signed and no size condition is used. -/
private theorem coprime_of_product_congruent {a : ℤ} {p n m : ℕ}
    (ha : Int.gcd a p = 1) (h : Int.ModEq p ((n : ℤ) * m) a) :
    n.Coprime p ∧ m.Coprime p := by
  have hg : Int.gcd ((n : ℤ) * m) p = 1 := by
    rw [← Int.gcd_emod ((n : ℤ) * m) p, h.eq, Int.gcd_emod, ha]
  have hnm : (n * m).Coprime p := by
    simpa [Int.gcd, Int.natAbs_mul] using hg
  exact Nat.coprime_mul_iff_left.mp hnm

private theorem shared_conditions_of_products {a : ℤ} {p m n₁ n₂ : ℕ}
    (hp : 0 < p) (ha : Int.gcd a p = 1)
    (h₁ : Int.ModEq p ((m : ℤ) * n₁) a)
    (h₂ : Int.ModEq p ((m : ℤ) * n₂) a) :
    n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ := by
  refine ⟨(coprime_of_product_congruent ha h₁).2,
    (coprime_of_product_congruent ha h₂).2, ?_⟩
  have hcross : Int.ModEq p (a * n₁) (a * n₂) :=
    (h₂.mul_right (n₁ : ℤ)).symm.trans
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using h₁.mul_right (n₂ : ℤ))
  apply Int.natCast_modEq_iff.mp
  simpa only [Int.gcd_comm (p : ℤ) a, ha, Nat.cast_one, Int.ediv_one]
    using hcross.cancel_left_div_gcd (by exact_mod_cast hp : (0 : ℤ) < p)

/-- The finite progression count is the owned Alpha quotient-block count. -/
private theorem sum_weight_product_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {p n : ℕ}
    (hp : 0 < p) (hn : n.Coprime p) (a : ℤ) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if Int.ModEq p ((m : ℤ) * n) a then
        d.transposedAtom.commonSmoothWeight m else 0) ≤ 4 * d.V / p + 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hceil : (Nat.ceil (3 * d.V) : ℝ) ≤ 4 * d.V := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * d.V)
    linarith
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n) a then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro m _
      split_ifs
      · exact CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _
      · exact le_rfl
    _ = (((Icc 0 (Nat.ceil (3 * d.V))).filter
        (fun m : ℕ ↦ Int.ModEq p ((m : ℤ) * n) a)).card : ℝ) := by
      rw [← sum_filter]
      simp [MediumAtom.commonSmoothCarrier, MediumAtom.transposedAtom]
    _ ≤ ((Nat.ceil (3 * d.V) / p + 1 : ℕ) : ℝ) := by
      exact_mod_cast PairedAlphaDeletion.card_product_modEq_le (Nat.ceil (3 * d.V)) p n a hn
    _ ≤ (Nat.ceil (3 * d.V) : ℝ) / p + 1 := by
      push_cast
      have hh : ((Nat.ceil (3 * d.V) / p : ℕ) : ℝ) ≤
          (Nat.ceil (3 * d.V) : ℝ) / p := Nat.cast_div_le
      exact add_le_add hh le_rfl
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hceil hpR.le) le_rfl

private theorem sum_weight_two_products_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {p : ℕ} (hp : 0 < p)
    (ha : Int.gcd d.residue p = 1) (n₁ n₂ : ℕ) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
          Int.ModEq p ((m : ℤ) * n₂) d.residue then
        d.transposedAtom.commonSmoothWeight m else 0) ≤
      if n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ then
        4 * d.V / p + 1 else 0 := by
  by_cases hc : n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂
  · rw [if_pos hc]
    apply le_trans _ (sum_weight_product_le hV hp hc.1 d.residue)
    apply sum_le_sum
    intro m _
    by_cases h₁ : Int.ModEq p ((m : ℤ) * n₁) d.residue
    · by_cases h₂ : Int.ModEq p ((m : ℤ) * n₂) d.residue
      · simp only [h₁, h₂, and_self, if_true, le_refl]
      · simpa only [h₁, h₂, and_false, if_false, if_true] using
          d.transposedAtom.commonSmoothWeight_nonneg m
    · simp only [h₁, false_and, if_false, le_refl]
  · rw [if_neg hc]
    have hz : (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
            Int.ModEq p ((m : ℤ) * n₂) d.residue then
          d.transposedAtom.commonSmoothWeight m else 0) = 0 := by
      apply sum_eq_zero
      intro m _
      apply if_neg
      exact fun hm ↦ hc (shared_conditions_of_products hp ha hm.1 hm.2)
    exact hz.le

/-- Whole factor-pair norm, with the p-progressions still inside its cost. -/
private theorem slice_factorPair_norm_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ p : ℕ,
        p ∈ d.primitiveFirstFactorCarrier → ∀ n₁ n₂ : ℕ,
          n₁ ∈ d.transposedAtom.betaCarrier → n₂ ∈ d.transposedAtom.betaCarrier →
            ¬(n₁ : ℤ) ∣ d.residue → ¬(n₂ : ℤ) ∣ d.residue →
              ‖(d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n₁ n₂‖ ≤
                C * d.scale ^ epsilon *
                  (if n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ then
                    4 * d.V / p + 1 else 0) := by
  obtain ⟨C, hC, hbound⟩ := tauFour_difference_subpower kappa hepsilon
  refine ⟨C ^ 2, by positivity, fun B sigma c0 d hd p hp n₁ n₂ hn₁ hn₂ hnd₁ hnd₂ ↦ ?_⟩
  have hs := mediumAdmissible_q1SliceAtom hd hp
  have hx := one_le_scale hd
  have hp0 := (p_pos_lower hd hp).1
  have hsum := ((d.q1SliceAtom p).transposedAtom.commonFactorPairWeight_norm_le n₁ n₂)
  have hcar : (d.q1SliceAtom p).transposedAtom.commonSmoothCarrier =
      d.transposedAtom.commonSmoothCarrier := rfl
  have hweight (m : ℕ) : (d.q1SliceAtom p).transposedAtom.commonSmoothWeight m =
      d.transposedAtom.commonSmoothWeight m := rfl
  rw [hcar] at hsum
  simp only [hweight] at hsum
  apply hsum.trans
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
            Int.ModEq p ((m : ℤ) * n₂) d.residue then
          d.transposedAtom.commonSmoothWeight m * (C ^ 2 * d.scale ^ epsilon) else 0 := by
      apply sum_le_sum
      intro m _
      by_cases hm : d.transposedAtom.commonSmoothWeight m = 0
      · simp only [hm, zero_mul, ite_self, le_refl]
      by_cases h₁ : Int.ModEq p ((m : ℤ) * n₁) d.residue
      · by_cases h₂ : Int.ModEq p ((m : ℤ) * n₂) d.residue
        · rw [if_pos ⟨h₁, h₂⟩]
          have ha₁ : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ ≤
              C * d.scale ^ (epsilon / 2) :=
            (absoluteRow_le_tauFour_of_not_dvd hs m n₁ hnd₁).trans
              (hbound B sigma c0 d hd m n₁ hn₁ hm hnd₁)
          have ha₂ : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂ ≤
              C * d.scale ^ (epsilon / 2) :=
            (absoluteRow_le_tauFour_of_not_dvd hs m n₂ hnd₂).trans
              (hbound B sigma c0 d hd m n₂ hn₂ hm hnd₂)
          have hh : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ *
              (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂ ≤
                C ^ 2 * d.scale ^ epsilon := by
            calc
              _ ≤ (C * d.scale ^ (epsilon / 2)) * (C * d.scale ^ (epsilon / 2)) :=
                mul_le_mul ha₁ ha₂
                  ((d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow_nonneg m n₂)
                  (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hx) _))
              _ = _ := by
                rw [mul_mul_mul_comm, ← Real.rpow_add (zero_lt_one.trans_le hx),
                  show epsilon / 2 + epsilon / 2 = epsilon by ring, pow_two]
          exact (show _ = d.transposedAtom.commonSmoothWeight m *
            ((d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ *
              (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂) by ring).trans_le
                (mul_le_mul_of_nonneg_left hh (d.transposedAtom.commonSmoothWeight_nonneg m))
        · rw [absoluteRow_eq_zero_of_not_product d p m n₂ h₂, mul_zero]
          simp only [h₂, and_false, if_false, le_refl]
      · rw [absoluteRow_eq_zero_of_not_product d p m n₁ h₁, mul_zero, zero_mul]
        simp only [h₁, false_and, if_false, le_refl]
    _ = (C ^ 2 * d.scale ^ epsilon) *
        ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
          if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
              Int.ModEq p ((m : ℤ) * n₂) d.residue then
            d.transposedAtom.commonSmoothWeight m else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_weight_two_products_le hd.2.1 hp0 (p_coprime_residue hp) n₁ n₂)
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (zero_le_one.trans hx) _))

private theorem cleaned_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  have hAlpha : ∀ n ∈ d.cleanedAlphaAtom.alphaCarrier, ‖d.cleanedAlphaAtom.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hclean
    exact hAlpha
  change ‖if n ∈ d.cleanedAlphaAtom.alphaCarrier then d.cleanedAlphaAtom.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.cleanedAlphaAtom.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem card_primitiveCarrier_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.Q1 := by
  have hsub : d.primitiveFirstFactorCarrier ⊆ Ioc 0 (Nat.floor (2 * d.Q1)) := by
    intro p hp
    have hlo := (mem_Icc.mp (mem_filter.mp hp).1).2
    exact mem_Ioc.mpr ⟨(p_pos_lower hd hp).1, hlo⟩
  have hc := card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.primitiveFirstFactorCarrier.card : ℝ) ≤ (Nat.floor (2 * d.Q1) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith [hd.2.2.1]))

end SharedFirstFactorLargePairedGCDW

/-- A whole-W bound for precisely the same ordered large-paired-gcd mask.
There is no bound for its raw zero or full nonzero part in this theorem. -/
theorem cleanedAlpha_sharedLargePairedGCDW_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Y : ℝ, 1 ≤ Y →
        ‖d.cleanedAlphaAtom.sharedLargePairedGCDW Y‖ ≤
          C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
            (16 * d.U ^ 2 / Y + 4 * d.Q1 * d.U * (1 + Real.log (2 * d.U))) := by
  obtain ⟨C, hC, hfactor⟩ :=
    SharedFirstFactorLargePairedGCDW.slice_factorPair_norm_subpower kappa hepsilon
  refine ⟨C, hC, fun B sigma c0 d hd Y hY ↦ ?_⟩
  have hx := SharedFirstFactorLargePairedGCDW.one_le_scale hd
  have hXeps : 0 ≤ C * d.scale ^ epsilon :=
    mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have hU0 : 0 ≤ d.U := zero_le_one.trans hd.1
  have hV0 : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hQpos : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hH : 0 ≤ 1 + Real.log (2 * d.U) := by
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.U by linarith [hd.1])]
  have hSlice (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖(d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.commonLargeBetaGCDW Y‖ ≤
        C * d.scale ^ epsilon * (4 * d.V / p + 1) *
          ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) := by
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (SharedFirstFactorLargePairedGCDW.p_pos_lower hd hp).1
    have hA : 0 ≤ C * d.scale ^ epsilon * (4 * d.V / p + 1) :=
      mul_nonneg hXeps (by positivity)
    have hExpand : (d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.commonLargeBetaGCDW Y =
        ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
          if Y < (n₁.gcd n₂ : ℝ) then
            d.cleanedAlphaAtom.transposedAtom.beta n₁ *
              star (d.cleanedAlphaAtom.transposedAtom.beta n₂) *
                (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n₁ n₂ else 0 := rfl
    rw [hExpand]
    calc
      _ ≤ ∑ n₁ ∈ d.transposedAtom.betaCarrier, ∑ n₂ ∈ d.transposedAtom.betaCarrier,
          if n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ ∧ Y < (n₁.gcd n₂ : ℝ) then
            C * d.scale ^ epsilon * (4 * d.V / p + 1) else 0 := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n₁ hn₁
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n₂ hn₂
        by_cases hy : Y < (n₁.gcd n₂ : ℝ)
        · rw [if_pos hy]
          by_cases h₁ : d.cleanedAlphaAtom.transposedAtom.beta n₁ = 0
          · simp only [h₁, zero_mul, norm_zero]
            split_ifs <;> first | exact hA | exact le_rfl
          by_cases h₂ : d.cleanedAlphaAtom.transposedAtom.beta n₂ = 0
          · simp only [h₂, star_zero, mul_zero, norm_zero]
            split_ifs <;> first | exact hA | exact le_rfl
          have hb := hfactor B sigma c0 d hd p hp n₁ n₂ hn₁ hn₂
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h₁)
            (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h₂)
          by_cases hc : n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂
          · have hfull : n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ ∧
                Y < (n₁.gcd n₂ : ℝ) := ⟨hc.1, hc.2.1, hc.2.2, hy⟩
            rw [if_pos hc] at hb
            rw [if_pos hfull]
            simp only [norm_mul, norm_star]
            have hcoef : ‖d.cleanedAlphaAtom.transposedAtom.beta n₁‖ *
                ‖d.cleanedAlphaAtom.transposedAtom.beta n₂‖ ≤ 1 := by
              simpa only [one_mul] using mul_le_mul
                (SharedFirstFactorLargePairedGCDW.cleaned_beta_norm_le_one hd n₁)
                (SharedFirstFactorLargePairedGCDW.cleaned_beta_norm_le_one hd n₂)
                (norm_nonneg _) zero_le_one
            calc
              _ ≤ 1 * (C * d.scale ^ epsilon * (4 * d.V / p + 1)) :=
                mul_le_mul hcoef hb (norm_nonneg _) zero_le_one
              _ = _ := one_mul _
          · have hnot : ¬(n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ ∧
                Y < (n₁.gcd n₂ : ℝ)) := fun h ↦ hc ⟨h.1, h.2.1, h.2.2.1⟩
            have hzero : (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n₁ n₂ = 0 := by
              apply norm_eq_zero.mp
              exact le_antisymm (by simpa only [if_neg hc, mul_zero] using hb) (norm_nonneg _)
            simp only [hzero, mul_zero, norm_zero, if_neg hnot, le_refl]
        · have hnot : ¬(n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ ∧
              Y < (n₁.gcd n₂ : ℝ)) := fun h ↦ hy h.2.2.2
          simp only [if_neg hy, if_neg hnot, norm_zero, le_refl]
      _ = _ := by
        rw [← sum_product, ← sum_filter]
        simp only [sharedPrimitiveLargeGCDPairs, sum_const, nsmul_eq_mul]
        ring
  have hRect : ∀ p ∈ d.primitiveFirstFactorCarrier,
      (4 * d.V / p + 1) * ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) ≤
        (4 * d.V / d.Q1 + 1) *
          (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U))) := by
    intro p hp
    obtain ⟨hp0, hpQ⟩ := SharedFirstFactorLargePairedGCDW.p_pos_lower hd hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hA : 4 * d.V / p + 1 ≤ 4 * d.V / d.Q1 + 1 :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hQpos hpQ) le_rfl
    have hCount := d.card_sharedPrimitiveLargeGCDPairs_le hd.1 hY hp0
    have hden : d.Q1 * Y ≤ (p : ℝ) * Y := mul_le_mul_of_nonneg_right hpQ hYpos.le
    have hCount' : ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) ≤
        8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)) := hCount.trans
      (add_le_add (div_le_div_of_nonneg_left (by positivity) (mul_pos hQpos hYpos) hden) le_rfl)
    exact mul_le_mul hA hCount' (Nat.cast_nonneg _) (by positivity)
  unfold MediumAtom.sharedLargePairedGCDW
  rw [show d.cleanedAlphaAtom.primitiveFirstFactorCarrier = d.primitiveFirstFactorCarrier from rfl]
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖(d.cleanedAlphaAtom.q1SliceAtom p).transposedAtom.commonLargeBetaGCDW Y‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        C * d.scale ^ epsilon * (4 * d.V / p + 1) *
          ((sharedPrimitiveLargeGCDPairs d.transposedAtom.betaCarrier p Y).card : ℝ) :=
      sum_le_sum hSlice
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
        C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U))) := by
      apply sum_le_sum
      intro p hp
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hRect p hp) hXeps
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
        (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)))) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) *
        (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          (8 * d.U ^ 2 / (d.Q1 * Y) + 2 * d.U * (1 + Real.log (2 * d.U)))) :=
      mul_le_mul_of_nonneg_right (SharedFirstFactorLargePairedGCDW.card_primitiveCarrier_le hd)
        (mul_nonneg (mul_nonneg hXeps (by positivity))
          (add_nonneg (div_nonneg (by positivity) (mul_nonneg hQpos.le hYpos.le))
            (mul_nonneg (mul_nonneg (by norm_num) hU0) hH)))
    _ = _ := by
      field_simp [hQpos.ne', hYpos.ne']
      ring

end

end ImbalancedChen.Part3
