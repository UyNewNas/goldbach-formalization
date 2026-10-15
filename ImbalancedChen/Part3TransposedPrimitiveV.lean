import ImbalancedChen.Part3TransposedPrimitiveU
import ImbalancedChen.Part3PrimitiveZeroReal

/-!
# The literal transposed mixed term minus the actual primitive zero main term

The full complex mixed sum retains every physical modulus and every
original alpha integer. The actual real dispersion V is its real part.
The primitive zero main term is proved real, so taking that real part
cannot increase the norm of the difference.

Primitive residues are used only when a grouped factor coefficient is
nonzero. That gate is proved from the original active gamma factors;
inactive grouped coefficients contribute zero on the unchanged carrier.
The finite error envelope is paid by the actual local mixed progression
bound, with its constant preceding every atom and arithmetic parameter.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance TransposedPrimitiveU

namespace TransposedPrimitiveV

/-- A nonzero grouped coefficient has an original active factor label,
and hence inherits the original primitive-residue gate. -/
theorem active_grouped_residue_gcd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {q : ℕ}
    (hG : d.groupedFactorGamma q ≠ 0) : Int.gcd d.residue q = 1 := by
  by_contra hbad
  apply hG
  unfold MediumAtom.groupedFactorGamma
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha, hqa⟩ := Finset.mem_filter.mp ha
  by_contra hgamma
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨ha1, ha23⟩ := Finset.mem_product.mp ha
  obtain ⟨ha2, ha3⟩ := Finset.mem_product.mp ha23
  have hg : d.gamma1 a.1 * d.gamma2 a.2.1 * d.gamma3 a.2.2 ≠ 0 := hgamma
  obtain ⟨hg12, hg3⟩ := mul_ne_zero_iff.mp hg
  obtain ⟨hg1, hg2⟩ := mul_ne_zero_iff.mp hg12
  have hcop : (complexFactorModulus a).Coprime d.residue.natAbs :=
    (((h1 a.1 ha1).2 hg1).mul_left ((h2 a.2.1 ha2).2 hg2)).mul_left
      ((h3 a.2.2 ha3).2 hg3)
  have hgcd : Int.gcd d.residue (complexFactorModulus a) = 1 := by
    simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using hcop.gcd_eq_one
  exact hbad (hqa ▸ hgcd)

def progressionMass (d : MediumAtom) (m q : ℕ) : ℂ :=
  ∑ n ∈ d.alphaCarrier,
    if Int.ModEq q ((m : ℤ) * n) d.residue then d.alpha n else 0

/-- Exact progression-row grouping before any primitive-residue assumption. -/
theorem actual_progressionRow_eq_grouped (d : MediumAtom) (m : ℕ) :
    d.transposedAtom.complexProgressionRow m =
      ∑ q ∈ d.physicalFactorModuli, d.groupedFactorGamma q * progressionMass d m q := by
  have hmass (q : ℕ) :
      (∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n *
        (if (((m * n : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ))
          then (1 : ℂ) else 0)) = progressionMass d m q := by
    rw [d.sum_transposedBeta_mul]
    unfold progressionMass
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : Int.ModEq q ((m : ℤ) * n) d.residue
    · have hc' : (((m * n : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ)) := by
        simpa only [Int.ModEq, Nat.cast_mul] using hc
      rw [if_pos hc', if_pos hc, mul_one]
    · have hc' : ¬(((m * n : ℕ) : ℤ) % (q : ℤ) = d.residue % (q : ℤ)) := by
        simpa only [Int.ModEq, Nat.cast_mul] using hc
      rw [if_neg hc', if_neg hc, mul_zero]
  calc
    _ = ∑ a ∈ d.complexFactorLabels, d.complexFactorGamma a *
        ∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n *
          (if (((m * n : ℕ) : ℤ) % (complexFactorModulus a : ℤ) =
            d.residue % (complexFactorModulus a : ℤ)) then (1 : ℂ) else 0) := by
      unfold MediumAtom.complexProgressionRow MediumAtom.complexRowLabels
      simp only [Finset.sum_product]
      change (∑ a ∈ d.complexFactorLabels, ∑ n ∈ d.transposedAtom.betaCarrier,
        d.complexFactorGamma a * d.transposedAtom.beta n *
          (if (((m * n : ℕ) : ℤ) % (complexFactorModulus a : ℤ) =
            d.residue % (complexFactorModulus a : ℤ)) then (1 : ℂ) else 0)) = _
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a ∈ d.complexFactorLabels,
        d.complexFactorGamma a * progressionMass d m (complexFactorModulus a) := by
      simp only [hmass]
    _ = _ := d.sum_factorLabels_eq_grouped (fun q : ℕ ↦ progressionMass d m q)

def mixedPairCoefficient (d : MediumAtom) (q r : ℕ) : ℂ :=
  d.groupedFactorGamma q * star (d.groupedFactorGamma r) *
    star (coprimeMass d.alphaCarrier d.alpha r) / (r.totient : ℂ)

def mixedProgressionMass (d : MediumAtom) (q r : ℕ) : ℂ :=
  ∑ n ∈ d.alphaCarrier, d.alpha n *
    ((∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
        then d.transposedAtom.commonSmoothWeight m else 0 : ℝ) : ℂ)

def actualMixedTerm (d : MediumAtom) : ℂ :=
  ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
    mixedPairCoefficient d q r * mixedProgressionMass d q r

theorem actual_row_product_eq_pair (d : MediumAtom) (m : ℕ) :
    d.transposedAtom.complexProgressionRow m *
        star (d.transposedAtom.complexPrincipalRow m) =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        mixedPairCoefficient d q r *
          ∑ n ∈ d.alphaCarrier, d.alpha n *
            (if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
              then (1 : ℂ) else 0) := by
  rw [actual_progressionRow_eq_grouped, actual_principalRow_eq_grouped,
    star_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hm : m.Coprime r
  · rw [if_pos hm, star_div₀, star_mul', star_natCast]
    unfold progressionMass
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hc : Int.ModEq q ((m : ℤ) * n) d.residue
    · rw [if_pos hc, if_pos ⟨hm, hc⟩]
      unfold mixedPairCoefficient
      simp only [div_eq_mul_inv]
      ring
    · rw [if_neg hc, if_neg (fun h ↦ hc h.2)]
      ring
  · rw [if_neg hm]
    have hsum : (∑ n ∈ d.alphaCarrier, d.alpha n *
        (if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
          then (1 : ℂ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro n _
      rw [if_neg (fun h ↦ hm h.1), mul_zero]
    rw [hsum]
    simp only [mul_zero, zero_div, star_zero]

/-- The pair sum is the full complex row product, not its real surrogate. -/
theorem actualMixedTerm_eq_row_sum (d : MediumAtom) :
    actualMixedTerm d =
      ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        (d.transposedAtom.commonSmoothWeight m : ℂ) *
          (d.transposedAtom.complexProgressionRow m *
            star (d.transposedAtom.complexPrincipalRow m)) := by
  symm
  simp_rw [actual_row_product_eq_pair, Finset.mul_sum]
  unfold actualMixedTerm mixedProgressionMass
  simp only [Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs <;> push_cast <;> ring

theorem actualV_eq_re (d : MediumAtom) :
    d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight = (actualMixedTerm d).re := by
  rw [actualMixedTerm_eq_row_sum]
  unfold MediumAtom.complexDispersionV
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- The actual V difference is controlled by the complex mixed difference
because the literal primitive zero main term has already been proved real. -/
theorem actualV_sub_primitive_norm_le (d : MediumAtom) :
    ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
        ‖actualMixedTerm d - primitiveZeroMain d‖ := by
  calc
    _ = ‖((actualMixedTerm d).re : ℂ) - ((primitiveZeroMain d).re : ℂ)‖ := by
      rw [actualV_eq_re, primitiveZeroMain_ofReal_re]
    _ = |(actualMixedTerm d - primitiveZeroMain d).re| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.sub_re]
    _ ≤ _ := Complex.abs_re_le_norm _

/-- The mixed arithmetic zero mode is exactly the actual primitive main
term. This identity approximates neither the literal U nor the literal V. -/
theorem primitiveZeroMain_eq_mixed_main
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    primitiveZeroMain d =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        mixedPairCoefficient d q r *
          (coprimeMass d.alphaCarrier d.alpha q *
            (((d.V * CommonSmoothCutoff.cutoffMass / q) *
              ∑ e ∈ r.divisors.filter (fun e ↦ e.Coprime q),
                (ArithmeticFunction.moebius e : ℝ) / e : ℝ) : ℂ)) := by
  rw [primitiveZeroMain_eq_grouped]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  have hq0 : q ≠ 0 :=
    (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hq)).1.ne'
  have hr0 : r ≠ 0 :=
    (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hr)).1.ne'
  have hdensity := CommonSmoothCutoff.restricted_moebius_density hq0 hr0
  have hz : (d.V * CommonSmoothCutoff.cutoffMass / q) *
        (∑ e ∈ r.divisors.filter (fun e ↦ e.Coprime q),
          (ArithmeticFunction.moebius e : ℝ) / e) =
      (d.V * CommonSmoothCutoff.cutoffMass) *
        (((q * r).totient : ℝ) / ((q.totient : ℝ) * (q * r : ℕ))) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, hdensity]
  rw [hz]
  unfold mixedPairCoefficient primitivePairCoefficient
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem actualMixedTerm_sub_primitive_eq
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    actualMixedTerm d - primitiveZeroMain d =
      ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        mixedPairCoefficient d q r *
          (mixedProgressionMass d q r - coprimeMass d.alphaCarrier d.alpha q *
            (((d.V * CommonSmoothCutoff.cutoffMass / q) *
              ∑ e ∈ r.divisors.filter (fun e ↦ e.Coprime q),
                (ArithmeticFunction.moebius e : ℝ) / e : ℝ) : ℂ)) := by
  rw [actualMixedTerm, primitiveZeroMain_eq_mixed_main hd, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_sub]

/-- The actual alpha-weighted complex mixed error. Its universal constant
is inherited from the proved local mixed progression error. -/
theorem mixedProgressionMass_sub_main_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ d : MediumAtom, 1 ≤ d.V → ∀ q r : ℕ,
      0 < q → r ≠ 0 → Int.gcd d.residue q = 1 →
      ‖mixedProgressionMass d q r - coprimeMass d.alphaCarrier d.alpha q *
        (((d.V * CommonSmoothCutoff.cutoffMass / q) *
          ∑ e ∈ r.divisors.filter (fun e ↦ e.Coprime q),
            (ArithmeticFunction.moebius e : ℝ) / e : ℝ) : ℂ)‖ ≤
        C * coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
          (r.divisors.card : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    CommonSmoothCutoff.scaledDyadicCutoff_finset_coprime_progression_uniform_error
  refine ⟨C, hC, fun d hV q r hq hr ha ↦ ?_⟩
  let z : ℝ := (d.V * CommonSmoothCutoff.cutoffMass / q) *
    ∑ e ∈ r.divisors.filter (fun e ↦ e.Coprime q),
      (ArithmeticFunction.moebius e : ℝ) / e
  unfold mixedProgressionMass coprimeMass
  change ‖(∑ n ∈ d.alphaCarrier, d.alpha n *
      ((∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
          then d.transposedAtom.commonSmoothWeight m else 0 : ℝ) : ℂ)) -
      (∑ n ∈ d.alphaCarrier, if n.Coprime q then d.alpha n else 0) * (z : ℂ)‖ ≤
    C * (∑ n ∈ d.alphaCarrier, if n.Coprime q then ‖d.alpha n‖ else 0) *
      (r.divisors.card : ℝ)
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ d.alphaCarrier,
        C * (if n.Coprime q then ‖d.alpha n‖ else 0) * (r.divisors.card : ℝ) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n _
      by_cases hn : n.Coprime q
      · rw [if_pos hn]
        rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
        have he := hbound d.V (lt_of_lt_of_le zero_lt_one hV)
          d.transposedAtom.commonSmoothCarrier
          (fun m hm ↦ MediumAtom.transposedSmoothWeight_support_subset hV hm)
          q r n hq hr hn d.residue ha
        change |(∑ m ∈ d.transposedAtom.commonSmoothCarrier,
          if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
            then d.transposedAtom.commonSmoothWeight m else 0) - z| ≤
          C * (r.divisors.card : ℝ) at he
        calc
          _ ≤ ‖d.alpha n‖ * (C * (r.divisors.card : ℝ)) :=
            mul_le_mul_of_nonneg_left he (norm_nonneg _)
          _ = _ := by
            rw [if_pos hn]
            ring
      · have hz : (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
            if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) d.residue
              then d.transposedAtom.commonSmoothWeight m else 0 : ℝ) = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          apply if_neg
          intro hm
          exact hn (CommonSmoothCutoff.coprime_of_product_congruent ha hm.2).2
        simp only [if_neg hn, hz, Complex.ofReal_zero, mul_zero, zero_mul,
          sub_zero, norm_zero]
        exact le_rfl
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

/-- The finite actual V envelope is a conclusion, not an assumed budget.
Only active q coefficients use a primitive-residue gate. -/
theorem actualV_sub_primitive_finite_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
      ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
        d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ ≤
        C * ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
          ‖mixedPairCoefficient d q r‖ *
            coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
              (r.divisors.card : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := mixedProgressionMass_sub_main_uniform_bound
  refine ⟨C, hC, fun B sigma kappa c0 d hd ↦ ?_⟩
  apply (actualV_sub_primitive_norm_le d).trans
  rw [actualMixedTerm_sub_primitive_eq hd]
  calc
    _ ≤ ∑ q ∈ d.physicalFactorModuli, ∑ r ∈ d.physicalFactorModuli,
        C * (‖mixedPairCoefficient d q r‖ *
          coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
            (r.divisors.card : ℝ)) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q hq
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      by_cases hG : d.groupedFactorGamma q = 0
      · simp only [mixedPairCoefficient, hG, zero_mul, zero_div, norm_zero, mul_zero]
        exact le_rfl
      · have hq0 := (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hq)).1
        have hr0 := (Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hr)).1.ne'
        rw [norm_mul]
        calc
          _ ≤ ‖mixedPairCoefficient d q r‖ *
              (C * coprimeMass d.alphaCarrier (fun n ↦ ‖d.alpha n‖) q *
                (r.divisors.card : ℝ)) :=
            mul_le_mul_of_nonneg_left (hbound d hd.2.1 q r hq0 hr0
              (active_grouped_residue_gcd hd hG)) (norm_nonneg _)
          _ = _ := by ring
    _ = _ := by simp only [Finset.mul_sum]

end TransposedPrimitiveV

end

end ImbalancedChen.Part3
