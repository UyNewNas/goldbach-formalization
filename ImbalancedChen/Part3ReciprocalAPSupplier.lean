import ImbalancedChen.Part3MediumFiniteData
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryProgressionWeil

/-!
# The actual factor-modulus reciprocal AP supplier

The pinned external Fouvry theorem is applied to the complete integer
modulus `q1*q2*q3` of `MediumAtom`, not to one auxiliary factor length.
Membership in the actual three dyadic carriers supplies positivity.
Natural AP parameters retain their literal `X < t <= Y` endpoints and
their multiplicity even when the interval is longer than the modulus.

The residue coprimality is supplied by the three actual gamma gates.
It removes the moving residue from the gcd of the reciprocal frequency.
The gamma product stays inside the norm, including its zero branches.

This is an individual unweighted reciprocal AP bound. It does not supply
the dispersion decomposition of `MediumAtom.discrepancy`, auxiliary SW,
the aggregate gcd sums, or `RestrictedMediumObligation`. In particular
there is no arbitrary extra coefficient or arithmetic mask in the AP.
The fixed-pin supplier's transitive-axiom and object replay acceptance is
a separate obligation from these source-level adaptations.
-/

namespace ImbalancedChen.Part3

noncomputable section

open scoped BigOperators
open Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Literal carrier membership gives both real endpoints, including the
positive lower endpoint needed by the complete physical modulus. -/
theorem factorCarrier_real_bounds {Q : ℝ} (hQ : 1 ≤ Q)
    {q : ℕ} (hq : q ∈ factorCarrier Q) :
    0 < q ∧ Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
  have hloR : Q ≤ (q : ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hhiR : (q : ℝ) ≤ 2 * Q :=
    (show (q : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * Q))
  refine ⟨?_, hloR, hhiR⟩
  have hqR : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) (hQ.trans hloR)
  exact_mod_cast hqR

/-- The full physical modulus is positive and remains the product of
the three integer factors. Its dyadic bound is not a physical BV cap. -/
theorem factorCarrier_product_bounds {Q1 Q2 Q3 : ℝ}
    (hQ1 : 1 ≤ Q1) (hQ2 : 1 ≤ Q2) (hQ3 : 1 ≤ Q3)
    {q1 q2 q3 : ℕ} (hq1 : q1 ∈ factorCarrier Q1)
    (hq2 : q2 ∈ factorCarrier Q2) (hq3 : q3 ∈ factorCarrier Q3) :
    0 < q1 * q2 * q3 ∧
      ((q1 * q2 * q3 : ℕ) : ℝ) ≤ 8 * Q1 * Q2 * Q3 := by
  obtain ⟨h1, _h1lo, h1hi⟩ := factorCarrier_real_bounds hQ1 hq1
  obtain ⟨h2, _h2lo, h2hi⟩ := factorCarrier_real_bounds hQ2 hq2
  obtain ⟨h3, _h3lo, h3hi⟩ := factorCarrier_real_bounds hQ3 hq3
  refine ⟨Nat.mul_pos (Nat.mul_pos h1 h2) h3, ?_⟩
  have h12 : (q1 : ℝ) * q2 ≤ (2 * Q1) * (2 * Q2) :=
    mul_le_mul h1hi h2hi (Nat.cast_nonneg q2) (by linarith)
  calc
    ((q1 * q2 * q3 : ℕ) : ℝ) = (q1 : ℝ) * q2 * q3 := by push_cast; ring
    _ ≤ ((2 * Q1) * (2 * Q2)) * (2 * Q3) :=
      mul_le_mul h12 h3hi (Nat.cast_nonneg q3)
        (mul_nonneg (by linarith) (by linarith))
    _ = 8 * Q1 * Q2 * Q3 := by ring

/-- Extract the actual factor scales without strengthening the medium
proposition's admissibility hypotheses. -/
theorem mediumAdmissible_factorScale_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    1 ≤ d.Q1 ∧ 1 ≤ d.Q2 ∧ 1 ≤ d.Q3 := by
  obtain ⟨_hU, _hV, h1, h2, h3, _⟩ := hd
  exact ⟨h1, h2, h3⟩

/-- Every active gamma factor is coprime to the original moving residue,
so their complete product is coprime too. No pairwise coprimality of the
three modulus factors is needed. -/
theorem mediumAdmissible_active_modulus_coprime_residue
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {q1 q2 q3 : ℕ} (hq1 : q1 ∈ factorCarrier d.Q1)
    (hq2 : q2 ∈ factorCarrier d.Q2) (hq3 : q3 ∈ factorCarrier d.Q3)
    (hg1 : d.gamma1 q1 ≠ 0) (hg2 : d.gamma2 q2 ≠ 0)
    (hg3 : d.gamma3 q3 ≠ 0) :
    (q1 * q2 * q3).Coprime d.residue.natAbs := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  exact (((h1 q1 hq1).2 hg1).mul_left ((h2 q2 hq2).2 hg2)).mul_left
    ((h3 q3 hq3).2 hg3)

/-- The actual gamma product is one-bounded; signs and complex phases
remain inside the final norm. -/
theorem mediumAdmissible_gamma_product_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    {q1 q2 q3 : ℕ} (hq1 : q1 ∈ factorCarrier d.Q1)
    (hq2 : q2 ∈ factorCarrier d.Q2) (hq3 : q3 ∈ factorCarrier d.Q3) :
    ‖d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  rw [norm_mul, norm_mul]
  have h12 : ‖d.gamma1 q1‖ * ‖d.gamma2 q2‖ ≤ (1 : ℝ) := by
    simpa only [one_mul] using mul_le_mul (h1 q1 hq1).1 (h2 q2 hq2).1
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using
    mul_le_mul h12 (h3 q3 hq3).1 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- Removing a unit residue from the reciprocal frequency keeps the gcd
with the full physical modulus exactly, also at zero and negative frequency. -/
theorem reciprocalFrequency_gcd_cancel_residue {q : ℕ} (a delta : ℤ)
    (ha : a.natAbs.Coprime q) :
    q.gcd (a * delta).natAbs = q.gcd delta.natAbs := by
  rw [Int.natAbs_mul, Nat.mul_comm a.natAbs delta.natAbs]
  exact ha.gcd_mul_right_cancel_right _

/-- The same pinned Fouvry constant covers every complete factor modulus,
natural AP and frequency before any atom or endpoint is chosen. The sum
keeps the literal natural parameter rather than reducing it modulo q. -/
theorem naturalReciprocalAP_fullModulus_fouvry {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (_ : NeZero q) (frequency : ℤ) (b v X Y : ℕ),
        v.Coprime q → X ≤ Y →
        ‖∑ t ∈ Finset.Ioc X Y,
          reciprocalPhase q frequency ((b + v * t : ℕ) : ZMod q)‖ ≤
            C * (1 + ((Y : ℝ) - X) / q) *
              Real.sqrt (q.gcd frequency.natAbs) *
                (q : ℝ) ^ (1 / 2 + epsilon : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocalProgression_fouvry hepsilon
  refine ⟨C, hC, ?_⟩
  intro q hq frequency b v X Y hv hXY
  rw [reciprocalProgression_nat]
  simpa only [Int.cast_natCast] using
    hbound q hq frequency b v X Y hv (by exact_mod_cast hXY)

/-- An actual medium atom receives the individual AP estimate with its
three gamma factors and moving residue. Positivity comes from the
literal dyadic carriers; residue coprimality comes from the active gamma
gates. The resulting gcd is that of the reduced collision frequency.

Only the sampled reciprocal phase is estimated here. Identifying a
completed dispersion term with this AP is a separate required identity. -/
theorem medium_gamma_reciprocalAP_fouvry {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom)
        (hd : MediumAdmissible B sigma kappa c0 d)
        (q1 q2 q3 : ℕ) (hq1 : q1 ∈ factorCarrier d.Q1)
        (hq2 : q2 ∈ factorCarrier d.Q2) (hq3 : q3 ∈ factorCarrier d.Q3)
        (delta : ℤ) (b v X Y : ℕ),
        v.Coprime (q1 * q2 * q3) → X ≤ Y →
        letI : NeZero (q1 * q2 * q3) :=
          ⟨(factorCarrier_product_bounds
            (mediumAdmissible_factorScale_bounds hd).1
            (mediumAdmissible_factorScale_bounds hd).2.1
            (mediumAdmissible_factorScale_bounds hd).2.2 hq1 hq2 hq3).1.ne'⟩
        ‖(d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3) *
          ∑ t ∈ Finset.Ioc X Y,
            reciprocalPhase (q1 * q2 * q3) (d.residue * delta)
              ((b + v * t : ℕ) : ZMod (q1 * q2 * q3))‖ ≤
          C * (1 + ((Y : ℝ) - X) / (q1 * q2 * q3 : ℕ)) *
            Real.sqrt ((q1 * q2 * q3).gcd delta.natAbs) *
              (q1 * q2 * q3 : ℕ) ^ (1 / 2 + epsilon : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := naturalReciprocalAP_fullModulus_fouvry hepsilon
  refine ⟨C, hC, ?_⟩
  intro B sigma kappa c0 d hd q1 q2 q3 hq1 hq2 hq3 delta b v X Y hv hXY
  letI : NeZero (q1 * q2 * q3) :=
    ⟨(factorCarrier_product_bounds
      (mediumAdmissible_factorScale_bounds hd).1
      (mediumAdmissible_factorScale_bounds hd).2.1
      (mediumAdmissible_factorScale_bounds hd).2.2 hq1 hq2 hq3).1.ne'⟩
  have hlength : 0 ≤ (Y : ℝ) - X := sub_nonneg.mpr (by exact_mod_cast hXY)
  have hbudget : 0 ≤
      C * (1 + ((Y : ℝ) - X) / (q1 * q2 * q3 : ℕ)) *
        Real.sqrt ((q1 * q2 * q3).gcd delta.natAbs) *
          (q1 * q2 * q3 : ℕ) ^ (1 / 2 + epsilon : ℝ) := by
    positivity
  by_cases hg1 : d.gamma1 q1 = 0
  · simpa only [hg1, zero_mul, norm_zero] using hbudget
  by_cases hg2 : d.gamma2 q2 = 0
  · simpa only [hg2, mul_zero, zero_mul, norm_zero] using hbudget
  by_cases hg3 : d.gamma3 q3 = 0
  · simpa only [hg3, mul_zero, zero_mul, norm_zero] using hbudget
  have hcop := mediumAdmissible_active_modulus_coprime_residue
    hd hq1 hq2 hq3 hg1 hg2 hg3
  have hAP := hbound (q1 * q2 * q3) inferInstance
    (d.residue * delta) b v X Y hv hXY
  rw [reciprocalFrequency_gcd_cancel_residue d.residue delta hcop.symm] at hAP
  calc
    _ = ‖d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3‖ *
        ‖∑ t ∈ Finset.Ioc X Y,
          reciprocalPhase (q1 * q2 * q3) (d.residue * delta)
            ((b + v * t : ℕ) : ZMod (q1 * q2 * q3))‖ := norm_mul _ _
    _ ≤ ‖∑ t ∈ Finset.Ioc X Y,
        reciprocalPhase (q1 * q2 * q3) (d.residue * delta)
          ((b + v * t : ℕ) : ZMod (q1 * q2 * q3))‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mediumAdmissible_gamma_product_norm_le_one hd hq1 hq2 hq3) (norm_nonneg _)
    _ ≤ _ := hAP

end

end ImbalancedChen.Part3
