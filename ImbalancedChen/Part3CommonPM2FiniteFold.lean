import ImbalancedChen.Part3CommonPFiniteReduction
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace CommonPM2FiniteFold

def shiftDifference (d : MediumAtom) (v : ℕ) : ℕ :=
  ((v : ℤ) - d.residue).natAbs

def tau (v : ℕ) : ℝ := (v.divisors.card : ℝ)

def fourthDivisorWeight (d : MediumAtom) (v : ℕ) : ℝ :=
  (fouvryTau 4 (shiftDifference d v) : ℝ) ^ 4

def productCarrier (d : MediumAtom) : Finset ℕ :=
  (Ioc 0 (Nat.floor (6 * d.scale))).filter (fun v => (v : ℤ) ≠ d.residue)

/-- The literal actual row, including its signed divisor-deletion gate. -/
def rowSum (d : MediumAtom) (p m : ℕ) : ℝ :=
  ∑ n ∈ d.cleanedCommonPProgression p m,
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ *
      (fouvryTau 4 (shiftDifference d (m * n)) : ℝ) ^ 2

def moment (d : MediumAtom) : ℝ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    ∑ m ∈ d.cleanedAlphaAtom.transposedAtom.commonSmoothCarrier,
      d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m * rowSum d p m ^ 2

/-- Every label is (p,m,n), not an unlabelled modulus or a pair quotient. -/
def activeLabels (d : MediumAtom) : Finset ((ℕ × ℕ) × ℕ) :=
  ((d.primitiveFirstFactorCarrier ×ˢ
      d.cleanedAlphaAtom.transposedAtom.commonSmoothCarrier) ×ˢ
      d.cleanedAlphaAtom.transposedAtom.betaCarrier).filter
    (fun z => d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight z.1.2 ≠ 0 ∧
      z.2 ∈ d.cleanedCommonPProgression z.1.1 z.1.2)

def labelProduct (z : (ℕ × ℕ) × ℕ) : ℕ := z.1.2 * z.2

def foldedSum (d : MediumAtom) : ℝ :=
  ∑ v ∈ productCarrier d,
    tau v * tau (shiftDifference d v) * fourthDivisorWeight d v

/-- Original outside energies occur exactly once. -/
def outsideEnergy (d : MediumAtom) : ℝ :=
  (∑ m ∈ d.betaCarrier, ‖d.beta m‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)

theorem cleaned_transposedBeta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
  change ‖(if n ∈ d.alphaCarrier then d.cleanedAlpha n else 0)‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · rw [if_pos hn]
    by_cases hdiv : (n : ℤ) ∣ d.residue
    · simp only [MediumAtom.cleanedAlpha, if_pos hdiv, norm_zero, zero_le_one]
    · simpa only [MediumAtom.cleanedAlpha, if_neg hdiv] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

/-- Stage 1: genuine row Cauchy; no moment estimate is a premise. -/
theorem rowSum_sq_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma)
    (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) (m : ℕ)
    (hpsi : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0) :
    rowSum d p m ^ 2 ≤ (3 * d.U / d.Q1) *
      ∑ n ∈ d.cleanedCommonPProgression p m, fourthDivisorWeight d (m * n) := by
  by_cases hrow : (d.cleanedCommonPProgression p m).Nonempty
  · have hcard := (d.cleaned_commonP_progression_geometry
      hd hsigma p hp m hpsi hrow).2.2.2.2
    have hinner :
        (∑ n ∈ d.cleanedCommonPProgression p m,
          (‖d.cleanedAlphaAtom.transposedAtom.beta n‖ *
            (fouvryTau 4 (shiftDifference d (m * n)) : ℝ) ^ 2) ^ 2) ≤
        ∑ n ∈ d.cleanedCommonPProgression p m,
          fourthDivisorWeight d (m * n) := by
      apply Finset.sum_le_sum
      intro n _
      have hb : ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ^ 2 ≤ (1 : ℝ) := by
        simpa only [one_pow] using
          (sq_le_sq₀ (norm_nonneg _) zero_le_one).2
            (cleaned_transposedBeta_norm_le_one hd n)
      calc
        _ = ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ^ 2 *
            fourthDivisorWeight d (m * n) := by unfold fourthDivisorWeight; ring
        _ ≤ 1 * fourthDivisorWeight d (m * n) :=
          mul_le_mul_of_nonneg_right hb (by unfold fourthDivisorWeight; positivity)
        _ = _ := one_mul _
    calc
      _ ≤ ((d.cleanedCommonPProgression p m).card : ℝ) *
          ∑ n ∈ d.cleanedCommonPProgression p m,
            (‖d.cleanedAlphaAtom.transposedAtom.beta n‖ *
              (fouvryTau 4 (shiftDifference d (m * n)) : ℝ) ^ 2) ^ 2 := by
        simpa only [rowSum, one_mul, one_pow, Finset.sum_const,
          nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq
            (d.cleanedCommonPProgression p m) (fun _ => (1 : ℝ))
            (fun n => ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ *
              (fouvryTau 4 (shiftDifference d (m * n)) : ℝ) ^ 2)
      _ ≤ ((d.cleanedCommonPProgression p m).card : ℝ) *
          ∑ n ∈ d.cleanedCommonPProgression p m,
            fourthDivisorWeight d (m * n) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg (fun _ _ => by unfold fourthDivisorWeight; positivity))
  · have hempty : d.cleanedCommonPProgression p m = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hrow
    simp only [rowSum, hempty, Finset.sum_empty, zero_pow (by decide : 2 ≠ 0), mul_zero,
      le_refl]

/-- Stage 2a: discard only zero smooth weights; keep all actual row gates. -/
theorem sum_activeLabels (d : MediumAtom) (F : ℕ → ℝ) :
    (∑ z ∈ activeLabels d, F (labelProduct z)) =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        ∑ m ∈ d.cleanedAlphaAtom.transposedAtom.commonSmoothCarrier,
          if d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0 then
            ∑ n ∈ d.cleanedCommonPProgression p m, F (m * n) else 0 := by
  simp only [activeLabels, Finset.sum_filter, Finset.sum_product, labelProduct]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro m _
  by_cases hpsi : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0
  · rw [if_pos hpsi]
    simp only [MediumAtom.cleanedCommonPProgression, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_filter, hn, true_and]
    by_cases hg : ¬(n : ℤ) ∣ d.residue ∧
        Int.ModEq p ((m : ℤ) * n) d.residue
    · rw [if_pos (And.intro hpsi hg), if_pos hg]
    · have hboth : ¬(d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0 ∧
          (¬(n : ℤ) ∣ d.residue ∧
            Int.ModEq p ((m : ℤ) * n) d.residue)) := by
        intro h
        exact hg h.2
      rw [if_neg hboth, if_neg hg]
  · simp only [hpsi, false_and, if_false, Finset.sum_const_zero]

theorem moment_le_activeLabels
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    moment d ≤ (3 * d.U / d.Q1) *
      ∑ z ∈ activeLabels d, fourthDivisorWeight d (labelProduct z) := by
  rw [sum_activeLabels, Finset.mul_sum]
  unfold moment
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  by_cases hpsi : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≠ 0
  · rw [if_pos hpsi]
    have hpsi0 := d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight_nonneg m
    have hpsi1 : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m ≤ 1 :=
      CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _
    have hbase : 0 ≤ (3 * d.U / d.Q1) *
        ∑ n ∈ d.cleanedCommonPProgression p m, fourthDivisorWeight d (m * n) := by
      have hU : 0 ≤ d.U := zero_le_one.trans hd.1
      have hQ : 0 ≤ d.Q1 := zero_le_one.trans hd.2.2.1
      apply mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hU) hQ)
      exact Finset.sum_nonneg (fun _ _ => by unfold fourthDivisorWeight; positivity)
    calc
      _ ≤ d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m *
          ((3 * d.U / d.Q1) *
            ∑ n ∈ d.cleanedCommonPProgression p m, fourthDivisorWeight d (m * n)) :=
        mul_le_mul_of_nonneg_left (rowSum_sq_le hd hsigma p hp m hpsi) hpsi0
      _ ≤ 1 * ((3 * d.U / d.Q1) *
            ∑ n ∈ d.cleanedCommonPProgression p m, fourthDivisorWeight d (m * n)) :=
        mul_le_mul_of_nonneg_right hpsi1 hbase
      _ = _ := one_mul _
  · have hz : d.cleanedAlphaAtom.transposedAtom.commonSmoothWeight m = 0 :=
      not_ne_iff.mp hpsi
    simp only [hz, zero_mul, ne_eq, not_true_eq_false, if_false, mul_zero, le_refl]

/-- Support and signed nonzero shift are established before divisor membership. -/
theorem activeLabel_arithmetic
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma)
    {z : (ℕ × ℕ) × ℕ} (hz : z ∈ activeLabels d) :
    labelProduct z ∈ productCarrier d ∧
      z.1.1 ∈ (shiftDifference d (labelProduct z)).divisors := by
  obtain ⟨hzCarrier, hpsi, hnRow⟩ := Finset.mem_filter.mp hz
  obtain ⟨hpm, _hnCarrier⟩ := Finset.mem_product.mp hzCarrier
  obtain ⟨hp, _hm⟩ := Finset.mem_product.mp hpm
  have hgeom := d.cleaned_commonP_progression_geometry
    hd hsigma z.1.1 hp z.1.2 hpsi ⟨z.2, hnRow⟩
  obtain ⟨hnCarrier, hdelete, hmod⟩ := Finset.mem_filter.mp hnRow
  have hnIcc : z.2 ∈ Icc (Nat.ceil d.U) (Nat.floor (2 * d.U)) := hnCarrier
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hnIcc
  have hnLower : d.U ≤ (z.2 : ℝ) :=
    (Nat.le_ceil d.U).trans (by exact_mod_cast hnlo)
  have hnpos : 0 < z.2 := by
    have : (0 : ℝ) < z.2 := zero_lt_one.trans_le (hd.1.trans hnLower)
    exact_mod_cast this
  have hnUpper : (z.2 : ℝ) ≤ 2 * d.U :=
    (show (z.2 : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by exact_mod_cast hnhi).trans
      (Nat.floor_le (by linarith [hd.1]))
  have hvpos : 0 < labelProduct z := Nat.mul_pos hgeom.2.2.1 hnpos
  have hvUpper : (labelProduct z : ℝ) ≤ 6 * d.scale := by
    calc
      _ = (z.1.2 : ℝ) * z.2 := by simp only [labelProduct, Nat.cast_mul]
      _ ≤ (3 * d.V) * (2 * d.U) :=
        mul_le_mul hgeom.2.1 hnUpper (Nat.cast_nonneg _) (by linarith [hd.2.1])
      _ = _ := by unfold MediumAtom.scale; ring
  have hvne : (labelProduct z : ℤ) ≠ d.residue := by
    intro heq
    apply hdelete
    refine ⟨(z.1.2 : ℤ), ?_⟩
    rw [← heq]
    simp only [labelProduct, Nat.cast_mul, mul_comm]
  have hshift : shiftDifference d (labelProduct z) ≠ 0 :=
    Int.natAbs_ne_zero.mpr (sub_ne_zero.mpr hvne)
  have hpdiv : z.1.1 ∣ shiftDifference d (labelProduct z) := by
    apply Int.natCast_dvd.mp
    simpa only [labelProduct, Nat.cast_mul] using hmod.symm.dvd
  exact ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_Ioc.mpr ⟨hvpos, Nat.le_floor hvUpper⟩, hvne⟩,
    Nat.mem_divisors.mpr ⟨hpdiv, hshift⟩⟩

/-- The actual p selection and each ordered (m,n) factorization are both paid.
No primality and no claim that disjoint dyadic carriers cover p is used. -/
theorem card_productFiber_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma)
    (v : ℕ) (hv : v ∈ productCarrier d) :
    ((activeLabels d).filter (fun z => labelProduct z = v)).card ≤
      v.divisors.card * (shiftDifference d v).divisors.card := by
  have hvpos : 0 < v := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hv).1).1
  have hcard : v.divisorsAntidiagonal.card = v.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact Finset.card_map _
  calc
    _ ≤ (v.divisorsAntidiagonal ×ˢ (shiftDifference d v).divisors).card := by
      apply Finset.card_le_card_of_injOn
        (fun z : (ℕ × ℕ) × ℕ => ((z.1.2, z.2), z.1.1))
      · intro z hz
        obtain ⟨hz, hprod⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_product.mpr ⟨?_, ?_⟩
        · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hvpos.ne'⟩
        · simpa only [hprod] using (activeLabel_arithmetic hd hsigma hz).2
      · intro z _ w _ heq
        exact Prod.ext
          (Prod.ext (congrArg (fun t => t.2) heq) (congrArg (fun t => t.1.1) heq))
          (congrArg (fun t => t.1.2) heq)
    _ = _ := by rw [Finset.card_product, hcard]

/-- Stage 3: a genuine finite fold, even for an arbitrary nonnegative F.
The only hypotheses concern F pointwise; no shifted-moment bound is assumed. -/
theorem sum_activeLabels_le_divisorFold
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma)
    (F : ℕ → ℝ) (hF : ∀ v, 0 ≤ F v) :
    (∑ z ∈ activeLabels d, F (labelProduct z)) ≤
      ∑ v ∈ productCarrier d, tau v * tau (shiftDifference d v) * F v := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := activeLabels d) (t := productCarrier d) (g := labelProduct)
    (fun z hz => (activeLabel_arithmetic hd hsigma hz).1)]
  apply Finset.sum_le_sum
  intro v hv
  calc
    _ = (((activeLabels d).filter (fun z => labelProduct z = v)).card : ℝ) * F v := by
      calc
        _ = ∑ _z ∈ (activeLabels d).filter (fun z => labelProduct z = v), F v := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [(Finset.mem_filter.mp hz).2]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((v.divisors.card * (shiftDifference d v).divisors.card : ℕ) : ℝ) * F v :=
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_productFiber_le hd hsigma v hv) (hF v)
    _ = _ := by simp only [Nat.cast_mul, tau]

end CommonPM2FiniteFold

/-- The complete common-p finite reduction with the actual coefficients.
This is a source proposal, not a certified supplier. -/
theorem MediumAtom.cleaned_commonP_moment_le_finite_divisor_fold
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    CommonPM2FiniteFold.moment d ≤ (3 * d.U / d.Q1) *
      CommonPM2FiniteFold.foldedSum d := by
  apply (CommonPM2FiniteFold.moment_le_activeLabels hd hsigma).trans
  apply mul_le_mul_of_nonneg_left
    (CommonPM2FiniteFold.sum_activeLabels_le_divisorFold hd hsigma
      (CommonPM2FiniteFold.fourthDivisorWeight d)
      (fun _ => by unfold CommonPM2FiniteFold.fourthDivisorWeight; positivity))
  exact div_nonneg
    (mul_nonneg (by norm_num) (zero_le_one.trans hd.1))
    (zero_le_one.trans hd.2.2.1)

/-- The literal M2 outside factor is retained exactly once. -/
theorem MediumAtom.cleaned_commonP_M2_le_finite_divisor_fold
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 < sigma) :
    CommonPM2FiniteFold.outsideEnergy d * CommonPM2FiniteFold.moment d ≤
      CommonPM2FiniteFold.outsideEnergy d *
        ((3 * d.U / d.Q1) * CommonPM2FiniteFold.foldedSum d) := by
  apply mul_le_mul_of_nonneg_left
    (d.cleaned_commonP_moment_le_finite_divisor_fold hd hsigma)
  unfold CommonPM2FiniteFold.outsideEnergy
  exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end

end ImbalancedChen.Part3
