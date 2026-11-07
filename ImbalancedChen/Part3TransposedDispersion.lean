import ImbalancedChen.Part3CommonPoisson
import ImbalancedChen.Part3FactorFiberDivisor

/-!
# Actual transposed complex dispersion, with SW on the paired side

This is a new dispersion object. Its smooth variable has length original V,
and its paired coefficient is original alpha, extended by zero from the
original interval to the full U-dyadic carrier. The signed error, moving
signed residue, three complex gamma labels and physical moduli are exact.

No MediumAdmissible assertion is made for the transposed atom: original
beta need not be one-bounded or rough. Generic finite Cauchy and dispersion
identities apply without that assertion. Its actual L2 cost is paid by the
fixed divisor moment at original length 2V. The new common smooth weight,
constructed CRT output and full Poisson series are supplied here directly
from original V>=1 and the original active-gamma primitive gates.

The original UniformAuxiliarySW error is exactly the auxiliary error of
this paired coefficient. This does not yet assert an external SW-family
quantifier conversion, zero-mode payment, or a nonzero-frequency estimate.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Set
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The interval is moved into the paired coefficient, without losing any
original alpha point or adding a nonzero coefficient outside that interval. -/
def MediumAtom.transposedAtom (d : MediumAtom) : MediumAtom :=
  { d with
    U := d.V
    V := d.U
    intervalLo := -1
    intervalHi := (Nat.floor (2 * d.V) : ℝ)
    alpha := d.beta
    beta := fun n ↦ if n ∈ d.alphaCarrier then d.alpha n else 0 }

theorem MediumAtom.transposedAtom_scale (d : MediumAtom) :
    d.transposedAtom.scale = d.scale := by
  unfold MediumAtom.scale MediumAtom.transposedAtom
  exact mul_comm _ _

theorem MediumAtom.transposedAtom_alphaCarrier (d : MediumAtom) :
    d.transposedAtom.alphaCarrier = d.betaCarrier := by
  ext n
  change n ∈ (Finset.Icc (Nat.ceil d.V) (Nat.floor (2 * d.V))).filter
    (fun k : ℕ ↦ (-1 : ℝ) < (k : ℝ) ∧ (k : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ)) ↔
      n ∈ Finset.Icc (Nat.ceil d.V) (Nat.floor (2 * d.V))
  rw [Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hn
    refine ⟨hn, ?_, ?_⟩
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · exact_mod_cast (Finset.mem_Icc.mp hn).2

theorem MediumAtom.transposedAtom_betaCarrier (d : MediumAtom) :
    d.transposedAtom.betaCarrier = factorCarrier d.U := rfl

/-- Exact finite extension by zero of the original interval coefficient. -/
theorem MediumAtom.sum_transposedBeta_mul (d : MediumAtom) (f : ℕ → ℂ) :
    (∑ n ∈ d.transposedAtom.betaCarrier, d.transposedAtom.beta n * f n) =
      ∑ n ∈ d.alphaCarrier, d.alpha n * f n := by
  change (∑ n ∈ factorCarrier d.U,
    (if n ∈ d.alphaCarrier then d.alpha n else 0) * f n) = _
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hsub : d.alphaCarrier ⊆ factorCarrier d.U := Finset.filter_subset _ _
  have heq : (factorCarrier d.U).filter (fun n ↦ n ∈ d.alphaCarrier) = d.alphaCarrier := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hsub h, h⟩⟩
  rw [heq]

private theorem primitiveKernel_comm (a : ℤ) (q m n : ℕ) :
    complexPrimitiveKernel a q m n = complexPrimitiveKernel a q n m := by
  simp only [complexPrimitiveKernel, Nat.mul_comm]

/-- Exact Fubini and multiplication commutativity, before taking any norm. -/
theorem MediumAtom.transposedAtom_discrepancy (d : MediumAtom) (q : ℕ) :
    d.transposedAtom.discrepancy q = d.discrepancy q := by
  change (∑ m ∈ d.transposedAtom.alphaCarrier, ∑ n ∈ d.transposedAtom.betaCarrier,
    d.transposedAtom.alpha m * d.transposedAtom.beta n *
      complexPrimitiveKernel d.residue q m n) =
        ∑ n ∈ d.alphaCarrier, ∑ m ∈ d.betaCarrier,
          d.alpha n * d.beta m * complexPrimitiveKernel d.residue q n m
  rw [d.transposedAtom_alphaCarrier]
  calc
    _ = ∑ m ∈ d.betaCarrier, ∑ n ∈ d.transposedAtom.betaCarrier,
        d.transposedAtom.beta n * (d.beta m * complexPrimitiveKernel d.residue q n m) := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      change d.beta m * d.transposedAtom.beta n *
        complexPrimitiveKernel d.residue q m n = _
      rw [primitiveKernel_comm]
      ring
    _ = ∑ m ∈ d.betaCarrier, ∑ n ∈ d.alphaCarrier,
        d.alpha n * (d.beta m * complexPrimitiveKernel d.residue q n m) := by
      apply Finset.sum_congr rfl
      intro m _
      exact d.sum_transposedBeta_mul _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro m _
      ring

theorem MediumAtom.transposedAtom_signedError (d : MediumAtom) :
    d.transposedAtom.signedError = d.signedError := by
  unfold MediumAtom.signedError
  change (∑ q1 ∈ factorCarrier d.Q1, ∑ q2 ∈ factorCarrier d.Q2,
    ∑ q3 ∈ factorCarrier d.Q3,
      d.gamma1 q1 * d.gamma2 q2 * d.gamma3 q3 *
        d.transposedAtom.discrepancy (q1 * q2 * q3)) = _
  simp only [MediumAtom.transposedAtom_discrepancy]

def MediumAtom.transposedPairedSWError (d : MediumAtom) (k q b : ℕ) : ℂ :=
  (∑ n ∈ d.transposedAtom.betaCarrier,
    if Nat.ModEq q n b ∧ Nat.Coprime n k then d.transposedAtom.beta n else 0) -
  (∑ n ∈ d.transposedAtom.betaCarrier,
    if Nat.Coprime n (k * q) then d.transposedAtom.beta n else 0) / (Nat.totient q : ℂ)

private theorem sum_transposedBeta_ite (d : MediumAtom) (p : ℕ → Prop) :
    (∑ n ∈ d.transposedAtom.betaCarrier, if p n then d.transposedAtom.beta n else 0) =
      ∑ n ∈ d.alphaCarrier, if p n then d.alpha n else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    d.sum_transposedBeta_mul (fun n ↦ if p n then 1 else 0)

/-- The SW hypothesis is now on the coefficient which is actually paired. -/
theorem MediumAtom.transposedPairedSWError_eq_auxSWError (d : MediumAtom) (k q b : ℕ) :
    d.transposedPairedSWError k q b = d.auxSWError k q b := by
  unfold MediumAtom.transposedPairedSWError MediumAtom.auxSWError
  have hfirst :
      (∑ n ∈ d.transposedAtom.betaCarrier,
        if Nat.ModEq q n b ∧ Nat.Coprime n k then d.transposedAtom.beta n else 0) =
      ∑ n ∈ d.alphaCarrier, if Nat.ModEq q n b ∧ Nat.Coprime n k then d.alpha n else 0 := by
    convert sum_transposedBeta_ite d (fun n : ℕ ↦ Nat.ModEq q n b ∧ Nat.Coprime n k) using 1
    all_goals
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : Nat.ModEq q n b ∧ Nat.Coprime n k
      · simp only [if_pos hn]
      · simp only [if_neg hn]
  have hsecond :
      (∑ n ∈ d.transposedAtom.betaCarrier,
        if Nat.Coprime n (k * q) then d.transposedAtom.beta n else 0) =
      ∑ n ∈ d.alphaCarrier, if Nat.Coprime n (k * q) then d.alpha n else 0 := by
    convert sum_transposedBeta_ite d (fun n : ℕ ↦ Nat.Coprime n (k * q)) using 1
    all_goals
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : Nat.Coprime n (k * q)
      · simp only [if_pos hn]
      · simp only [if_neg hn]
  exact congrArg₂ (fun z w : ℂ ↦ z - w / (Nat.totient q : ℂ)) hfirst hsecond

theorem uniformAuxiliarySW_transposedPairedBeta {ι : Type*}
    (F : ι → MediumAtom) (C0 : ℕ) (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
      ∀ i : ι, x0 ≤ (F i).scale → ∀ k q b : ℕ,
        1 ≤ k → 1 ≤ q → Nat.Coprime b q →
        ‖(F i).transposedPairedSWError k q b‖ ≤
          C * (F i).U * ((k.divisors.card : ℝ) ^ C0) / (Real.log (F i).scale) ^ A := by
  simpa only [UniformAuxiliarySW, MediumAtom.transposedPairedSWError_eq_auxSWError] using hSW

/-- The actual divisor square moment of original beta; B stays fixed. -/
theorem mediumAdmissible_beta_norm_sq_sum_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) ≤
      2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1) := by
  have hsub : d.betaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.V)) := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hceil : 1 ≤ Nat.ceil d.V := by exact_mod_cast hd.2.1.trans (Nat.le_ceil d.V)
    exact Finset.mem_Ioc.mpr ⟨by omega, hhi⟩
  apply sum_alpha_sq_le_fouvryTau (k := 2 ^ B)
    (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero B (by norm_num)))
    (by linarith [hd.2.1] : 1 ≤ 2 * d.V) d.betaCarrier hsub (fun n ↦ ‖d.beta n‖)
  intro n hn
  have hnpos := (Finset.mem_Ioc.mp (hsub hn)).1
  have hbeta : ‖d.beta n‖ ≤ (n.divisors.card : ℝ) ^ B := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hbeta, _⟩ := hd
    exact hbeta n hn
  rw [abs_norm]
  exact hbeta.trans (by
    rw [← fouvryTau_two]
    exact_mod_cast fouvryTau_pow_le 2 B hnpos.ne')

/-- The new weight is fixed at V, independently of all physical labels. -/
theorem MediumAtom.transposedSmoothWeight_eq_one_on_beta
    {d : MediumAtom} (hV : 1 ≤ d.V) {n : ℕ} (hn : n ∈ d.betaCarrier) :
    d.transposedAtom.commonSmoothWeight n = 1 := by
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  have hlo : d.V ≤ (n : ℝ) := (Nat.le_ceil d.V).trans (by exact_mod_cast hnlo)
  have hhi : (n : ℝ) ≤ 2 * d.V :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.V) : ℝ) by exact_mod_cast hnhi).trans
      (Nat.floor_le (by linarith : 0 ≤ 2 * d.V))
  exact CommonSmoothCutoff.scaledDyadicCutoff_eq_one (M := d.V) (by linarith) ⟨hlo, hhi⟩

theorem MediumAtom.transposedSmoothWeight_support_subset
    {d : MediumAtom} (hV : 1 ≤ d.V) {n : ℕ}
    (hn : d.transposedAtom.commonSmoothWeight n ≠ 0) :
    n ∈ d.transposedAtom.commonSmoothCarrier := by
  have hV0 : 0 < d.V := lt_of_lt_of_le zero_lt_one hV
  have hs : (n : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.V) :=
    subset_closure hn
  have hupper := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset hV0 hs).2
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.zero_le _, ?_⟩
  exact_mod_cast hupper.trans (Nat.le_ceil (3 * d.V))

/-- Finite Cauchy in the original beta variable, with its literal L2 cost. -/
theorem MediumAtom.signedError_norm_sq_le_transposedCommonSmoothDispersion
    {d : MediumAtom} (hV : 1 ≤ d.V) :
    ‖d.signedError‖ ^ 2 ≤
      (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
        (d.transposedAtom.complexDispersionW d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight -
          2 * d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight +
          d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight) := by
  have h := d.transposedAtom.signedError_norm_sq_le_smoothedComplexDispersion
    d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight
    (by
      rw [d.transposedAtom_alphaCarrier]
      intro n hn
      apply d.transposedSmoothWeight_support_subset hV
      rw [d.transposedSmoothWeight_eq_one_on_beta hV hn]
      norm_num)
    (fun n _ ↦ d.transposedAtom.commonSmoothWeight_nonneg n)
    (by
      rw [d.transposedAtom_alphaCarrier]
      intro n hn
      exact (d.transposedSmoothWeight_eq_one_on_beta hV hn).ge)
  rw [d.transposedAtom_signedError, d.transposedAtom_alphaCarrier] at h
  exact h

/-- The finite divisor moment pays the Cauchy cost; no one-bound is added
to original beta and no MediumAdmissible premise is imposed on the swap. -/
theorem MediumAtom.signedError_norm_sq_le_transposedMomentDispersion
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ‖d.signedError‖ ^ 2 ≤
      (2 * d.V * (1 + Real.log (2 * d.V)) ^ ((2 ^ B) ^ 2 - 1)) *
        (d.transposedAtom.complexDispersionW d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight -
          2 * d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight +
          d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
            d.transposedAtom.commonSmoothWeight) := by
  exact (d.signedError_norm_sq_le_transposedCommonSmoothDispersion hd.2.1).trans
    (mul_le_mul_of_nonneg_right (mediumAdmissible_beta_norm_sq_sum_le hd)
      (d.transposedAtom.complex_dispersion_nonneg _ _
        (fun n _ ↦ d.transposedAtom.commonSmoothWeight_nonneg n)))

private theorem transposed_factor_modulus_pos
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) : 0 < complexFactorModulus r := by
  obtain ⟨_, _, hQ1, hQ2, hQ3, _⟩ := hd
  have factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ} (hq : q ∈ factorCarrier Q) : 0 < q := by
    have hlo := (Finset.mem_Icc.mp hq).1
    have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
    omega
  obtain ⟨hr1, hr23⟩ := Finset.mem_product.mp hr
  obtain ⟨hr2, hr3⟩ := Finset.mem_product.mp hr23
  exact Nat.mul_pos (Nat.mul_pos (factor_pos hQ1 hr1) (factor_pos hQ2 hr2))
    (factor_pos hQ3 hr3)

private theorem transposed_active_residue_gcd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {r : ℕ × ℕ × ℕ}
    (hr : r ∈ d.complexFactorLabels) (hgamma : d.complexFactorGamma r ≠ 0) :
    Int.gcd d.residue (complexFactorModulus r) = 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hd
  obtain ⟨hr1, hr23⟩ := Finset.mem_product.mp hr
  obtain ⟨hr2, hr3⟩ := Finset.mem_product.mp hr23
  have hg : d.gamma1 r.1 * d.gamma2 r.2.1 * d.gamma3 r.2.2 ≠ 0 := hgamma
  obtain ⟨hg12, hg3⟩ := mul_ne_zero_iff.mp hg
  obtain ⟨hg1, hg2⟩ := mul_ne_zero_iff.mp hg12
  have hcop : (complexFactorModulus r).Coprime d.residue.natAbs :=
    (((h1 r.1 hr1).2 hg1).mul_left ((h2 r.2.1 hr2).2 hg2)).mul_left
      ((h3 r.2.2 hr3).2 hg3)
  simpa only [Int.gcd, Int.natAbs_natCast, Nat.gcd_comm] using hcop.gcd_eq_one

/-- Constructed CRT for the new W, using original physical primitive gates. -/
theorem MediumAtom.transposedDispersionW_eq_constructedCRT
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (S : Finset ℕ) (w : ℕ → ℝ) :
    (d.transposedAtom.complexDispersionW S w : ℂ) =
      ∑ l ∈ d.transposedAtom.complexRowLabels, ∑ l' ∈ d.transposedAtom.complexRowLabels,
        d.transposedAtom.complexBetaCoefficient l * star (d.transposedAtom.complexBetaCoefficient l') *
          (ComplexCRT.constructedProgressionWeight S w d.residue
            (complexFactorModulus l.1) (complexFactorModulus l'.1) l.2 l'.2 : ℂ) := by
  rw [MediumAtom.complexDispersionW_eq_productProgressions]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro l' hl'
  have hf : l.1 ∈ d.complexFactorLabels := (Finset.mem_product.mp hl).1
  have hf' : l'.1 ∈ d.complexFactorLabels := (Finset.mem_product.mp hl').1
  by_cases hg : d.complexFactorGamma l.1 = 0
  · simp only [MediumAtom.complexBetaCoefficient, MediumAtom.complexFactorGamma,
      MediumAtom.transposedAtom] at hg ⊢
    simp only [hg, zero_mul]
  by_cases hg' : d.complexFactorGamma l'.1 = 0
  · simp only [MediumAtom.complexBetaCoefficient, MediumAtom.complexFactorGamma,
      MediumAtom.transposedAtom] at hg' ⊢
    simp only [hg', zero_mul, star_zero, mul_zero]
  rw [show d.transposedAtom.residue = d.residue from rfl]
  rw [ComplexCRT.productProgressionWeight_eq_constructed S w
    (transposed_factor_modulus_pos hd hf) (transposed_active_residue_gcd hd hf hg)
    (transposed_active_residue_gcd hd hf' hg')]

/-- A new full Poisson identity at original V, on one fixed carrier. -/
theorem MediumAtom.transposedDispersionW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.transposedAtom.complexDispersionW d.transposedAtom.commonSmoothCarrier
      d.transposedAtom.commonSmoothWeight : ℂ) =
        d.transposedAtom.complexCRTSmoothZeroPart + d.transposedAtom.complexCRTSmoothNonzeroPart := by
  rw [d.transposedDispersionW_eq_constructedCRT hd]
  unfold MediumAtom.complexCRTSmoothZeroPart MediumAtom.complexCRTSmoothNonzeroPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l' hl'
  unfold ComplexCRT.constructedProgressionWeight
  by_cases hc : ComplexCRT.Compatible (complexFactorModulus l.1)
      (complexFactorModulus l'.1) l.2 l'.2
  · simp only [hc, if_true]
    have hf : l.1 ∈ d.complexFactorLabels := (Finset.mem_product.mp hl).1
    have hf' : l'.1 ∈ d.complexFactorLabels := (Finset.mem_product.mp hl').1
    have hD : 0 < (complexFactorModulus l.1).lcm (complexFactorModulus l'.1) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (transposed_factor_modulus_pos hd hf).ne'
        (transposed_factor_modulus_pos hd hf').ne')
    have he := CommonSmoothCutoff.scaledDyadicCutoff_finset_progression_eq_main_add_fourier
      (lt_of_lt_of_le zero_lt_one hd.2.1) d.transposedAtom.commonSmoothCarrier
      (fun m hm ↦ d.transposedSmoothWeight_support_subset hd.2.1 hm) hD
      (ComplexCRT.residue (complexFactorModulus l.1)
        (complexFactorModulus l'.1) l.2 l'.2 d.residue)
    simp only [MediumAtom.commonSmoothWeight, MediumAtom.transposedAtom] at he ⊢
    rw [he, Complex.ofReal_add]
    ring
  · simp only [hc, if_false, Complex.ofReal_zero, mul_zero, add_zero]

/-- The actual new dispersion center still retains literal V and U. -/
theorem MediumAtom.transposed_dispersion_identity_with_commonPoisson
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ n ∈ d.transposedAtom.commonSmoothCarrier,
      d.transposedAtom.commonSmoothWeight n * ‖d.transposedAtom.complexCenteredRow n‖ ^ 2 : ℝ) : ℂ) =
      (d.transposedAtom.complexCRTSmoothZeroPart -
        2 * (d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) +
        (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ)) + d.transposedAtom.complexCRTSmoothNonzeroPart := by
  rw [MediumAtom.complex_dispersion_identity]
  push_cast
  rw [d.transposedDispersionW_eq_zero_add_nonzero hd]
  ring

end

end ImbalancedChen.Part3
