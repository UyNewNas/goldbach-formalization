import ImbalancedChen.Part3ActualWeightedFilteredBDH
import ImbalancedChen.Part3OriginalMediumPrincipalFiniteCRT
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original medium appendix (11),(13),(15): the actual principal variance
is bounded by its own diagonal r-filtered variances. The same exact
paperPrincipalCoefficient and original centered rows are retained.
Outer q,d, literal Lambda and the final asymptotic (15) are not assumed.
-/

namespace ImbalancedChen.Part3.ActualPrincipalGramVarianceBoundSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance
open OriginalMediumPrincipalFiniteCRT
open ActualFilteredPrincipalCharacterVarianceSourceOnly
open ActualFilteredPrimitiveSWSourceOnly
open ActualLowConductorQuotientSumSourceOnly
open ActualWeightedFilteredBDHSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The exact original centered row in the positive kernel is precisely
the actual r-filtered error on a unit class. -/
theorem centeredPaperRow_eq_filteredError (d : MediumAtom) {ell b : ℕ}
    (hell : 0 < ell) (hb : b ∈ reducedResidues ell) (r : ℕ) :
    centeredPaperRow d.alphaCarrier d.alpha ell r b = filteredError d ell r b := by
  have hbc : b.Coprime ell := (Finset.mem_filter.mp hb).2
  have h := actual_centered_mass_eq_auxSWError d (q := ell*r) (delta := ell) (b := b)
    (dvd_mul_right ell r) hbc
  rw [Nat.mul_div_cancel_left r hell] at h
  change centeredPaperRow d.alphaCarrier d.alpha ell r b = d.auxSWError r ell b at h
  rw [h]
  unfold MediumAtom.auxSWError filteredError filteredAP filteredMass
  simp only [Nat.mul_comm]

/-- The actual Gram feature has its original reciprocal-totient norm. -/
theorem principalFeature_norm_le (ell r v : ℕ) :
    ‖principalFeature ell r v‖ ≤ 1/((ell*r).totient : ℝ) := by
  unfold principalFeature
  by_cases hg : v.Coprime (ell*r)
  · rw [if_pos hg,norm_div,norm_one,Complex.norm_natCast]
  · rw [if_neg hg,norm_zero]
    positivity

/-- Finite Cauchy on the original rough-factor carrier. -/
theorem principalGramEnergy_le_diagonal (L ell : ℕ) (R : Finset ℕ) (coeff : ℕ → ℂ) :
    principalGramEnergy L ell R coeff ≤
      (L : ℝ)*(R.card : ℝ)*
        (∑ r ∈ R, ‖coeff r‖^2/((ell*r).totient : ℝ)^2) := by
  have hpoint (v : ℕ) :
      ‖∑ r ∈ R, coeff r*principalFeature ell r v‖^2 ≤
        (R.card : ℝ)*(∑ r ∈ R, ‖coeff r‖^2/((ell*r).totient : ℝ)^2) := by
    refine (norm_finset_sum_sq_le_card_mul_sum_norm_sq R
      (fun r => coeff r*principalFeature ell r v)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro r hr
    rw [norm_mul,mul_pow]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (principalFeature_norm_le ell r v) 2
    have h := mul_le_mul_of_nonneg_left hh (sq_nonneg (‖coeff r‖))
    simpa only [div_pow,one_pow,mul_one_div] using h
  unfold principalGramEnergy
  calc
    _ ≤ ∑ _v ∈ Finset.Ioc 0 L, (R.card : ℝ)*
        (∑ r ∈ R, ‖coeff r‖^2/((ell*r).totient : ℝ)^2) :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = _ := by simp [mul_assoc]

/-- The actual paper quadratic form is the finite Gram average, hence its
Cauchy upper bound is independent of the arbitrarily chosen common period. -/
theorem paper_principal_quadratic_le_diagonal
    {L ell : ℕ} (hL : 0 < L) (hell : 0 < ell)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 0 < r)
    (hcommon : ∀ r ∈ R, ell*r ∣ L) (coeff : ℕ → ℂ) :
    (∑ r ∈ R, ∑ s ∈ R,
      coeff r*star (coeff s)*paperPrincipalCoefficient ell r s).re ≤
      (R.card : ℝ)*(∑ r ∈ R, ‖coeff r‖^2/((ell*r).totient : ℝ)^2) := by
  let E := principalGramEnergy L ell R coeff
  let Q : ℂ := ∑ r ∈ R, ∑ s ∈ R,
    coeff r*star (coeff s)*paperPrincipalCoefficient ell r s
  have hid : (E : ℂ) = (L : ℂ)*Q := by
    dsimp only [E]
    rw [principal_gram_expansion]
    dsimp only [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [principal_kernel_eq_paper_coefficient hell (hR r hr) (hR s hs)
      (hcommon r hr) (hcommon s hs)]
    ring
  have hr := congrArg Complex.re hid
  simp only [Complex.ofReal_re,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero] at hr
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hQ : Q.re = E/(L : ℝ) := (eq_div_iff hLR.ne').mpr (by nlinarith)
  change Q.re ≤ _
  rw [hQ]
  calc
    _ ≤ ((L : ℝ)*(R.card : ℝ)*
        (∑ r ∈ R, ‖coeff r‖^2/((ell*r).totient : ℝ)^2))/(L : ℝ) :=
      div_le_div_of_nonneg_right (principalGramEnergy_le_diagonal L ell R coeff) hLR.le
    _ = _ := by field_simp [hLR.ne']; ring

/-- Principal positive Gram insertion into the actual filtered variance.
The r-dependent native density and arbitrary signed eta remain explicit;
no positivity of eta or an already-proved principal bound is required. -/
theorem actual_paperPrincipalVariance_le
    (d : MediumAtom) {L ell : ℕ} (hL : 0 < L) (hell : 0 < ell)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 0 < r)
    (hcommon : ∀ r ∈ R, ell*r ∣ L) (eta : ℕ → ℂ) :
    paperPrincipalVariance d.alphaCarrier d.alpha ell R eta ≤
      (R.card : ℝ)*
        (∑ r ∈ R, ‖eta r‖^2*filteredVariance d ell r/((ell*r).totient : ℝ)^2) := by
  unfold paperPrincipalVariance
  calc
    _ ≤ ∑ b ∈ reducedResidues ell, (R.card : ℝ)*
        (∑ r ∈ R,
          ‖eta r*centeredPaperRow d.alphaCarrier d.alpha ell r b‖^2 /
            ((ell*r).totient : ℝ)^2) :=
      Finset.sum_le_sum (fun b hb => paper_principal_quadratic_le_diagonal
        hL hell R hR hcommon (fun r => eta r*centeredPaperRow d.alphaCarrier d.alpha ell r b))
    _ = (R.card : ℝ)*∑ b ∈ reducedResidues ell,
        ∑ r ∈ R, ‖eta r*centeredPaperRow d.alphaCarrier d.alpha ell r b‖^2 /
          ((ell*r).totient : ℝ)^2 := by rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      unfold filteredVariance
      rw [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro b hb
      rw [centeredPaperRow_eq_filteredError d hell hb r,norm_mul,mul_pow]

/-- A concrete common period for the original finite rough carrier. It is
only an exact Gram normalization and never an analytic error scale. -/
def actualCommonPeriod (ell : ℕ) (R : Finset ℕ) : ℕ := ell*(∏ r ∈ R, r)

theorem actual_paperPrincipalVariance_bound
    (d : MediumAtom) {ell : ℕ} (hell : 0 < ell)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 0 < r) (eta : ℕ → ℂ) :
    paperPrincipalVariance d.alphaCarrier d.alpha ell R eta ≤
      (R.card : ℝ)*
        (∑ r ∈ R, ‖eta r‖^2*filteredVariance d ell r/((ell*r).totient : ℝ)^2) := by
  have hL : 0 < actualCommonPeriod ell R :=
    Nat.mul_pos hell (Finset.prod_pos (fun r hr => hR r hr))
  have hcommon : ∀ r ∈ R, ell*r ∣ actualCommonPeriod ell R := by
    intro r hr
    obtain ⟨k,hk⟩ := Finset.dvd_prod_of_mem (fun r : ℕ => r) hr
    refine ⟨k,?_⟩
    unfold actualCommonPeriod
    rw [hk]
    ring
  exact actual_paperPrincipalVariance_le d hL hell R hR hcommon eta

end
end ImbalancedChen.Part3.ActualPrincipalGramVarianceBoundSourceOnly
