import ImbalancedChen.Part3MediumGenuinePoissonFibre
import ImbalancedChen.Part3OriginalMediumPrincipalFiniteCRT
import ImbalancedChen.Part3OriginalMediumS3ZeroCentering
import ImbalancedChen.Part3OriginalPaperPsiCoprimeCount
import ImbalancedChen.Part3OriginalSamePsiS1OwnedAtlas
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Independent actual MT / restored S3 zero model / centered P constructors.
This base imports no F S1/S2/variance estimate. Coefficients are actual
lambdaTrim, q is primitive-filtered, d uses its actual active support.
The centering is the manuscript's MT+P, not total zero-mode cancellation.
-/
namespace ImbalancedChen.Part3.MediumNativePrincipalSource20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalMediumPrincipalFiniteCRT
open ImbalancedChen.Part3.OriginalMediumS3ZeroCentering
open ImbalancedChen.Part3.TransposedZeroCovariance

/-- Same primitive q and actual active d as the independent E principal
variance object. This is not an unfiltered positive envelope. -/
def nativeQD (atom : MediumAtom) (k : Key) : Finset (ℕ × ℕ) :=
  ((paperPsiNaturalCarrier atom.Q1).filter
    (fun q => q.Coprime atom.residue.natAbs)) ×ˢ activeD atom k

def nativeMT (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ p ∈ nativeQD atom k, (paperQWeight atom p.1 : ℂ) * (atom.V * paperMass : ℂ) *
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      lambdaTrim atom receiver y k p.2 r * star (lambdaTrim atom receiver y k p.2 s) *
        paperPrincipalCoefficient (p.1 * p.2) r s *
        paperCoprimeMean atom.alphaCarrier atom.alpha (p.1 * p.2) r *
        star (paperCoprimeMean atom.alphaCarrier atom.alpha (p.1 * p.2) s)

/-- The full restored principal model from manuscript (13), before the
clean-pair, diagonal and close-pair corrections are reattached. -/
def nativeRestoredZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ p ∈ nativeQD atom k, (paperQWeight atom p.1 : ℂ) * (atom.V * paperMass : ℂ) *
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      lambdaTrim atom receiver y k p.2 r * star (lambdaTrim atom receiver y k p.2 s) *
        (((p.1 * p.2).totient : ℂ) * paperPrincipalCoefficient (p.1 * p.2) r s) *
        ∑ b ∈ reducedResidues (p.1 * p.2),
          paperResidueRow atom.alphaCarrier atom.alpha (p.1 * p.2) r b *
          star (paperResidueRow atom.alphaCarrier atom.alpha (p.1 * p.2) s b)

def nativeCenteredComplex (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ p ∈ nativeQD atom k, (paperQWeight atom p.1 : ℂ) * (atom.V * paperMass : ℂ) *
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      lambdaTrim atom receiver y k p.2 r * star (lambdaTrim atom receiver y k p.2 s) *
        (((p.1 * p.2).totient : ℂ) * paperPrincipalCoefficient (p.1 * p.2) r s) *
        ∑ b ∈ reducedResidues (p.1 * p.2),
          paperCenteredRow atom.alphaCarrier atom.alpha (p.1 * p.2) r b *
          star (paperCenteredRow atom.alphaCarrier atom.alpha (p.1 * p.2) s b)

/-- Real P in precisely the same primitive source convention as E. -/
def nativeP (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℝ :=
  atom.V * paperMass * ∑ p ∈ nativeQD atom k,
    paperQWeight atom p.1 * ((p.1 * p.2).totient : ℝ) *
      paperPrincipalVariance atom.alphaCarrier atom.alpha (p.1 * p.2)
        (dyadicWindow k.w) (lambdaTrim atom receiver y k p.2)

private theorem nativeQD_positive {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) {p : ℕ × ℕ} (hp : p ∈ nativeQD atom k) : 0 < p.1 * p.2 := by
  obtain ⟨hq, hd⟩ := mem_product.mp hp
  have hqLo := (mem_Icc.mp (mem_filter.mp hq).1).1
  have hqceilR : (0 : ℝ) < Nat.ceil (atom.Q1 / 2) :=
    lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
  have hqPos : 0 < p.1 := (by exact_mod_cast hqceilR : 0 < Nat.ceil (atom.Q1 / 2)).trans_le hqLo
  have hdLo := (mem_Ico.mp (mem_filter.mp hd).1).1
  have hdPos : 0 < p.2 := (pow_pos (by norm_num : (0 : ℕ) < 2) k.d).trans_le hdLo
  exact mul_pos hqPos hdPos

/-- This finite identity uses only the actual residue row sum B_r and
phi(ell). No S1/S2 asymptotic or Gram variance estimate is a premise. -/
theorem nativeRestoredZero_eq_MT_add_centered (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) :
    nativeRestoredZero atom receiver y k =
      nativeMT atom receiver y k + nativeCenteredComplex atom receiver y k := by
  unfold nativeRestoredZero nativeMT nativeCenteredComplex
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← mul_add]
  exact congrArg (fun v : ℂ => (paperQWeight atom p.1 : ℂ) *
      (atom.V * paperMass : ℂ) * v)
    (literal_s3_zero_quadratic_centering atom.alphaCarrier atom.alpha
      (nativeQD_positive hQ hp) (dyadicWindow k.w)
      (lambdaTrim atom receiver y k p.2) (paperPrincipalCoefficient (p.1 * p.2)))

private theorem finite_sum_re {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → ℂ) : (∑ a ∈ S, f a).re = ∑ a ∈ S, (f a).re := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [sum_insert ha, ih]

private theorem sum_r_s_b_comm (R T : Finset ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ r ∈ R, ∑ s ∈ R, ∑ b ∈ T, f r s b) =
      ∑ b ∈ T, ∑ r ∈ R, ∑ s ∈ R, f r s b := by
  calc
    _ = ∑ r ∈ R, ∑ b ∈ T, ∑ s ∈ R, f r s b := by
      apply sum_congr rfl
      intro r hr
      exact sum_comm
    _ = _ := sum_comm

private theorem actual_centered_kernel_re (atom : MediumAtom) (ell : ℕ)
    (R : Finset ℕ) (eta : ℕ → ℂ) :
    (∑ r ∈ R, ∑ s ∈ R,
      eta r * star (eta s) * ((ell.totient : ℂ) * paperPrincipalCoefficient ell r s) *
        ∑ b ∈ reducedResidues ell,
          paperCenteredRow atom.alphaCarrier atom.alpha ell r b *
          star (paperCenteredRow atom.alphaCarrier atom.alpha ell s b)).re =
    (ell.totient : ℝ) * paperPrincipalVariance atom.alphaCarrier atom.alpha ell R eta := by
  let F (r s b : ℕ) : ℂ :=
    (eta r * centeredPaperRow atom.alphaCarrier atom.alpha ell r b) *
      star (eta s * centeredPaperRow atom.alphaCarrier atom.alpha ell s b) *
      paperPrincipalCoefficient ell r s
  have hc : (∑ r ∈ R, ∑ s ∈ R,
      eta r * star (eta s) * ((ell.totient : ℂ) * paperPrincipalCoefficient ell r s) *
        ∑ b ∈ reducedResidues ell,
          paperCenteredRow atom.alphaCarrier atom.alpha ell r b *
          star (paperCenteredRow atom.alphaCarrier atom.alpha ell s b)) =
      (ell.totient : ℂ) * ∑ b ∈ reducedResidues ell, ∑ r ∈ R, ∑ s ∈ R, F r s b := by
    calc
      _ = ∑ r ∈ R, ∑ s ∈ R, ∑ b ∈ reducedResidues ell,
          (ell.totient : ℂ) * F r s b := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro r hr
        apply sum_congr rfl
        intro s hs
        apply sum_congr rfl
        intro b hb
        simp only [F, paperCenteredRow, centeredPaperRow, star_mul]
        ring
      _ = ∑ b ∈ reducedResidues ell, ∑ r ∈ R, ∑ s ∈ R,
          (ell.totient : ℂ) * F r s b := sum_r_s_b_comm _ _ _
      _ = _ := by simp only [mul_sum]
  rw [hc]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  simp only [finite_sum_re, paperPrincipalVariance, F]

/-- The independently defined complex centered source has exactly the
real positive-Gram formula nativeP; only finite sum algebra is used. -/
theorem nativeCenteredComplex_re_eq_P (atom : MediumAtom) (receiver y : ℝ) (k : Key) :
    (nativeCenteredComplex atom receiver y k).re = nativeP atom receiver y k := by
  unfold nativeCenteredComplex nativeP
  rw [finite_sum_re, mul_sum]
  apply sum_congr rfl
  intro p hp
  have hk := actual_centered_kernel_re atom (p.1 * p.2) (dyadicWindow k.w)
    (lambdaTrim atom receiver y k p.2)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hk]
  ring

theorem nativeRestoredZero_re_eq_MT_add_P (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (hQ : 0 < atom.Q1) :
    (nativeRestoredZero atom receiver y k).re =
      (nativeMT atom receiver y k).re + nativeP atom receiver y k := by
  rw [nativeRestoredZero_eq_MT_add_centered atom receiver y k hQ]
  simp [nativeCenteredComplex_re_eq_P]

/-- On a unit residue b, the paper A_r(b) condition is (n,r)=1.
The full (n,ell*r)=1 row agrees exactly because n=b mod ell already
supplies the ell-unit condition; no r.Coprime ell gate is required. -/
theorem residueRow_eq_original_A (N : Finset ℕ) (alpha : ℕ → ℂ)
    (ell r b : ℕ) (hb : b ∈ reducedResidues ell) :
    paperResidueRow N alpha ell r b =
      ∑ n ∈ N, if Nat.ModEq ell n b ∧ n.Coprime r then alpha n else 0 := by
  have hbCop := (mem_filter.mp hb).2
  unfold paperResidueRow residueMass
  apply sum_congr rfl
  intro n hn
  by_cases hm : Nat.ModEq ell n b
  · have hnCop : n.Coprime ell := by
      change n.gcd ell = 1
      rw [hm.gcd_eq, hbCop.gcd_eq_one]
    simp [hm, Nat.coprime_mul_iff_right, hnCop]
  · simp [hm]

/-- Positivity is the existing exact FINITE Gram theorem at a constructed
common period. No auxiliary-SW/BDH or final P estimate is used. -/
theorem nativeP_nonneg (atom : MediumAtom) (receiver y : ℝ) (k : Key)
    (hQ : 0 < atom.Q1) (hV : 0 ≤ atom.V) : 0 ≤ nativeP atom receiver y k := by
  unfold nativeP
  apply mul_nonneg (mul_nonneg hV paperMass_nonneg)
  apply sum_nonneg
  intro p hp
  let ell := p.1 * p.2
  let R := dyadicWindow k.w
  let L := ell * ∏ r ∈ R, r
  have hell : 0 < ell := nativeQD_positive hQ hp
  have hR : ∀ r ∈ R, 0 < r := fun r hr =>
    (pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le (mem_Ico.mp hr).1
  have hL : 0 < L := mul_pos hell (prod_pos hR)
  have hcommon : ∀ r ∈ R, ell * r ∣ L := by
    intro r hr
    obtain ⟨s, hs⟩ := dvd_prod_of_mem (fun r : ℕ => r) hr
    refine ⟨s, ?_⟩
    dsimp [L]
    rw [hs]
    ring
  have hP := paper_principal_variance_nonneg atom.alphaCarrier atom.alpha hL hell R hR hcommon
    (lambdaTrim atom receiver y k p.2)
  exact mul_nonneg (mul_nonneg (OriginalGevreyFinalPsi20261028.paperPsi_nonneg _)
    (Nat.cast_nonneg _)) hP

end
end ImbalancedChen.Part3.MediumNativePrincipalSource20261028
