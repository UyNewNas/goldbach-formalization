import ImbalancedChen.Part3MediumNativePrincipalSource
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Actual full physical CRT zero pair and its clean normalization. Clean means
ONLY (r,s)=1 and (s,ell)=1; r may share arbitrary prime factors with ell.
The nonclean difference is a displayed finite source correction, never a
claimed zero. MT+P centering does not use a variance bound.
-/
namespace ImbalancedChen.Part3.MediumActualS3ZeroCentering20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
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

/-- Literal complete-lcm CRT zero pair before any clean deletion. -/
def crtZeroPair (atom : MediumAtom) (ell r s : ℕ) : ℂ :=
  (atom.V * paperMass : ℂ) / (((ell * r).lcm (ell * s) : ℕ) : ℂ) *
    compatibleMass atom.alphaCarrier atom.alpha (ell * r) (ell * s)

/-- Precisely the original rough clean gate. In particular no (r,ell)=1. -/
def CleanRough (ell r s : ℕ) : Prop := r.Coprime s ∧ s.Coprime ell

def residueZeroModelPair (atom : MediumAtom) (ell r s : ℕ) : ℂ :=
  ((ell.totient : ℂ) * paperPrincipalCoefficient ell r s) *
    ∑ b ∈ reducedResidues ell,
      paperResidueRow atom.alphaCarrier atom.alpha ell r b *
        star (paperResidueRow atom.alphaCarrier atom.alpha ell s b)

/-- The actual finite CRT zero coefficient equals the paper's full A_r
row expression on the original clean gate, even when r shares ell primes. -/
theorem crtZeroPair_clean (atom : MediumAtom) {ell r s : ℕ}
    (hell : 0 < ell) (hr : 0 < r) (hs : 0 < s) (hc : CleanRough ell r s) :
    crtZeroPair atom ell r s =
      (atom.V * paperMass : ℂ) * residueZeroModelPair atom ell r s := by
  have hg : (ell * r).gcd (ell * s) = ell := by
    rw [Nat.gcd_mul_left, hc.1.gcd_eq_one, mul_one]
  have hL : (ell * r).lcm (ell * s) = ell * r * s := by
    rw [Nat.lcm_mul_left, hc.1.lcm_eq_mul]
    ring
  unfold crtZeroPair residueZeroModelPair
  rw [compatibleMass_eq_residue_products _ _ (mul_pos hell hr), hg,
    clean_paper_coefficient hell hr hs hc.1 hc.2, hL]
  simp only [paperResidueRow]
  ring

/-- Explicit two-original-alpha-label form of the true zero packet.
No coprime residue class or zero mass is assumed by this dictionary. -/
theorem crtZeroPair_eq_actual_zero_nsum (atom : MediumAtom) (ell r s : ℕ) :
    crtZeroPair atom ell r s =
      ∑ n1 ∈ atom.alphaCarrier, ∑ n2 ∈ atom.alphaCarrier,
        atom.alpha n1 * star (atom.alpha n2) *
          (if ComplexCRT.Compatible (ell * r) (ell * s) n1 n2 then
            (atom.V / (((ell * r).lcm (ell * s) : ℕ) : ℝ)) •
              (𝓕 OriginalGevreyActualPsiFourierIBP20261028.paperPsiComplex) 0
           else 0) := by
  unfold crtZeroPair compatibleMass
  rw [paperPsi_fourier_zero]
  simp only [mul_sum]
  apply sum_congr rfl
  intro n1 hn1
  apply sum_congr rfl
  intro n2 hn2
  by_cases hc : ComplexCRT.Compatible (ell * r) (ell * s) n1 n2
  · simp only [if_pos hc, Complex.real_smul]
    push_cast
    ring
  · simp [hc]

def nativeCRTZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ p ∈ nativeQD atom k, (paperQWeight atom p.1 : ℂ) *
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      lambdaTrim atom receiver y k p.2 r * star (lambdaTrim atom receiver y k p.2 s) *
        crtZeroPair atom (p.1 * p.2) r s

/-- This is the genuine NONCLEAN source difference, term by term over its
actual r,s complement. Its smallness is not part of the definition. -/
def roughReplacementCorrection (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ p ∈ nativeQD atom k, (paperQWeight atom p.1 : ℂ) *
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      if ¬CleanRough (p.1 * p.2) r s then
        lambdaTrim atom receiver y k p.2 r * star (lambdaTrim atom receiver y k p.2 s) *
          (crtZeroPair atom (p.1 * p.2) r s -
            (atom.V * paperMass : ℂ) * residueZeroModelPair atom (p.1 * p.2) r s)
      else 0

private theorem qd_positive {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) {p : ℕ × ℕ} (hp : p ∈ nativeQD atom k) : 0 < p.1 * p.2 := by
  obtain ⟨hq, hd⟩ := mem_product.mp hp
  have hqLo := (mem_Icc.mp (mem_filter.mp hq).1).1
  have hqR : (0 : ℝ) < Nat.ceil (atom.Q1 / 2) :=
    lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
  have hqN : 0 < p.1 := (by exact_mod_cast hqR : 0 < Nat.ceil (atom.Q1 / 2)).trans_le hqLo
  have hdN : 0 < p.2 := (pow_pos (by norm_num : (0 : ℕ) < 2) k.d).trans_le
    (mem_Ico.mp (mem_filter.mp hd).1).1
  exact mul_pos hqN hdN

/-- Full actual CRT zero = restored model plus the explicit rough-clean
replacement correction. This is not a claimed exact clean restoration. -/
theorem nativeCRTZero_eq_restored_add_roughCorrection (atom : MediumAtom)
    (receiver y : ℝ) (k : Key) (hQ : 0 < atom.Q1) :
    nativeCRTZero atom receiver y k = nativeRestoredZero atom receiver y k +
      roughReplacementCorrection atom receiver y k := by
  unfold nativeCRTZero nativeRestoredZero roughReplacementCorrection
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [mul_sum]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro r hr
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro s hs
  have hr0 : 0 < r := (pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le (mem_Ico.mp hr).1
  have hs0 : 0 < s := (pow_pos (by norm_num : (0 : ℕ) < 2) k.w).trans_le (mem_Ico.mp hs).1
  by_cases hc : CleanRough (p.1 * p.2) r s
  · rw [if_neg (not_not.mpr hc), crtZeroPair_clean atom (qd_positive hQ hp) hr0 hs0 hc]
    unfold residueZeroModelPair
    ring
  · rw [if_pos hc]
    unfold residueZeroModelPair
    ring

/-- Correct actual CRT-zero centering with the nonclean correction kept.
No P estimate, no unfiltered envelope and no total cancellation is used. -/
theorem nativeCRTZero_re_eq_MT_P_roughCorrection (atom : MediumAtom)
    (receiver y : ℝ) (k : Key) (hQ : 0 < atom.Q1) :
    (nativeCRTZero atom receiver y k).re = (nativeMT atom receiver y k).re +
      nativeP atom receiver y k + (roughReplacementCorrection atom receiver y k).re := by
  rw [nativeCRTZero_eq_restored_add_roughCorrection atom receiver y k hQ]
  simp only [Complex.add_re, nativeRestoredZero_re_eq_MT_add_P atom receiver y k hQ]

/-- This source is defined directly on E's genuine Poisson fibre,
with E's actual lambda, q primitive filter and physical complete lcm. -/
def nativeGenuineZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k,
    headCoefficient atom receiver y k v * zeroMode atom v

private theorem actual_alpha_pair_zero_sum (atom : MediumAtom) (receiver y : ℝ)
    (k : Key) (q d : ℕ) :
    (∑ r ∈ dyadicWindow k.w, ∑ n1 ∈ atom.alphaCarrier,
      ∑ s ∈ dyadicWindow k.w, ∑ n2 ∈ atom.alphaCarrier,
        headCoefficient atom receiver y k ((q,d),((r,n1),(s,n2))) *
          zeroMode atom ((q,d),((r,n1),(s,n2)))) =
      (paperQWeight atom q : ℂ) *
        ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
          lambdaTrim atom receiver y k d r * star (lambdaTrim atom receiver y k d s) *
            crtZeroPair atom (q*d) r s := by
  calc
    _ = ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
        ∑ n1 ∈ atom.alphaCarrier, ∑ n2 ∈ atom.alphaCarrier,
          headCoefficient atom receiver y k ((q,d),((r,n1),(s,n2))) *
            zeroMode atom ((q,d),((r,n1),(s,n2))) := by
      apply sum_congr rfl
      intro r hr
      exact sum_comm
    _ = _ := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro r hr
      apply sum_congr rfl
      intro s hs
      rw [crtZeroPair_eq_actual_zero_nsum]
      simp only [mul_sum]
      apply sum_congr rfl
      intro n1 hn1
      apply sum_congr rfl
      intro n2 hn2
      unfold headCoefficient zeroMode compatible completeL leftModulus rightModulus
      ring

/-- Actual E zero source is the complete CRT zero expression. The
nonprimitive d complement is proved zero using the original gamma gate;
it is not replaced by an independently chosen active-d hypothesis. -/
theorem nativeGenuineZero_eq_nativeCRTZero
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (receiver y : ℝ) (k : Key) :
    nativeGenuineZero atom receiver y k = nativeCRTZero atom receiver y k := by
  unfold nativeGenuineZero nativeCRTZero nativeQD fibreCarrier
  simp only [innerCarrier, sum_product]
  simp_rw [actual_alpha_pair_zero_sum]
  apply sum_congr rfl
  intro q hq
  symm
  apply sum_subset (filter_subset _ _)
  intro d hd hn
  have hbad : ¬d.Coprime atom.residue.natAbs := by
    intro hc
    exact hn (mem_filter.mpr ⟨hd,hc⟩)
  have hz (r : ℕ) : lambdaTrim atom receiver y k d r = 0 :=
    lambdaTrim_zero_of_nonprimitive atom receiver y k d r hA hbad
  simp [hz]

/-- Actual all-label zero-mode source, with every nonclean rough-pair
replacement term retained, centers to the correct primitive MT+P. -/
theorem nativeGenuineZero_re_eq_MT_P_correction
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (receiver y : ℝ) (k : Key) :
    (nativeGenuineZero atom receiver y k).re =
      (nativeMT atom receiver y k).re + nativeP atom receiver y k +
        (roughReplacementCorrection atom receiver y k).re := by
  rw [nativeGenuineZero_eq_nativeCRTZero hA]
  exact nativeCRTZero_re_eq_MT_P_roughCorrection atom receiver y k
    (zero_lt_one.trans_le hA.2.2.1)

def genuineDiagonalZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 = v.2.2.2 then
    headCoefficient atom receiver y k v * zeroMode atom v else 0

def genuineOffDiagonalZero (atom : MediumAtom) (receiver y : ℝ) (k : Key) : ℂ :=
  ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
    headCoefficient atom receiver y k v * zeroMode atom v else 0

theorem genuineZero_eq_diagonal_add_offDiagonal (atom : MediumAtom)
    (receiver y : ℝ) (k : Key) :
    nativeGenuineZero atom receiver y k =
      genuineDiagonalZero atom receiver y k + genuineOffDiagonalZero atom receiver y k := by
  unfold nativeGenuineZero genuineDiagonalZero genuineOffDiagonalZero
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v hv
  by_cases h : v.2.1.2 = v.2.2.2 <;> simp [h]

/-- The zero source actually used by E's OFF-DIAGONAL Poisson identity.
The diagonal correction is displayed and has not been prematurely zeroed. -/
theorem genuineOffDiagonalZero_re_eq_MT_P_corrections
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (receiver y : ℝ) (k : Key) :
    (genuineOffDiagonalZero atom receiver y k).re =
      (nativeMT atom receiver y k).re + nativeP atom receiver y k +
      (roughReplacementCorrection atom receiver y k).re -
      (genuineDiagonalZero atom receiver y k).re := by
  have h := nativeGenuineZero_re_eq_MT_P_correction hA receiver y k
  rw [genuineZero_eq_diagonal_add_offDiagonal] at h
  simp only [Complex.add_re] at h
  linarith

end
end ImbalancedChen.Part3.MediumActualS3ZeroCentering20261028
