import ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
import ImbalancedChen.Part3MediumNativePrincipalSource
import ImbalancedChen.Part3OriginalS2ZeroGramErrorPayment
import ImbalancedChen.Part3OriginalPaperPsiCoprimeCount
import Mathlib.Tactic

/-! Same-source S2 zero-mode comparison with the independently defined
native MT consumed by S1 and S3. The Gram error is an explicit density
difference, not a variance estimate or whole-expression placeholder.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalS2SameSourcePrincipal

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2OneCongruencePoisson
open ImbalancedChen.Part3OriginalS2ZeroGramCompiler
open ImbalancedChen.Part3OriginalS2ZeroGramErrorPayment
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalMediumPrincipalFiniteCRT
open ImbalancedChen.Part3.OriginalMediumS3ZeroCentering
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalPaperPsiCoprimeCount
open ImbalancedChen.Part3.TransposedZeroCovariance
open Classical Finset
open scoped BigOperators

noncomputable section

def nativeZeroDensity (ell r s : ℕ) : ℝ :=
  1 / (((ell * r : ℕ) : ℝ) * (Nat.totient (ell * s) : ℝ))

def nativePrincipalPair (d : MediumAtom) (z y : ℝ) (k : Key)
    (q small r s : ℕ) : ℂ :=
  (paperQWeight d q : ℂ) * lambdaTrim d z y k small r *
    star (lambdaTrim d z y k small s) * ((d.V * paperMass : ℝ) : ℂ) *
    (gramDensity (q * small) r s : ℂ) *
    (primitiveMass d (q * small) r * star (primitiveMass d (q * small) s))

def actualZeroGramErrorPair (d : MediumAtom) (z y : ℝ) (k : Key)
    (q small r s : ℕ) : ℂ :=
  (paperQWeight d q : ℂ) * lambdaTrim d z y k small r *
    star (lambdaTrim d z y k small s) * ((d.V * paperMass : ℝ) : ℂ) *
    ((nativeZeroDensity (q * small) r s - gramDensity (q * small) r s : ℝ) : ℂ) *
    (primitiveMass d (q * small) r * star (primitiveMass d (q * small) s))

def actualZeroGramError (d : MediumAtom) (z y : ℝ) (k : Key) : ℂ :=
  ∑ q ∈ nativeQCarrier d, ∑ small ∈ dyadicWindow k.d,
    ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
      actualZeroGramErrorPair d z y k q small r s

theorem primitiveMass_eq_paperCoprimeMean (d : MediumAtom) (ell r : ℕ) :
    primitiveMass d ell r = paperCoprimeMean d.alphaCarrier d.alpha ell r := by
  simp only [primitiveMass, paperCoprimeMean, coprimeMass, Finset.sum_filter]

theorem gramDensity_cast (ell r s : ℕ) :
    (gramDensity ell r s : ℂ) = paperPrincipalCoefficient ell r s := by
  simp only [gramDensity, paperPrincipalCoefficient, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Both sides are independently built principal objects. The only
extra d values in the full dyadic window have zero actual lambdaTrim. -/
theorem nativeMT_eq_full_d_principal
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    nativeMT d z y k =
      ∑ q ∈ nativeQCarrier d, ∑ small ∈ dyadicWindow k.d,
        ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
          nativePrincipalPair d z y k q small r s := by
  unfold nativeMT nativeQD
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    _ = ∑ small ∈ activeD d k, ∑ r ∈ dyadicWindow k.w, ∑ s ∈ dyadicWindow k.w,
        nativePrincipalPair d z y k q small r s := by
      apply Finset.sum_congr rfl
      intro small hsmall
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      rw [nativePrincipalPair, primitiveMass_eq_paperCoprimeMean,
        primitiveMass_eq_paperCoprimeMean, gramDensity_cast]
      push_cast
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro small hsmall hn
      have hbad : ¬small.Coprime d.residue.natAbs := by
        intro hc
        exact hn (Finset.mem_filter.mpr ⟨hsmall, hc⟩)
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro s hs
      simp [nativePrincipalPair, lambdaTrim_zero_of_nonprimitive d z y k small r hd hbad]

/-- Exact zero-mode identity on the same native source as S1 and S3.
The error is the literal 1/(ell*r*phi(ell*s))-c_ell(r,s) coefficient. -/
theorem actualS2ZeroMode_eq_nativeMT_add_error
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    actualS2ZeroMode d z y k = nativeMT d z y k + actualZeroGramError d z y k := by
  rw [actualS2ZeroMode_eq_collapsed, nativeMT_eq_full_d_principal hd]
  unfold actualS2ZeroCollapsed actualZeroGramError
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [paperPsi_fourier_zero]
  simp only [nativePrincipalPair, actualZeroGramErrorPair, nativeZeroDensity,
    Algebra.smul_def, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast]
  ring

/-- Density comparison itself, valid for any actual original rough s.
The harmless global smoothing mass cancels from this arithmetic lemma. -/
theorem native_density_difference_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    {z : ℝ} (hz : 4 ≤ z)
    (hlarge : 4 * Real.log d.scale / (z * Real.log 2) ≤ 1)
    (small ell r s : ℕ) (hs : s ∈ roughFiber d z small)
    (hell : 0 < ell) (hr : 0 < r) :
    |nativeZeroDensity ell r s - gramDensity ell r s| ≤
      roughEulerDelta d z * nativeZeroDensity ell r s := by
  have hspos := roughFiber_pos d z small s hs
  have hG : 0 < gramDensity ell r s := by
    unfold gramDensity
    have ht := Nat.totient_pos.mpr (Nat.mul_pos (Nat.mul_pos hell hr) hspos)
    have htr := Nat.totient_pos.mpr (Nat.mul_pos hell hr)
    have hts := Nat.totient_pos.mpr (Nat.mul_pos hell hspos)
    positivity
  have hratio := zero_to_gram_density_ratio ell r s hell hr hspos
  have hbound := zero_to_gram_ratio_linear_on_medium hd hsigma hz hlarge
    small ell r s hs hell hr
  have hlow : 1 ≤ nativeZeroDensity ell r s / gramDensity ell r s := by
    rw [nativeZeroDensity, hratio]
    exact hbound.1
  have hhigh : nativeZeroDensity ell r s / gramDensity ell r s ≤
      1 + roughEulerDelta d z := by
    rw [nativeZeroDensity, hratio]
    exact hbound.2
  have hGZ : gramDensity ell r s ≤ nativeZeroDensity ell r s := by
    have h := (le_div_iff₀ hG).mp hlow
    nlinarith
  have hdiff : nativeZeroDensity ell r s - gramDensity ell r s ≤
      roughEulerDelta d z * gramDensity ell r s := by
    have h := (div_le_iff₀ hG).mp hhigh
    nlinarith
  have hdelta : 0 ≤ roughEulerDelta d z := by
    unfold roughEulerDelta
    have hlog : 0 ≤ Real.log d.scale := by
      have hx := hd.2.2.2.2.2.1
      have he : 1 < Real.exp (Real.exp 1) := Real.one_lt_exp.mpr (Real.exp_pos 1)
      exact Real.log_nonneg (by linarith)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  rw [abs_of_nonneg (sub_nonneg.mpr hGZ)]
  exact hdiff.trans (mul_le_mul_of_nonneg_left hGZ hdelta)

end
end ImbalancedChen.Part3OriginalS2SameSourcePrincipal
