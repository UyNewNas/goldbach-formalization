import ImbalancedChen.P4BOriginalNoMediumAtlasPayment

/-! SOURCE ONLY / UNCOMPILED. The actual existing RealB upper reduction
now leaves only the original rank-two mediumAtlas term on wholeHigh.
No estimate of that remaining medium term and no hUpper claim is made. -/
namespace ImbalancedChen.P4BOriginalRankTwoMediumRemainder
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumAtlasDictionary (noMediumTotal)
open P4BOriginalNoMediumAtlasPayment
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BOriginalFiniteSmoothCount (Q coefficient mass)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_RealB_le_high_modes)
open P4BOriginalHighRankMotherModes (modes eventually_atlas_eq_modes)
open P4BOriginalTwoAtlasSmallPayment (atlasPair)
open P4BOriginalAllRankClassicalRange (wholeHigh)
open P5Z.OriginalPrimeAtlasReserveBranches (mediumAtlas originalMediumLow originalMediumHigh)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P4BOuterRampRoughness (baseline)

def mediumTotal {b kap s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) : ℂ :=
  ∑ js∈chartBank N 2,mediumAtlas (pairLicence hb hs hg N) K N N kap0
    (originalMediumLow zeta js) (originalMediumHigh zeta js) S (fun d => (c d:ℂ)) js

theorem atlasPair_eq_medium_add_noMedium {b kap s : ℝ}
    (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (N K : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) :
    atlasPair hb hs hg K N kap0 zeta S c=
      mediumTotal hb hs hg N K kap0 zeta S c+noMediumTotal hb hs hg N K kap0 zeta S c := by
  unfold atlasPair mediumTotal noMediumTotal
  simp only [Finset.sum_add_distrib]

/-- Same raw positive source, same coefficient, beta/k, wholeHigh carrier
and singularNormalization as the existing RealB reduction. The no-medium
component is independently paid before it is removed from the signed sum. -/
theorem eventually_RealB_le_original_medium (K : ℕ) (hK : 2≤K)
    {zeta kappa kap0 b : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) (hkap0 : 0<kap0)
    (hb : (1:ℝ)/2<b) (hb1 : b<1) (hgate : 19/96<baseline b kap0)
    (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,∃ hs : 0<outerWidth N,∃ hg : 2*outerWidth N≤baseline b kap0-19/96,
      Even N → 0≤mass b kap0 (outerWidth N) N ∧
      |mass b kap0 (outerWidth N) N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (nu beta : ℝ),
      0<nu → 0<beta → beta≤1 → nu*beta^2≤19/96 → nu*beta<1/1000 →
      let omega := nu*beta^2
      let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+
        (mediumTotal (by linarith : 0<b) hs hg N K kap0 zeta
          (wholeHigh m r n e q a omega k N (nu*beta)) c).re+eta*singularNormalization N := by
  have hb0 : 0<b := by linarith
  filter_upwards [eventually_RealB_le_high_modes hb hb1 hkap0 ht1 hgate K hK (eta/2) (half_pos heta),
    eventually_rankTwo_noMediumAtlas_le_singular K hz hz1 hk hkz ht ht1
      hb0 hb1.le hkap0 hgate (eta/2) (half_pos heta),
    eventually_atlas_eq_modes (kap:=kap0) hb0] with N hcount hno hidentity
  obtain ⟨hs,hg,Hno⟩ := hno
  refine ⟨hs,hg,?_⟩
  intro heven
  obtain ⟨hpos,happrox,Hcount⟩ := hcount heven
  refine ⟨hpos,happrox.trans (by linarith),?_⟩
  intro m r n e q a k nu beta hnu hbeta hbOne homega hell
  dsimp only
  intro hRange
  let omega := nu*beta^2
  let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
  let S := wholeHigh m r n e q a omega k N (nu*beta)
  let med := mediumTotal hb0 hs hg N K kap0 zeta S c
  let no := noMediumTotal hb0 hs hg N K kap0 zeta S c
  let full := modes b kap0 (outerWidth N) N K kap0 S c
  have hS : S⊆Q omega N := fun d hd => (Finset.mem_sdiff.mp hd).1
  have hbound : ‖no‖≤eta/2*singularNormalization N :=
    Hno m r n e q a omega k (nu*beta) hRange S hS
  have hfull : full=med+no :=
    (hidentity (outerWidth N) hs hg K kap0 zeta S c).symm.trans
      (atlasPair_eq_medium_add_noMedium hb0 hs hg N K kap0 zeta S c)
  have hremove : full.re-med.re≤eta/2*singularNormalization N := by
    rw [hfull,Complex.add_re]
    linarith [(Complex.re_le_norm no).trans hbound]
  have HC := Hcount m r n e q a k nu beta hnu hbeta hbOne homega hell hRange
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+
    full.re+eta/2*singularNormalization N at HC
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+
    med.re+eta*singularNormalization N
  linarith only [HC,hremove]

end
end ImbalancedChen.P4BOriginalRankTwoMediumRemainder
