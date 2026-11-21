import ImbalancedChen.P4BOriginalNoMediumAtlasDictionary

/-! SOURCE ONLY / UNCOMPILED. Payment of the ORIGINAL raw rank-two
noMediumAtlas total through its proved source identity. The only local
estimate used is source74's actual two-mother bank theorem. No new
whole-atlas price, amplitude hypothesis or termwise branch bound is assumed. -/
namespace ImbalancedChen.P4BOriginalNoMediumAtlasPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumAtlasDictionary
open P4BOriginalTwoLongMotherPayment
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)

theorem eventually_rankTwo_noMediumAtlas_paid (K A : ℕ)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgate : 19/96<baseline b kap) :
    ∀ᶠ N : ℕ in atTop,∃ hs : 0<outerWidth N,∃ hg : 2*outerWidth N≤baseline b kap-19/96,
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      ‖noMediumTotal hb hs hg N K kap0 zeta S (coefficient m r n e q a omega k N ((N:ℝ)^ell))‖≤
        (N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_actual_twoLong_mother_paid K A hz hz1 hk hkz ht ht1 hb hb1 hkap hgate,
    eventually_noMediumTotal_eq_originalBank (kap:=kap) hb,
    eventually_width _ (half_pos (sub_pos.mpr hgate))] with N hbank hdict hw
  have hs : 0<outerWidth N := hw.2.1
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith [hw.2.2.1]
  refine ⟨hs,hg,?_⟩
  intro m r n e q a omega k ell hRange S hS
  rw [hdict (outerWidth N) hs hg K kap0 zeta S (coefficient m r n e q a omega k N ((N:ℝ)^ell))]
  exact hbank m r n e q a omega k ell hRange S hS

/-- The displayed scale is the official singularNormalization, whose
definition is the manuscript C_N*N/log(N)^2, with no leading factor two.
This theorem pays the rank-two noMediumAtlas component, not every H_N term. -/
theorem eventually_rankTwo_noMediumAtlas_le_singular (K : ℕ)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgate : 19/96<baseline b kap)
    (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,∃ hs : 0<outerWidth N,∃ hg : 2*outerWidth N≤baseline b kap-19/96,
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) → ∀ S : Finset ℕ,S⊆Q omega N →
      ‖noMediumTotal hb hs hg N K kap0 zeta S (coefficient m r n e q a omega k N ((N:ℝ)^ell))‖≤
        eta*singularNormalization N := by
  filter_upwards [eventually_actual_twoLong_mother_le_singular K hz hz1 hk hkz ht ht1
    hb hb1 hkap hgate eta heta,eventually_noMediumTotal_eq_originalBank (kap:=kap) hb,
    eventually_width _ (half_pos (sub_pos.mpr hgate))] with N hbank hdict hw
  have hs : 0<outerWidth N := hw.2.1
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith [hw.2.2.1]
  refine ⟨hs,hg,?_⟩
  intro m r n e q a omega k ell hRange S hS
  rw [hdict (outerWidth N) hs hg K kap0 zeta S (coefficient m r n e q a omega k N ((N:ℝ)^ell))]
  exact hbank m r n e q a omega k ell hRange S hS

/-- A literal expansion of the existing definition, not a renamed target
or an added normalization premise. For even N>2 this is the manuscript H_N. -/
theorem singularNormalization_original_formula (N : ℕ) :
    singularNormalization N=
      (twinPrimeConstant*∏ p∈oddPrimeDivisors N,((p:ℝ)-1)/((p:ℝ)-2))*(N:ℝ)/(Real.log (N:ℝ))^2 := rfl

end
end ImbalancedChen.P4BOriginalNoMediumAtlasPayment
