import ImbalancedChen.P4BOriginalRankTwoGlobalPayment

/-! Exact residual for the full original prime-product discrepancy after
paying the small complete moduli and the remaining rough rank two. -/
namespace ImbalancedChen.P4BOriginalRankTwoHigherRemainder
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalRankTwoGlobalPayment (eventually_original_prime_rank_two)
open P4BOriginalRankTwoChartPayment (carrier tau)
open P4BOriginalTwoAtlasSmallPayment (remaining small atlasPair)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)
open Part3 (primeProductSignedError)
open P4AUpperTaggedParityCompiler (universe)
open P4AOriginalFull87RawChronology (cutoff)

def higher (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (ell : ℝ) :=
  remaining omega N \ carrier m r n e q a omega k N ell

theorem actual_rank_at_least_three (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (ell : ℝ) {v b d : ℕ} (hv : v∈higher m r n e q a omega k N ell)
    (hn : coefficient m r n e q a omega k N ((N:ℝ)^ell) v≠0)
    (hb : b∈actualSmallRosserSupport N N ((N:ℝ)^omega))
    (hd : d∈universe N N ((N:ℝ)^omega) (cutoff N)) (he : b*d=v) : 3≤d.primeFactorsList.length := by
  by_contra! h
  have hl := P4AFiniteFallbackLowRankRho.mem_activeLow_of_decomposition m r n e q a omega N
    (tau m e q a k) ell hn hb hd he (by omega)
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1,hl⟩)

theorem eventually_only_higher_ranks (K : ℕ) (hK : 2≤K) {b kap : ℝ} (hb : 0<b) (hk : 0<kap)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (kap0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      ell<1/1000 →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kap s kap0 N):ℂ)-
        atlasPair hb hs hg K N kap0 zeta (higher m r n e q a omega k N ell) c‖≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  have hfee : 0<delta/3 := by linarith
  filter_upwards [P4BOriginalTwoAtlasSmallPayment.actual_small_prime_sum A (delta/3) hfee,
    eventually_original_prime_rank_two A (delta/3) hfee,
    P4BOriginalRestrictedAtlasProper.eventually_subset_atlases K hK hb hk A (delta/3) hfee]
    with N hsmall hlow hchart
  intro s hs hg kap0 zeta m r n e q a omega k ell hell
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let W := trimmedWeight b kap s kap0 N
  let D := fun S : Finset ℕ => (primeProductSignedError 2 N N S c W:ℂ)
  let S := carrier m r n e q a omega k N ell
  let T := higher m r n e q a omega k N ell
  let H := atlasPair hb hs hg K N kap0 zeta T c
  let fee := (delta/3)*(N:ℝ)/(Real.log (N:ℝ))^A
  have hs1 := P4BArbitraryWidthUpperPairProfile.legal_width_le_one hb hk
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) (by simpa only [one_mul] using hg)
  have ha : ‖D (small omega N)‖≤fee := by
    simpa only [D,Complex.norm_real,Real.norm_eq_abs] using
      hsmall b kap s kap0 hs hs1 m r n e q a omega k ((N:ℝ)^ell)
  have hl : ‖D S‖≤fee := by
    simpa only [D,Complex.norm_real,Real.norm_eq_abs] using
      hlow b kap s kap0 hb hk hs hg m r n e q a omega k ell hell
  have highSub : T⊆Q omega N := fun d hd' =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hd').1).1
  have hh : ‖D T-H‖≤fee := hchart s hs hg kap0 zeta m r n e q a omega k
    ((N:ℝ)^ell) T highSub hrange
  have sub : S⊆remaining omega N := Finset.inter_subset_left
  have split : D T+D S=D (remaining omega N) := by
    change ((primeProductSignedError 2 N N T c W:ℝ):ℂ)+
      ((primeProductSignedError 2 N N S c W:ℝ):ℂ)=_
    rw [← Complex.ofReal_add]
    exact congrArg (fun z : ℝ => (z:ℂ)) (Finset.sum_sdiff sub)
  have orig : D (Q omega N)=D (small omega N)+D (remaining omega N) := by
    simp only [D,P4BOriginalTwoAtlasSmallPayment.exact_source_partition N omega c W,Complex.ofReal_add]
  have he : D (Q omega N)-H=D (small omega N)+D S+(D T-H) := by
    rw [orig,←split]; ring
  change ‖D (Q omega N)-H‖≤_
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add ha hl)) hh).trans_eq
    (by dsimp only [fee]; ring))

end
end ImbalancedChen.P4BOriginalRankTwoHigherRemainder
