import ImbalancedChen.P4BOriginalRankTwoHigherRemainder

/-! The complete-modulus BV range holds for all rough ranks. The quantitative
remainder can be returned to the original high-rank carrier before grouping. -/
namespace ImbalancedChen.P4BOriginalAllRankClassicalRange
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOriginalTwoAtlasSmallPayment (atlasPair)
open P4BOriginalRankTwoChartPayment (tau)
open P4BOriginalRankTwoGlobalPayment (eventually_bounded_moduli_prime)
open P4BOuterRampRoughness (baseline)
open Part3 (primeProductSignedError)

def below (omega : ℝ) (N : ℕ) :=
  (Q omega N).filter (fun v => (v:ℝ)<(N:ℝ)^(2/5:ℝ))

def above (omega : ℝ) (N : ℕ) := Q omega N \ below omega N

abbrev lowRank (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (ell : ℝ) :=
  P4AFiniteFallbackLowRankRho.activeLow m r n e q a omega N (tau m e q a k) ell

def wholeHigh (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (ell : ℝ) :=
  Q omega N \ lowRank m r n e q a omega k N ell

theorem actual_class (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (L : ℝ)
    {U : Finset ℕ} (hU : U⊆Q omega N)
    (hsize : ∀ v∈U,(v:ℝ)<(N:ℝ)^(2/5:ℝ)) :
    ∀ v∈U,0<v ∧ (v:ℝ)<(N:ℝ)^(2/5:ℝ) ∧ N.Coprime v ∧
      |coefficient m r n e q a omega k N L v|≤1 := by
  intro v hv
  have hq := hU hv
  exact ⟨Nat.pos_of_ne_zero (P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hq).ne_zero,
    hsize v hv,(P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hq).symm,
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ v⟩

theorem lowRank_subset_below (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (hN : 1<N) (ell : ℝ) (hell : ell<1/1000) :
    lowRank m r n e q a omega k N ell⊆below omega N := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
    P4AFiniteFallbackLowRankRho.activeLow_power m r n e q a omega N hN (tau m e q a k) ell hell hv⟩

theorem above_subset_wholeHigh (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (hN : 1<N) (ell : ℝ) (hell : ell<1/1000) :
    above omega N⊆wholeHigh m r n e q a omega k N ell := by
  intro v hv
  obtain ⟨hvQ,hn⟩ := Finset.mem_sdiff.mp hv
  exact Finset.mem_sdiff.mpr ⟨hvQ,fun h => hn (lowRank_subset_below m r n e q a omega k N hN ell hell h)⟩

/-- The complete height cut is used only in a discrepancy identity. The original
whole high carrier is selected by the rough factor rank itself. -/
theorem above_actual_rank (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (hN : 1<N) (ell : ℝ) (hell : ell<1/1000) {v u d : ℕ}
    (hv : v∈above omega N) (hn : coefficient m r n e q a omega k N ((N:ℝ)^ell) v≠0)
    (hu : u∈actualSmallRosserSupport N N ((N:ℝ)^omega))
    (hd : d∈P4AUpperTaggedParityCompiler.universe N N ((N:ℝ)^omega) (P4AOriginalFull87RawChronology.cutoff N))
    (he : u*d=v) :
    (N:ℝ)^(2/5:ℝ)≤v ∧ 3≤d.primeFactorsList.length := by
  have hvQ := (Finset.mem_sdiff.mp hv).1
  constructor
  · exact le_of_not_gt (fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨hvQ,h⟩))
  · by_contra! h
    have hlow := P4AFiniteFallbackLowRankRho.mem_activeLow_of_decomposition m r n e q a omega N
      (tau m e q a k) ell hn hu hd he (by omega)
    exact (Finset.mem_sdiff.mp (above_subset_wholeHigh m r n e q a omega k N hN ell hell hv)).2 hlow

/-- Any chosen bounded part of the actual complete modulus set can be removed.
The fixed policy, two ordered primes, trim, smooth width and signed mean are identical. -/
theorem eventually_remove_bounded (K : ℕ) (hK : 2≤K) {b kap : ℝ} (hb : 0<b) (hk : 0<kap)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (kap0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (L : ℝ)
        (U : Finset ℕ),U⊆Q omega N → (∀ v∈U,(v:ℝ)<(N:ℝ)^(2/5:ℝ)) →
      let c := coefficient m r n e q a omega k N L
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖(primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kap s kap0 N):ℂ)-
        atlasPair hb hs hg K N kap0 zeta (Q omega N \ U) c‖≤delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_bounded_moduli_prime A (delta/2) (half_pos hd),
    P4BOriginalRestrictedAtlasProper.eventually_subset_atlases K hK hb hk A (delta/2) (half_pos hd)]
    with N H E
  intro s hs hg kap0 zeta m r n e q a omega k L U hU hsize
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N L
  let D := fun T : Finset ℕ => (primeProductSignedError 2 N N T c (trimmedWeight b kap s kap0 N):ℂ)
  let V := Q omega N \ U
  let Y := atlasPair hb hs hg K N kap0 zeta V c
  let fee := (delta/2)*(N:ℝ)/(Real.log (N:ℝ))^A
  have hv : V⊆Q omega N := fun _ h => (Finset.mem_sdiff.mp h).1
  have hu : ‖D U‖≤fee := by
    simpa only [D,Complex.norm_real,Real.norm_eq_abs] using
      H b kap s kap0 hb hk hs hg U c (actual_class m r n e q a omega k N L hU hsize)
  have hy : ‖D V-Y‖≤fee := E s hs hg kap0 zeta m r n e q a omega k L V hv hrange
  have he : D V+D U=D (Q omega N) := by
    unfold D
    rw [←Complex.ofReal_add]
    exact congrArg (fun z : ℝ => (z:ℂ)) (Finset.sum_sdiff hU)
  change ‖D (Q omega N)-Y‖≤_
  rw [←he,show D V+D U-Y=D U+(D V-Y) by ring]
  exact (norm_add_le _ _).trans ((add_le_add hu hy).trans_eq (by dsimp only [fee]; ring))

/-- The full physical error admits both the sharp true height remainder and the whole
high-rank remainder. Their joint chart sums differ by an arbitrarily small fee, so no
cut of a complete product is carried into any of the independent convolution factors. -/
theorem eventually_height_and_wholeHigh (K : ℕ) (hK : 2≤K) {b kap : ℝ} (hb : 0<b) (hk : 0<kap)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (kap0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      ell<1/1000 →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      let D := (primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kap s kap0 N):ℂ)
      let H := fun S => atlasPair hb hs hg K N kap0 zeta S c
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖D-H (above omega N)‖≤delta*(N:ℝ)/(Real.log (N:ℝ))^A ∧
      ‖D-H (wholeHigh m r n e q a omega k N ell)‖≤delta*(N:ℝ)/(Real.log (N:ℝ))^A ∧
      ‖H (above omega N)-H (wholeHigh m r n e q a omega k N ell)‖≤delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_remove_bounded K hK hb hk A (delta/2) (half_pos hd),
    eventually_ge_atTop (2:ℕ)] with N HH hN
  intro s hs hg kap0 zeta m r n e q a omega k ell hell
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let D := (primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kap s kap0 N):ℂ)
  let H := fun S => atlasPair hb hs hg K N kap0 zeta S c
  let T := above omega N
  let V := wholeHigh m r n e q a omega k N ell
  let fee := (delta/2)*(N:ℝ)/(Real.log (N:ℝ))^A
  have H' := HH s hs hg kap0 zeta m r n e q a omega k ((N:ℝ)^ell)
  have hT : ‖D-H T‖≤fee := H' (below omega N) (Finset.filter_subset _ _)
    (fun _ hv => (Finset.mem_filter.mp hv).2) hrange
  have sub := lowRank_subset_below m r n e q a omega k N (by omega) ell hell
  have hV : ‖D-H V‖≤fee := H' (lowRank m r n e q a omega k N ell)
    (sub.trans (Finset.filter_subset _ _)) (fun _ hv => (Finset.mem_filter.mp (sub hv)).2) hrange
  have e2 : fee+fee=delta*(N:ℝ)/(Real.log (N:ℝ))^A := by dsimp only [fee]; ring
  have hfee : fee≤delta*(N:ℝ)/(Real.log (N:ℝ))^A :=
    (le_add_of_nonneg_right ((norm_nonneg _).trans hT)).trans_eq e2
  refine ⟨hT.trans hfee,hV.trans hfee,?_⟩
  change ‖H T-H V‖≤_
  calc
    _ = ‖(H T-D)+(D-H V)‖ := by congr 1; ring
    _ ≤ ‖H T-D‖+‖D-H V‖ := norm_add_le _ _
    _ ≤ fee+fee := add_le_add (by simpa only [norm_sub_rev (H T) D] using hT) hV
    _ = _ := e2

end
end ImbalancedChen.P4BOriginalAllRankClassicalRange
