import ImbalancedChen.P4BOriginalPairSmallModuliBV
import ImbalancedChen.P4BOriginalRestrictedAtlasProper
import ImbalancedChen.P4AFiniteFallbackLowRankRho

/-! The literal total of the two original HB alternatives on small
complete moduli. The complementary two alternatives use the same
rectangle, signed coefficient, labels, arithmetic tests and mean. -/
namespace ImbalancedChen.P4BOriginalTwoAtlasSmallPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteSignedTrim (pairLicence trimmedWeight)
open P4BOriginalFiniteProperWords (exponent)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4AFiniteFallbackLowRankRho (actualRho mem_activeLow_of_decomposition actual_decomposition)
open P4AUpperTaggedParityCompiler (universe)
open P4AOriginalFull87RawChronology (cutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAtlasReserveBranches (mediumAtlas noMediumAtlas originalMediumLow originalMediumHigh)

def small (omega : ℝ) (N : ℕ) := (Q omega N).filter (fun d => (d:ℝ)≤(N:ℝ)^(1/5:ℝ))
def remaining (omega : ℝ) (N : ℕ) := (Q omega N).filter (fun d => ¬(d:ℝ)≤(N:ℝ)^(1/5:ℝ))

def atlasPair {b kappa s : ℝ} (hb : 0<b) (hs : 0<s) (hg : 2*s≤baseline b kappa-exponent)
    (K N : ℕ) (kappa0 zeta : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) : ℂ :=
  let L := pairLicence hb hs hg N
  let cc := fun d => (c d:ℂ)
  ∑ js∈chartBank N 2,
    (mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
      noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js)

theorem actual_small_prime_sum (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kappa s kappa0 : ℝ),0<s → s≤1 →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      |Part3.primeProductSignedError 2 N N (small omega N) (coefficient m r n e q a omega k N level)
        (trimmedWeight b kappa s kappa0 N)| ≤ delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  filter_upwards [P4BOriginalPairSmallModuliBV.eventually_pair_sum A delta hd] with N H
  intro b kappa s kappa0 hs hs1 m r n e q a omega k level
  refine H (small omega N) (coefficient m r n e q a omega k N level) ?_ b kappa s kappa0 hs hs1
  intro d hd
  obtain ⟨hQ,hsize⟩ := Finset.mem_filter.mp hd
  have hsq := P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hQ
  exact ⟨Nat.pos_of_ne_zero hsq.ne_zero,hsize,hsq,
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d,
    (P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hQ).symm⟩

/-- Every genuinely present complete modulus with zero or one rough
prime is in the paid part. The small beta factor uses the actual sign
of the compiled coefficient and the level chosen before N. -/
theorem rank_zero_one_in_small (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (hN : 1<N) (ell : ℝ) (hell : ell<1/1000)
    {t u d : ℕ} (hact : coefficient m r n e q a omega k N ((N:ℝ)^ell) t≠0)
    (hu : u∈actualSmallRosserSupport N N ((N:ℝ)^omega))
    (hd : d∈universe N N ((N:ℝ)^omega) (cutoff N)) (hprod : u*d=t)
    (hlen : d.primeFactorsList.length≤1) : t∈small omega N := by
  let tau := P4AOriginalOrderedThirdActualCoefficient.alignedWidth
    (P4AOriginalFiniteFallbackCount.jointIndex (P4AFallbackCanonicalBanks.bank m)
      (P4AOriginalNewFifthUnion.data e q a).m) k
  have hact' : actualRho m r n e q a omega N tau ell t≠0 := hact
  have hlow := mem_activeLow_of_decomposition m r n e q a omega N tau ell hact' hu hd hprod
    (by omega : d.primeFactorsList.length≤2)
  obtain ⟨u',d',hu',hd',hp',huL,_,_⟩ := actual_decomposition m r n e q a omega N tau ell hlow
  have he := P4AUpperTaggedBetaAttachment.product_unique N N ((N:ℝ)^omega) (cutoff N)
    hu hd hu' hd' (hprod.trans hp'.symm)
  rw [← he.1] at huL
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  obtain ⟨hsub,heprod⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe
    N N ((N:ℝ)^omega) (cutoff N) hd
  have hshort (ps : List ℕ) (hl : ps.length≤1)
      (hh : ∀ p∈ps,(p:ℝ)≤cutoff N) : (ps.prod:ℝ)≤cutoff N := by
    cases ps with
    | nil => simpa using Real.one_le_rpow hn.le (by norm_num : 0≤(19/96:ℝ))
    | cons p tail =>
      have hz : tail.length=0 := by simp only [List.length_cons] at hl; omega
      have ht := List.length_eq_zero.mp hz
      subst tail
      simpa using hh p (by simp)
  have hR := hshort d.primeFactorsList.reverse (by simpa using hlen)
    (fun p hp => (mem_roughPrimeUniverse.mp (hsub.subset hp)).2.2.2.2.le)
  rw [heprod] at hR
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hlow).1,?_⟩
  calc
    (t:ℝ) = (u:ℝ)*(d:ℝ) := by rw [←hprod,Nat.cast_mul]
    _ ≤ (N:ℝ)^ell*cutoff N := mul_le_mul huL.le hR (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N:ℝ)^(ell+19/96) := (Real.rpow_add (zero_lt_one.trans hn) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le (by linarith only [hell])

theorem exact_source_partition (N : ℕ) (omega : ℝ) (c : ℕ → ℝ)
    (W : (Fin 2 → Fin (N+1)) → ℝ) :
    Part3.primeProductSignedError 2 N N (Q omega N) c W =
      Part3.primeProductSignedError 2 N N (small omega N) c W+
      Part3.primeProductSignedError 2 N N (remaining omega N) c W := by
  unfold Part3.primeProductSignedError small remaining
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The small-modulus chart total is paid. Only the same two chart sums
on complete moduli above N^(1/5) remain in the full physical PP error.
Each alternative displayed here has a single delta budget. -/
theorem eventually_two_atlas_small_and_remainder (K : ℕ) (hK : 2≤K) {b kappa : ℝ}
    (hb : 0<b) (hk : 0<kappa) (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kappa-exponent),
      ∀ (kappa0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      let c := coefficient m r n e q a omega k N level
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖atlasPair hb hs hg K N kappa0 zeta (small omega N) c‖ ≤ delta*(N:ℝ)/Real.log (N:ℝ)^A ∧
      ‖(Part3.primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kappa s kappa0 N):ℂ)-
        atlasPair hb hs hg K N kappa0 zeta (remaining omega N) c‖ ≤
        delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  filter_upwards [actual_small_prime_sum A (delta/2) (half_pos hd),
    P4BOriginalRestrictedAtlasProper.eventually_subset_atlases K hK hb hk A (delta/2) (half_pos hd)]
    with N hsmall hchart
  intro s hs hg kappa0 zeta m r n e q a omega k level
  dsimp only
  intro hrange
  let c := coefficient m r n e q a omega k N level
  let W := trimmedWeight b kappa s kappa0 N
  let ps (S : Finset ℕ) : ℂ := (Part3.primeProductSignedError 2 N N S c W:ℂ)
  let atSum (S : Finset ℕ) := atlasPair hb hs hg K N kappa0 zeta S c
  let B := (delta/2)*(N:ℝ)/Real.log (N:ℝ)^A
  have hs1 := P4BArbitraryWidthUpperPairProfile.legal_width_le_one hb hk
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
    (by simpa only [one_mul] using hg)
  have hlow : ‖ps (small omega N)‖≤B := by
    simpa only [ps,Complex.norm_real,Real.norm_eq_abs] using
      hsmall b kappa s kappa0 hs hs1 m r n e q a omega k level
  have H (S : Finset ℕ) (hS : S⊆Q omega N) : ‖ps S-atSum S‖≤B :=
    hchart s hs hg kappa0 zeta m r n e q a omega k level S hS hrange
  have hpart : ps (Q omega N)=ps (small omega N)+ps (remaining omega N) := by
    simp only [ps,exact_source_partition N omega c W,Complex.ofReal_add]
  have hbudget : B+B=delta*(N:ℝ)/Real.log (N:ℝ)^A := by dsimp [B]; ring
  constructor
  · change ‖atSum (small omega N)‖≤_
    have h := H (small omega N) (Finset.filter_subset _ _)
    rw [norm_sub_rev] at h
    calc
      _ = ‖atSum (small omega N)-ps (small omega N)+ps (small omega N)‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := (add_le_add h hlow).trans_eq hbudget
  · change ‖ps (Q omega N)-atSum (remaining omega N)‖≤_
    rw [hpart,add_sub_assoc]
    exact (norm_add_le _ _).trans ((add_le_add hlow (H _ (Finset.filter_subset _ _))).trans_eq hbudget)

end
end ImbalancedChen.P4BOriginalTwoAtlasSmallPayment
