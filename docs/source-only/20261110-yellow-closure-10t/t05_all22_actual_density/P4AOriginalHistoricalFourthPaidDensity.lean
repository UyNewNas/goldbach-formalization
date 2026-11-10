import ImbalancedChen.P4AOriginalHistoricalThirdPaidDensity
import ImbalancedChen.P1OriginalFourthCofinalGain

/-! G1 on the same physical coefficient which already includes all four
positive endpoints and G2,G3,G5,G6,G15–G22. Both original bounds
use one e and one cofinal q. The G1 threshold allows every early a
in the already adopted interval, independently of the later beta. -/
namespace ImbalancedChen.P4AOriginalHistoricalFourthPaidDensity
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (original data)
open P4AOriginalNewFifthPhysical (Joined fifthRounding sixthChange)
open P1OriginalFourthCofinalGain (exists_cofinal_original_fourth_gain)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalNewFifthCounting (tree)
open P4AOriginalNewFifthPaidDensity (rho)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87Saved86 (savedGain)
open P5OriginalCommonFourthSourceLedger (originalFourthIntegral)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalVariableFifthPhysicalLedger (physical)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)

def beforeEight (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℝ :=
  (∑ i,currentUpperEighteenPositive i)-currentUpperEighteenGains 0-
    currentUpperEighteenGains 1-currentUpperEighteenGains 2-
    currentUpperEighteenGains 4-currentUpperEighteenGains 5+
    normalize N (fifthRounding n e q a N+sixthChange n e q a N)

def upper (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (w eta : ℝ) : ℝ :=
  (beforeEight n e q a N-(savedGain : ℝ)+eta+compilerReserve) *
    (singularSeries N/Real.log (N:ℝ))-
      p4aActualPresieveCorrection (tree r n e q a N false) N N w (cutoff N)

theorem replace_fourth {e : ℚ} {q : ℕ} {a eta : ℝ}
    (h : currentUpperEighteenGains 0-eta/2 < originalFourthIntegral (original e q a))
    (n N : ℕ) :
    P4AOriginalHistoricalThirdPaidDensity.beforeEight n e q a N+eta/2 ≤ beforeEight n e q a N+eta := by
  unfold P4AOriginalHistoricalThirdPaidDensity.beforeEight beforeEight
  linarith only [h]

private theorem join_fourth {P : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop} {eta eMax : ℝ}
    (heta : 0 < eta) (h : Joined eMax P) : Joined eMax (fun r n e q a N =>
      P r n e q a N ∧ currentUpperEighteenGains 0-eta/2 < originalFourthIntegral (original e q a)) := by
  obtain ⟨r0,hR⟩ := h
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨a0,ha0,hac,hA⟩ := hN n hn
  refine ⟨a0,ha0,hac,?_⟩
  intro a ha haa
  obtain ⟨E,hE,hG⟩ := exists_cofinal_original_fourth_gain (eta/2) (half_pos heta)
  have hac' : a ≤ (3/200 : ℝ) := (haa.trans hac).trans (by norm_num)
  obtain ⟨e0,he0,hem,hO⟩ := hA a ha haa
  refine ⟨min e0 E,lt_min he0 hE,(min_le_left _ _).trans hem,?_⟩
  intro e he hee qMin mMin
  obtain ⟨qG,_,hg⟩ := hG e (by exact_mod_cast he) (hee.trans_le (min_le_right _ _)) a ha hac' mMin qMin
  obtain ⟨q0,hq0,hMin,hQ⟩ := hO e he (hee.trans_le (min_le_left _ _)) (max qMin qG) mMin
  refine ⟨q0,hq0,(le_max_left _ _).trans hMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hOld⟩ := hQ q hq
  refine ⟨hm,hpos,?_⟩
  filter_upwards [hOld] with N hot
  exact fun hev => ⟨hot hev,(hg q (((le_max_right _ _).trans hMin).trans hq)).2⟩

theorem exists_joined_ordinary (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    Joined eMax (fun r n e q a N =>
      normalize N (rawRoot (tree r n e q a N) N) < beforeEight n e q a N-(savedGain : ℝ)+eta) := by
  apply P4AOriginalNewFifthPhysical.joined_eventually_mono (join_fourth heta
    (P4AOriginalHistoricalThirdPaidDensity.exists_joined_ordinary (eta/2) eMax (half_pos heta) heMax))
  filter_upwards with N
  intro r n e q a _ h
  obtain ⟨ho,hg⟩ := h
  linarith only [ho,replace_fourth hg n N]

theorem exists_joined_positive_presieve (nu eta betaMax eMax : ℝ)
    (hnu : 0 < nu) (heta : 0 < eta) (hMax : 0 < betaMax) (heMax : 0 < eMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 ≤ (19/96 : ℝ)/nu ∧
    Joined eMax (fun r n e q a N =>
      let w := (N : ℝ)^(nu*beta^2)
      let L := (N : ℝ)^(nu*beta)
      1 < w ∧ w ≤ cutoff N ∧ normalize N (physical (tree r n e q a N) N N w (cutoff N) L) <
        beforeEight n e q a N-(savedGain : ℝ)+eta) := by
  obtain ⟨beta,hb,hb8,hbM,hbs,h⟩ := P4AOriginalHistoricalThirdPaidDensity.exists_joined_positive_presieve
    nu (eta/2) betaMax eMax hnu (half_pos heta) hMax heMax
  refine ⟨beta,hb,hb8,hbM,hbs,?_⟩
  apply P4AOriginalNewFifthPhysical.joined_eventually_mono (join_fourth heta h)
  filter_upwards with N
  intro r n e q a _ hpair
  obtain ⟨⟨hw,hwz,ho⟩,hg⟩ := hpair
  exact ⟨hw,hwz,by linarith only [ho,replace_fourth hg n N]⟩

/-- The 13 original gains enter the density and the finite count of the very same physical coefficient. -/
theorem exists_paid_density_and_count (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1/800 ∧ ∀ a : ℝ, 0 < a → a ≤ a0 →
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
    ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      mMin ≤ (data e q a).m ∧
      (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) (data e q a).m ≤
        (∑ i, currentUpperEighteenPositive i) + originalDensityReserve/4) ∧
      ∀ nu betaMax : ℝ, 0 < nu → 0 < betaMax → ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧
        beta < betaMax ∧ nu*beta^2 < 19/96 ∧ nu*beta < 1/1000 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
        (∀ N : ℕ, 2 ≤ N → ∀ x : ℕ,
          rho r n e q a N ((N : ℝ)^(nu*beta^2)) tau ((N : ℝ)^(nu*beta)) x ≠ 0 →
            (x : ℝ) < (N : ℝ)^(599/1000 : ℝ)) ∧
        (∀ᶠ N : ℕ in atTop, Even N →
          let w := (N : ℝ)^(nu*beta^2)
          let L := (N : ℝ)^(nu*beta)
          physicalDensitySum (moduli N w) (rho r n e q a N w tau L) < upper r n e q a N w eta) ∧
        ∀ b kappa : ℝ, 0 < b → b < 1 → (19/96 : ℝ) < (1-kappa)*(b/(1+b)) →
          ∀ᶠ N : ℕ in atTop, Even N →
            let w := (N : ℝ)^(nu*beta^2)
            let L := (N : ℝ)^(nu*beta)
            let T := manuscriptHalfProductCutoff kappa N
            (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) * upper r n e q a N w eta +
              realPhysicalDistributionError b N T (moduli N w) (rho r n e q a N w tau L) +
                (Nat.ceil (cutoff N) : ℝ) + (T+1) := by
  obtain ⟨r0,hR⟩ := P4AOriginalHistoricalThirdPaidDensity.exists_paid_density_and_count (eta/2)
    eMax (half_pos heta) heMax
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨a0,ha0,hac,hA⟩ := hN n hn
  refine ⟨a0,ha0,hac,?_⟩
  intro a ha haa
  obtain ⟨E,hE,hG⟩ := exists_cofinal_original_fourth_gain (eta/2) (half_pos heta)
  have hac' : a ≤ (3/200 : ℝ) := (haa.trans hac).trans (by norm_num)
  obtain ⟨e0,he0,hem,hO⟩ := hA a ha haa
  refine ⟨min e0 E,lt_min he0 hE,(min_le_left _ _).trans hem,?_⟩
  intro e he hee qMin mMin
  obtain ⟨qG,_,hg⟩ := hG e (by exact_mod_cast he) (hee.trans_le (min_le_right _ _)) a ha hac' mMin qMin
  obtain ⟨q0,hq0,hMin,hQ⟩ := hO e he (hee.trans_le (min_le_left _ _)) (max qMin qG) mMin
  refine ⟨q0,hq0,(le_max_left _ _).trans hMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hCont⟩ := hQ q hq
  refine ⟨hm,hpos,?_⟩
  intro nu betaMax hnu hmax
  obtain ⟨beta,hb,hb8,hbM,hbc,hbl,tau0,ht0,hTau⟩ := hCont nu betaMax hnu hmax
  refine ⟨beta,hb,hb8,hbM,hbc,hbl,tau0,ht0,?_⟩
  intro tau ht htc
  obtain ⟨hs,hd,hcount⟩ := hTau tau ht htc
  have hupper : ∀ᶠ N : ℕ in atTop, Even N → ∀ w : ℝ,
      P4AOriginalHistoricalThirdPaidDensity.upper r n e q a N w (eta/2) ≤ upper r n e q a N w eta := by
    have hgt := (hg q (((le_max_right _ _).trans hMin).trans hq)).2
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN2
    intro hev w
    unfold P4AOriginalHistoricalThirdPaidDensity.upper upper
    apply sub_le_sub_right
    apply mul_le_mul_of_nonneg_right _ (densityScale_pos hN2).le
    linarith only [replace_fourth hgt n N]
  refine ⟨hs,?_,?_⟩
  · filter_upwards [hd,hupper] with N h hu
    exact fun hev => (h hev).trans_le (hu hev _)
  · intro b kappa hb' hb1 hgap
    filter_upwards [hcount b kappa hb' hb1 hgap,hupper] with N hc hu
    intro hev
    let T := manuscriptHalfProductCutoff kappa N
    have hmul := mul_le_mul_of_nonneg_left (hu hev ((N : ℝ)^(nu*beta^2)))
      (Nat.cast_nonneg (realHalfProductSource b N T).card)
    exact (hc hev).trans (add_le_add_right (add_le_add_right (add_le_add_right hmul _) _) _)

end
end ImbalancedChen.P4AOriginalHistoricalFourthPaidDensity
