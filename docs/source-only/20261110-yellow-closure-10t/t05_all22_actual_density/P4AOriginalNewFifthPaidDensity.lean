import ImbalancedChen.P4AOriginalNewFifthCounting
import ImbalancedChen.P4AFull87UnionPhysicalSupport

/-! The true enlarged eighth tree pays the complete compiler reserve
on its own cap-reading history. G3 and the complete eight eighth-stage
entries use their ordinary transport. Beta is charged once, here. -/
namespace ImbalancedChen.P4AOriginalNewFifthPaidDensity
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthCounting (coefficient tree)
open P4AOriginalNewFifthPhysical (beforeEight)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOriginalFull87JointPhysicalBudget (cutoff_le_target)
open P4AOriginalFull87CompiledCounting (moduli compiled_modulus_dvd)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87Saved86 (savedGain)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve compilerReserve_pos)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)
open P5OriginalCommonPositivePresieve (normalize)

abbrev tags (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) : ℕ → List Bool :=
  P4AFull87DataCompilerReads.tag (width r) (width_pos r) n (data e q a) N

abbrev rho (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (w tau L : ℝ) :=
  coefficient r n e q a N (tags r n e q a N) w tau L

def upper (r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (w eta : ℝ) : ℝ :=
  (beforeEight n e q a N - (savedGain : ℝ) + eta + compilerReserve) *
      (singularSeries N / Real.log (N : ℝ)) -
    p4aActualPresieveCorrection (tree r n e q a N false) N N w (cutoff N)

private theorem unnormalize {N : ℕ} (hN : 2 ≤ N) {x b : ℝ} (h : normalize N x < b) :
    x < b * (singularSeries N / Real.log (N : ℝ)) := by
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc : normalize N x * (singularSeries N / Real.log (N : ℝ)) = x := by
    unfold normalize
    field_simp [(singularSeries_pos N).ne',hl.ne'] <;> ring
  simpa only [hc] using mul_lt_mul_of_pos_right h (densityScale_pos hN)

/-- Same physical Q and rho for the density and distribution terms.
Every coarse choice and the narrow width precede the even target. -/
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
  obtain ⟨r0,hR⟩ := P4AOriginalNewFifthPhysical.exists_joined_ordinary eta eMax heta heMax
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨a0,ha0,haSmall,hA⟩ := hN n hn
  refine ⟨a0,ha0,haSmall,?_⟩
  intro a ha haa
  obtain ⟨e0,he0,heCap,hE⟩ := hA a ha haa
  refine ⟨e0,he0,heCap,?_⟩
  intro e he hee qMin mMin
  obtain ⟨q0,hq0,hqMin,hQ⟩ := hE e he hee qMin mMin
  refine ⟨q0,hq0,hqMin,?_⟩
  intro q hq
  obtain ⟨hm,hpos,hOrd⟩ := hQ q hq
  refine ⟨hm,hpos,?_⟩
  intro nu betaMax hnu hMax
  let v := (19/96 : ℝ)/nu
  have hv : 0 < v := div_pos (by norm_num) hnu
  have hv' : nu*v = (19/96 : ℝ) := by dsimp [v]; field_simp [hnu.ne'] <;> ring
  obtain ⟨beta,hb,hb8,hbM,hbs,hbl,tau0,ht0,Nc,hNc,hpay⟩ :=
    P4AFull87UnionCompilerPayment.union_paid (width r) (width_pos r) n e (by exact_mod_cast he.le) q a
      nu v compilerReserve betaMax hnu hv (hv'.le.trans (by norm_num)) compilerReserve_pos hMax
  have homega : nu*beta^2 < (19/96 : ℝ) := (mul_lt_mul_of_pos_left hbs hnu).trans_eq hv'
  obtain ⟨tauR,htR,hRange⟩ := P4AFull87UnionPhysicalSupport.data_physical_range
    (width r) (width_pos r) n (data e q a) (by exact_mod_cast he.le)
    (nu*beta^2) (nu*beta) (mul_pos hnu (sq_pos_of_pos hb)) hbl
  refine ⟨beta,hb,hb8,hbM,homega,hbl,min tau0 tauR,lt_min ht0 htR,?_⟩
  intro tau ht hsmall
  have hboxed := (hRange tau ht (hsmall.trans (min_le_right _ _))).2
  refine ⟨fun N hN x => hboxed N N hN (cutoff N) (tags r n e q a N) x,?_⟩
  have hd : ∀ᶠ N : ℕ in atTop, Even N →
      let w := (N : ℝ)^(nu*beta^2)
      let L := (N : ℝ)^(nu*beta)
      physicalDensitySum (moduli N w) (rho r n e q a N w tau L) < upper r n e q a N w eta := by
    filter_upwards [hOrd,eventually_ge_atTop Nc] with N ho hc
    intro hev
    have hN2 := hNc.trans hc
    have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hz : (N : ℝ)^(nu*v) ≤ (N : ℝ) := by simpa only [hv'] using cutoff_le_target N hNR
    have h := (hpay N hc hev N hz tau ht (hsmall.trans (min_le_left _ _))).2.2
    dsimp only at h
    simp only [hv'] at h
    let w := (N : ℝ)^(nu*beta^2)
    let L := (N : ℝ)^(nu*beta)
    let scale := singularSeries N / Real.log (N : ℝ)
    let corr := p4aActualPresieveCorrection (tree r n e q a N false) N N w (cutoff N)
    change physicalDensitySum (moduli N w) (rho r n e q a N w tau L) <
      rawRoot (tree r n e q a N) N - corr + compilerReserve*scale at h
    have hor := unnormalize hN2 (ho hev)
    change rawRoot (tree r n e q a N) N < (beforeEight n e q a N - (savedGain : ℝ) + eta)*scale at hor
    change _ < (beforeEight n e q a N - (savedGain : ℝ) + eta + compilerReserve)*scale - corr
    nlinarith only [h,hor]
  refine ⟨hd,?_⟩
  intro b kappa hbpos hb1 hgap
  have hg := eventually_manuscript_sieve_gate hbpos (by norm_num : (0 : ℝ) ≤ 19/96) hgap
  filter_upwards [hg,hd,eventually_ge_atTop (2 : ℕ)] with N hg hdN hN2
  intro hev
  let w := (N : ℝ)^(nu*beta^2)
  let L := (N : ℝ)^(nu*beta)
  let T := manuscriptHalfProductCutoff kappa N
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hL : 1 < L := Real.one_lt_rpow hNR (mul_pos hnu hb)
  have hb1' : beta < 1 := hb8.trans (by norm_num)
  have hwL : w ≤ L := Real.rpow_le_rpow_of_exponent_le hNR.le
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_lt_mul_of_pos_left hb1' hb] : beta^2 ≤ beta) hnu.le)
  have hwz : w ≤ cutoff N := Real.rpow_le_rpow_of_exponent_le hNR.le homega.le
  have hc := RealB_cast_le_same_rho_main_add_distribution_of_gate N (Nat.ceil (cutoff N))
    (moduli N w) (rho r n e q a N w tau L) hbpos hb1 hg.1 hg.2
    (fun _ hm _ => compiled_modulus_dvd N w hwz hm)
    (P4AOriginalNewFifthCounting.actual_majorant r n e q a N (tags r n e q a N) w tau L
      hL hwL hwz (cutoff_le_target N hNR.le))
  have hm' := mul_le_mul_of_nonneg_left (hdN hev).le (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hc.trans (add_le_add_right (add_le_add_right (add_le_add_right hm' _) _) _)

end
end ImbalancedChen.P4AOriginalNewFifthPaidDensity
