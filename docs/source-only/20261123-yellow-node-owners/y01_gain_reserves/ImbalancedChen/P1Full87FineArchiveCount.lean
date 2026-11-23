import ImbalancedChen.OriginalEighthCommonBetaWidthPayment
import ImbalancedChen.P4AHistoricalOneReserveDifference
import ImbalancedChen.P1OriginalFinite87PhysicalReserve
import ImbalancedChen.P4BOriginalFineAttachedUpper
import ImbalancedChen.P4BOriginalShortMediumCount

/-! Price the native Fourier count with the actual sum of all 87 integrals
on the same Fine witness as both upper densities. The compiler reserve
enters once, and the original presieve correction keeps its sign. -/
namespace ImbalancedChen.P1Full87FineArchiveCount
noncomputable section
open Filter Topology VariableEnvelope
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell Source)
open P4AOriginalFull87SevenCubeAdmission (point)
open P4AOriginalFull87HistoryCore (core width)
open P1OriginalFinalEighthMemberSupply (Supply)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (cutoff)
open P1OriginalFinite87PhysicalReserve (sixthRoot eighthRaw numericUpper unchanged_upper_sector)
open P1OriginalFinalEighthWeightedFrontier (missed frontierTest cofinal_original_carriers)
open P4AOriginalFiniteAll22Slots (eighthSlots eighthSlots_le_original_integral)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve)
open P4BOriginalFineAttachedUpper (Selection retention meshWidth compiledDensity attachedDensity)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4BOriginalCollisionWords (Params)
open P4BOriginalFiniteSmoothCount (mass)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOriginalShortMediumAtlas (remainingAtlas)
open P4BOriginalShortMediumFibreIntegral (WordRange)
open P5OriginalCommonPositivePresieve (normalize)

def integralUpper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eta : ℝ) (N : ℕ) : ℝ :=
  let scale := singularSeries N / Real.log (N : ℝ)
  sixthRoot m n e q a omega N - (∑ j : Cell, cellIntegral j) * scale -
    p4aActualPresieveCorrection (retention m r n e q a omega N)
      N N ((N : ℝ)^omega) (cutoff N) + (eta + compilerReserve) * scale

variable {m r n q : ℕ} {e : ℚ} {a nu v etaPP betaMax zeta : ℝ} {ft : ℝ → ℝ}

/-- The two quantities are tested on the same cap and both are uniformly
paid for any policies at the chosen beta. The second retains the actual
two signed first-exit corrections at the physical presieve. -/
def PairReserves (nu beta eta : ℝ) (N : ℕ) : Prop :=
  let w := (N : ℝ)^(nu*beta^2)
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  let X := (N : ℝ) / Real.log (N : ℝ)
  ∀ cap : ℕ, z ≤ (cap : ℝ) → ∀ old fresh : List ℕ → Bool,
    X * |OriginalEighthCommonBetaWidthPayment.widthTerm old fresh N cap w z L| ≤
      eta * singularNormalization N ∧
    X * |(p4aReservePhysicalDensity old N cap w z L - p4aReservePhysicalDensity fresh N cap w z L) -
      ((p4aReserveRawDensity old N cap 0 z - p4aReserveRawDensity fresh N cap 0 z) -
        (p4aActualPresieveCorrection old N cap w z - p4aActualPresieveCorrection fresh N cap w z))| ≤
      eta * singularNormalization N

private theorem reserves_below (nu v eta : ℝ) (hnu : 0 < nu) (hv : 0 < v)
    (hcut : nu*v = 19/96) (he : 0 < eta) :
    ∃ b : ℝ, 0 < b ∧ ∀ beta : ℝ, 0 < beta → beta < 1/8 → beta < b → beta^2 ≤ v →
      ∀ᶠ N : ℕ in atTop, Even N → PairReserves nu beta eta N := by
  obtain ⟨b, hb, h⟩ := OriginalEighthCommonBetaWidthPayment.exists_pair_target_error_reserve_below
    nu v eta hnu hv he
  refine ⟨b, hb, ?_⟩
  intro beta hpos h8 hsmall hsquare
  obtain ⟨N0, h2, hN0⟩ := h beta hpos h8 hsmall hsquare
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro hev cap hcap old fresh
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hcap' : (N : ℝ)^(nu*v) ≤ cap := by simpa only [hcut] using hcap
  obtain ⟨hw, hp⟩ := hN0 N hN hev cap hcap' old fresh
  dsimp only at hw hp
  rw [hcut] at hw hp
  let w := (N : ℝ)^(nu*beta^2)
  let z := cutoff N
  let L := (N : ℝ)^(nu*beta)
  have hwz : w ≤ z := by
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    rw [← hcut]
    exact mul_le_mul_of_nonneg_left hsquare hnu.le
  change |(p4aReservePhysicalDensity old N cap w z L - p4aReservePhysicalDensity fresh N cap w z L) -
    actualSmallEulerProduct N cap w * (p4aReserveRawDensity old N cap w z -
      p4aReserveRawDensity fresh N cap w z)| ≤ _ at hp
  rw [p4a_presievedDifference_eq_full_sub_corrections old fresh N cap w z hwz] at hp
  have scale_bound {x : ℝ} (hx : x ≤ eta * singularSeries N / Real.log (N : ℝ)) :
      ((N : ℝ) / Real.log (N : ℝ))*x ≤ eta*singularNormalization N := by
    have hX := div_nonneg (Nat.cast_nonneg N) (Real.log_pos hNr).le
    calc
      _ ≤ ((N : ℝ) / Real.log (N : ℝ))*(eta*singularSeries N / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hX
      _ = _ := by rw [← sourceMassScale_mul_densityScale N]; ring
  exact ⟨scale_bound hw, scale_bound hp⟩

/-- The original upper density appears with its native attached coefficient.
Only the pointwise density comparison is needed on that side. -/
def Archive (s : Selection m r n e q a nu v etaPP betaMax zeta ft) (eta : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, Even N →
    let omega := nu * s.beta ^ 2
    let w := (N : ℝ)^omega
    let z := cutoff N
    let I := ∑ j : Cell, cellIntegral j
    I - eta < normalize N (sixthRoot m n e q a omega N - eighthRaw m r n e q a omega N) ∧
    (∀ t : ℝ, t = 0 ∨ t = w →
      (∀ p : Fin 8 → ℕ, (∀ i, (p i).Prime) → (∀ i, ¬ p i ∣ N) → ∀ j : Cell,
        Source j (point (N:ℝ) p) → point (N:ℝ) p ∈ core (width r) →
        ∀ g : ℕ → ℝ, Supply (bank m) r n e q a omega N N t z g p j) ∧
      0 ≤ (∑ j : Cell, missed (bank m) r n e q a omega N N t z j) * singularNormalization N ∧
      (∑ j : Cell, missed (bank m) r n e q a omega N N t z j) * singularNormalization N <
        eta * singularNormalization N ∧
      I - eta < ∑ j : Cell, frontierTest (bank m) r n e q a omega N N t z j) ∧
    attachedDensity m r n e q a nu v s.beta N ≤ compiledDensity m r n e q a nu s.beta s.k N ∧
    compiledDensity m r n e q a nu s.beta s.k N < integralUpper m r n e q a omega eta N ∧
    integralUpper m r n e q a omega eta N ≤ numericUpper m r n e q a omega eta compilerReserve N ∧
    PairReserves nu s.beta eta N

private theorem fixed_price (s : Selection m r n e q a nu v etaPP betaMax zeta ft)
    {eta : ℝ} {N : ℕ} (hN : s.N0 ≤ N) (hev : Even N) (hnu : 0 < nu)
    (hcut : nu * v = 19/96)
    (hg : (∑ j : Cell, cellIntegral j) - eta < normalize N
      (sixthRoot m n e q a (nu*s.beta^2) N - eighthRaw m r n e q a (nu*s.beta^2) N)) :
    compiledDensity m r n e q a nu s.beta s.k N < integralUpper m r n e q a (nu*s.beta^2) eta N ∧
    integralUpper m r n e q a (nu*s.beta^2) eta N ≤
      numericUpper m r n e q a (nu*s.beta^2) eta compilerReserve N := by
  let omega := nu*s.beta^2
  let w := (N : ℝ)^omega
  let z := cutoff N
  let L := (N : ℝ)^(nu*s.beta)
  let tau := meshWidth m e q a s.k
  let f := retention m r n e q a omega N
  let scale := singularSeries N / Real.log (N : ℝ)
  let A := sixthRoot m n e q a omega N
  let D := eighthRaw m r n e q a omega N
  let C := p4aActualPresieveCorrection f N N w z
  let H := p4aReservePhysicalDensity f N N w z L
  let V := compiledDensity m r n e q a nu s.beta s.k N
  let I := ∑ j : Cell, cellIntegral j
  have h2 := s.two_le.trans hN
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hx : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hNr) (Real.log_pos hNr)
  have hscale : 0 < scale := densityScale_pos h2
  have hwz : w ≤ z := by
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    rw [← hcut]
    exact mul_le_mul_of_nonneg_left s.square_lt.le hnu.le
  have hcharged := (s.receipt N hN hev).2.2.1
  rw [← sourceMassScale_mul_densityScale N] at hcharged
  have hreorder : compilerReserve * (((N : ℝ) / Real.log (N : ℝ)) * scale) =
      ((N : ℝ) / Real.log (N : ℝ)) * (compilerReserve * scale) := by ring
  rw [hreorder] at hcharged
  have hfee := (mul_lt_mul_iff_right₀ hx).mp hcharged
  change H - actualSmallEulerProduct N N w * p4aReserveRawDensity f N N w z +
    |V - H| < compilerReserve * scale at hfee
  have hcorr := p4a_fullRaw_eq_euler_presieved_add_correction f N N w z hwz
  change D = actualSmallEulerProduct N N w * p4aReserveRawDensity f N N w z + C at hcorr
  have hden : V < D - C + compilerReserve * scale := by
    linarith only [hfee, hcorr, le_abs_self (V-H)]
  have hcancel : normalize N (A-D) * scale = A-D := by
    dsimp only [normalize, scale]
    field_simp [(singularSeries_pos N).ne', (Real.log_pos hNr).ne'] <;> ring
  have hgain := mul_lt_mul_of_pos_right hg hscale
  change (I-eta) * scale < normalize N (A-D) * scale at hgain
  rw [hcancel] at hgain
  have hslot := mul_le_mul_of_nonneg_right eighthSlots_le_original_integral hscale.le
  change V < A - I*scale - C + (eta+compilerReserve)*scale ∧
    A - I*scale - C + (eta+compilerReserve)*scale ≤ A - eighthSlots*scale - C +
      (eta+compilerReserve)*scale
  exact ⟨by linarith only [hgain, hden], by linarith only [hslot]⟩

/-- Intersect the original weighted-carrier and R17 schedules with the
existing Fine schedule. The three thresholds are combined before choosing
the rational strip and the final physical grid. -/
theorem exists_priced_selection (eta eMax : ℝ) (heta : 0 < eta) (hMax : 0 < eMax) :
    ∃ m0 : ℕ, ∀ m ≥ m0, ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧ ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E →
    ∀ a : ℝ, 0 < a → a ≤ 1/800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ, qMin ≤ q ∧ 0 < q ∧ 256 ∣ q ∧ mMin ≤ refinedMesh q ∧
    ∀ etaPP : ℝ, 0 < etaPP → etaPP ≤ P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ nu v betaMax zeta : ℝ, 0 < nu → 0 < v → nu*v = 19/96 → 0 < betaMax → 0 < zeta →
    ∀ ft : ℝ → ℝ, (∀ x : ℝ, 0 < x → 0 < ft x) →
      ∃ s : Selection m r n e q a nu v etaPP betaMax zeta ft, Archive s eta := by
  obtain ⟨mF, hF⟩ := P4BOriginalFineAttachedUpper.exists_fine_selection eMax hMax
  obtain ⟨rG, hG⟩ := P4AOriginalR17Full87SavedEndpoint.original_ordinary_source eta heta
  obtain ⟨rW, hW⟩ := cofinal_original_carriers eta heta
  refine ⟨mF, ?_⟩
  intro m hm
  obtain ⟨rF, hrF⟩ := hF m hm
  refine ⟨max rF (max rG rW), ?_⟩
  intro r hr
  obtain ⟨nF, hnF⟩ := hrF r (by omega)
  obtain ⟨nG, hnG⟩ := hG r (by omega)
  obtain ⟨nW, hnW⟩ := hW r (by omega)
  refine ⟨max nF (max nG nW), ?_⟩
  intro n hn
  obtain ⟨EF, hEF, hmax, heF⟩ := hnF n (by omega)
  obtain ⟨EG, hEG, heG⟩ := hnG n (by omega)
  obtain ⟨_, EW, hEW, heW⟩ := hnW n (by omega)
  refine ⟨min EF (min EG EW), lt_min hEF (lt_min hEG hEW), (min_le_left _ _).trans hmax, ?_⟩
  intro e he heE a ha haMax qMin mMin
  have heQ : (0 : ℚ) < e := by exact_mod_cast he
  obtain ⟨qG, _, hqG⟩ := heG e heQ (heE.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨qW, _, hqW⟩ := heW e heQ (heE.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨q, hqMin, hq, hd, hmesh, hchoose⟩ :=
    heF e he (heE.trans_le (min_le_left _ _)) a ha haMax (max qMin (max qG qW)) mMin
  have ha1 : a ≤ 1/100 := haMax.trans (by norm_num)
  obtain ⟨NG, _, hGain⟩ := hqG q (by omega) a ha1
  obtain ⟨NW, _, hWords⟩ := hqW q (by omega) a ha1
  refine ⟨q, by omega, hq, hd, hmesh, ?_⟩
  intro etaPP hPP hgap nu v betaMax zeta hnu hv hcut hb hz ft hft
  obtain ⟨B, hB, hPair⟩ := reserves_below nu v eta hnu hv hcut heta
  obtain ⟨u⟩ := hchoose etaPP hPP hgap nu v (min betaMax B) zeta hnu hv hcut
    (lt_min hb hB) hz ft hft
  let s : Selection m r n e q a nu v etaPP betaMax zeta ft :=
    ⟨u.beta, u.pos, u.lt_eighth, u.lt_ceiling.trans_le (min_le_left _ _), u.square_lt,
     u.omega_lt, u.small_lt, u.small_pp, u.small_extra, u.k, u.mesh_fine, u.mesh_pp,
     u.mesh_extra, u.N0, u.two_le, u.receipt⟩
  have hpair := hPair s.beta s.pos s.lt_eighth
    (u.lt_ceiling.trans_le (min_le_right _ _)) s.square_lt.le
  refine ⟨s, ?_⟩
  filter_upwards [eventually_ge_atTop s.N0, eventually_ge_atTop NG, eventually_ge_atTop NW,
    eventually_singularNormalization_pos, hpair] with N hN hgN hwN hH hRes
  intro hev
  let omega := nu*s.beta^2
  have h2 := s.two_le.trans hN
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hmu : (N : ℝ)^mu ≤ cutoff N :=
    Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [mu])
  have hcap : cutoff N ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (show (19/96 : ℝ) ≤ 1 by norm_num)
  have hraw := hGain N hgN hev omega s.omega_lt.le N (cutoff N) hmu hcap
  have hjoined : (∑ j : Cell, cellIntegral j)-eta <
      normalize N (sixthRoot m n e q a omega N - eighthRaw m r n e q a omega N) :=
    hraw.trans_eq (unchanged_upper_sector m r n e q a omega N).symm
  obtain ⟨hI, hU⟩ := fixed_price s hN hev hnu hcut hjoined
  refine ⟨hjoined, ?_, (s.receipt N hN hev).1, hI, hU, hRes hev⟩
  intro t ht
  obtain ⟨hSupply, hp, hm, hl⟩ := hWords (bank m) nu s.beta hnu s.pos s.lt_eighth s.small_lt
    s.omega_lt.le N hwN t ht
  exact ⟨hSupply, mul_nonneg hp hH.le, mul_lt_mul_of_pos_right hm hH, hl⟩

/-- On the priced selection, the original remaining signed Fourier row
and all its parameters are kept in the switched count. -/
theorem eventually_priced_count (s : Selection m r n e q a nu v etaPP betaMax zeta ft)
    {eta : ℝ} (hArchive : Archive s eta) (K : ℕ) (hK : 2 ≤ K) (he : 0 ≤ e)
    (he1 : (e : ℝ) ≤ 1/2048) (hq : 0 < q) (hnu : 0 < nu) (hcut : nu*v = 19/96)
    {b kappa kap0 : ℝ} (hb : (1/2 : ℝ) < b) (hb1 : b < 1)
    (hz : 0 < zeta) (hz0 : zeta ≤ 1/20000) (hk : 0 < kappa) (hkz : kappa ≤ zeta/200000)
    (ht : kap0 < kappa / (4*(1+kappa))) (hkap : 0 < kap0) (ht1 : kap0 < 1) :
    ∀ d : ℝ, 0 < d → ∀ᶠ N : ℕ in atTop, Even N →
      let omega := nu*s.beta^2
      let P : Params := ⟨m, r, n, e, q, a, omega, s.k, N, nu*s.beta⟩
      let M := mass b kap0 (outerWidth N) N
      let R := (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re
      let I := integralUpper m r n e q a omega eta N
      let U := numericUpper m r n e q a omega eta compilerReserve N
      (RealB b N : ℝ) ≤ M*I + R + d*singularNormalization N ∧
      (RealB b N : ℝ) ≤ M*U + R + d*singularNormalization N := by
  intro d hd
  have homega : nu*s.beta^2 ≤ 19/96 := by
    rw [← hcut]
    exact mul_le_mul_of_nonneg_left s.square_lt.le hnu.le
  have hgate := P4BOriginalFiniteSmoothSchedule.original_product_gap hb hk ht
  have hbound := P4BOriginalShortMediumCount.eventually_RealB_le_remaining K hK nu s.beta
    (meshWidth m e q a s.k) d hnu s.pos (s.lt_eighth.le.trans (by norm_num)) homega hd
    hz hz0 hk hkz ht ht1 hkap hb hb1 hgate
  filter_upwards [hbound, hArchive] with N hc haN
  intro hev
  let P : Params := ⟨m, r, n, e, q, a, nu*s.beta^2, s.k, N, nu*s.beta⟩
  have hW : WordRange P (nu*s.beta^2) (meshWidth m e q a s.k) zeta := by
    refine ⟨rfl, rfl, he, he1, hq, s.mesh_extra, (mul_pos hnu s.pos).le, ?_⟩
    change 2*(nu*s.beta) ≤ zeta/16
    linarith only [s.small_extra]
  obtain ⟨hm, _, hfinite⟩ := hc hev
  have hcount := hfinite m r n e q a s.k hW
  have hprices := (haN hev).2.2.2
  have hI := hcount.trans (add_le_add_right (add_le_add_right
    (mul_le_mul_of_nonneg_left hprices.1.le hm) _) _)
  exact ⟨hI, hI.trans (add_le_add_right (add_le_add_right
    (mul_le_mul_of_nonneg_left hprices.2.1 hm) _) _)⟩

end
end ImbalancedChen.P1Full87FineArchiveCount
