import ImbalancedChen.P1OriginalFinalEighthWeightedFrontier
import ImbalancedChen.P1OriginalSharpFiniteReceiver
import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
import ImbalancedChen.P4AOriginalFull87UpperDispatch
import ImbalancedChen.P4AOriginalFiniteAll22Slots
import ImbalancedChen.P4AOriginalFiniteFallbackFinePPSchedule
import ImbalancedChen.P4BOriginalHighRankPostModulusCount

/-! Original eighth numerical saving on the final finite upper bank and
enlarged fifth tree, with actual missed prime tuples and the same physical
rectangle and counting coefficient. -/
namespace ImbalancedChen.P1OriginalFinite87PhysicalReserve
noncomputable section
open Filter VariableEnvelope
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P1OriginalFinalEighthWeightedFrontier (missed frontierTest cofinal_original_carriers)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFiniteFallbackPolicy (upper dispatch F rho)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFiniteAll22Slots (eighthSlots eighthSlots_le_original_integral)
open P5OriginalCommonPositivePresieve (normalize)
open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (mass)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOriginalHighRankPostModulusCount (band)
open P4BOriginalAllRankClassicalRange (wholeHigh)

/-- The actual predecessor has the same upper bank and stops the lower
chronology at the complete sixth. -/
def sixthRoot (m n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  rawRoot (dispatch N (upper (bank m) (data e q a) omega N) (orderedSixth n e q a omega N)) N

def eighthRaw (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :=
  p4aReserveRawDensity (F (bank m) (width r) n (data e q a) omega N) N N 0 (cutoff N)

def numericUpper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eta u_c : ℝ) (N : ℕ) :=
  let scale := singularSeries N/Real.log (N:ℝ)
  sixthRoot m n e q a omega N-eighthSlots*scale-
    p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N)
      N N ((N:ℝ)^omega) (cutoff N)+(eta+u_c)*scale

theorem unchanged_upper_sector (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ) :
    normalize N (sixthRoot m n e q a omega N-eighthRaw m r n e q a omega N)=
      normalize N (rawRoot (orderedSixth n e q a omega N) N-rawRoot (orderedEighth r n e q a omega N) N) := by
  have h := P4AOriginalFull87UpperDispatch.dispatch_eighth (width r) (width_pos r) n (data e q a) omega N
    (upper (bank m) (data e q a) omega N) (P4AOriginalFiniteFallbackOccurrence.positive _ _ _ _)
  rw [P4AOriginalOrderedSixthStages.ten_is_original_parent] at h
  exact h

/-- One beta and one aligned k. The explicit finite band is the actual
remaining signed prime-product distribution on this same rho. The
original missed weight is reported at H_N scale on both physical cuts. -/
theorem original_archive_and_physical_reserves {b kappa : ℝ} (hb : (1:ℝ)/2<b) (hb1 : b<1)
    (hk : 0<kappa) (kapMax : ℝ) (hmax : 0<kapMax) :
    ∃ kap : ℝ,0<kap ∧ kap<kapMax ∧ kap<1 ∧ kap<kappa/(4*(1+kappa)) ∧ 19/96<baseline b kap ∧
    ∀ K : ℕ,2≤K → ∀ eta etaSharp etaCount : ℝ,0<eta → 0<etaSharp → 0<etaCount →
    ∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧
    ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a : ℝ,0<a → a≤1/100 →
    ∀ (m : ℕ) (budget nu v u_c betaMax : ℝ),0<budget → 0<nu → 0<v → nu*v=19/96 →
    0<u_c → 0<betaMax → ∀ fineTolerance : ℝ→ℝ,(∀ beta : ℝ,0<beta → 0<fineTolerance beta) →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧ nu*beta^2<a ∧
    nu*beta<1/1000 ∧ nu*beta<budget/32 ∧ ∃ k : ℕ,
    alignedWidth (jointIndex (bank m) (data e q a).m) k≤fineTolerance beta ∧
    alignedWidth (jointIndex (bank m) (data e q a).m) k*
      ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤budget ∧
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let L := (N:ℝ)^(nu*beta)
      let z := cutoff N
      let Q := moduli N w
      let c := rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      let U := numericUpper m r n e q a omega eta u_c N
      let X := mass b kap (outerWidth N) N
      (∀ t : ℝ,t=0 ∨ t=w →
        0≤(∑ j : Cell,missed (bank m) r n e q a omega N N t z j)*singularNormalization N ∧
        (∑ j : Cell,missed (bank m) r n e q a omega N N t z j)*singularNormalization N<
          eta*singularNormalization N ∧
        eighthSlots-eta<∑ j : Cell,frontierTest (bank m) r n e q a omega N N t z j) ∧
      (∑ j : Cell,cellIntegral j)-eta<normalize N
        (sixthRoot m n e q a omega N-eighthRaw m r n e q a omega N) ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => [])
        N N w z tau L<u_c*singularNormalization N ∧
      physicalDensitySum Q c<U ∧
      (∀ d : ℕ,c d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      |P1OriginalSharpFiniteReceiver.literal N Q c-
        P4AOriginalFull87EighthPrimeMeanLedger.primeMass N*physicalDensitySum Q c-
        P1OriginalSharpFiniteReceiver.middle N Q c|≤etaSharp*singularNormalization N ∧
      0≤X ∧ |X/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<etaCount ∧
      ∀ zeta : ℝ,
        let R := (band b kap N K 0 kap zeta (wholeHigh m r n e q a omega k N (nu*beta)) c).re
        (RealB b N:ℝ)≤X*physicalDensitySum Q c+R+etaCount*singularNormalization N ∧
        (RealB b N:ℝ)≤X*U+R+etaCount*singularNormalization N := by
  obtain ⟨kap,hkp,hkm,hk1,hkg,hgate,hBand⟩ :=
    P4BOriginalHighRankPostModulusCount.exists_trimmed_RealB_le_band hb hb1 hk kapMax hmax
  refine ⟨kap,hkp,hkm,hk1,hkg,hgate,?_⟩
  intro K hK eta etaSharp etaCount he hsh hc
  obtain ⟨rW,hrW⟩ := cofinal_original_carriers eta he
  obtain ⟨rG,hrG⟩ := P4AOriginalR17Full87SavedEndpoint.original_ordinary_source eta he
  obtain ⟨NB,hNB⟩ := eventually_atTop.mp (((hBand K hK etaCount hc).and eventually_singularNormalization_pos).and
    (P1OriginalSharpFiniteReceiver.eventual_receiver etaSharp hsh))
  refine ⟨max rW rG,?_⟩
  intro r hr
  obtain ⟨nW,hnW⟩ := hrW r ((le_max_left _ _).trans hr)
  obtain ⟨nG,hnG⟩ := hrG r ((le_max_right _ _).trans hr)
  refine ⟨max nW nG,?_⟩
  intro n hn
  obtain ⟨_,EW,hEW,hW⟩ := hnW n ((le_max_left _ _).trans hn)
  obtain ⟨EG,hEG,hG⟩ := hnG n ((le_max_right _ _).trans hn)
  refine ⟨min EW EG,lt_min hEW hEG,?_⟩
  intro e hepos heE
  obtain ⟨qW,hqW,hWW⟩ := hW e hepos (heE.trans_le (min_le_left _ _))
  obtain ⟨qG,hqG,hGG⟩ := hG e hepos (heE.trans_le (min_le_right _ _))
  refine ⟨max qW qG,hqW.trans_le (le_max_left _ _),?_⟩
  intro q hq a ha ha1 m budget nu v uc bMax hbud hnu hv hvv huc hbMax fineTolerance hFine
  obtain ⟨NW,hNW,hWords⟩ := hWW q ((le_max_left _ _).trans hq) a ha1
  obtain ⟨NG,hNG,hGain⟩ := hGG q ((le_max_right _ _).trans hq) a ha1
  obtain ⟨beta,hbeta,hb8,hbm,hbsq,hwa,hell,hbBudget,k,hfine,hJ,NC,hNC,hCompiler⟩ :=
    P4AOriginalFiniteFallbackFinePPSchedule.joined (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m)
      r n e hepos.le q a ha budget hbud nu v uc bMax hnu hv hvv huc hbMax fineTolerance hFine
  refine ⟨beta,hbeta,hb8,hbm,hbsq,hwa,hell,hbBudget,k,hfine,hJ,max NC (max NG (max NW NB)),
    hNC.trans (le_max_left _ _),?_⟩
  intro N hN hev
  have hCN : NC≤N := by omega
  have hGN : NG≤N := by omega
  have hWN : NW≤N := by omega
  have hBN : NB≤N := by omega
  have h2 := hNC.trans hCN
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  let omega := nu*beta^2
  let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
  let w := (N:ℝ)^omega
  let L := (N:ℝ)^(nu*beta)
  let z := cutoff N
  let S := moduli N w
  let c := rho (bank m) r n e q a omega N tau L
  let A := sixthRoot m n e q a omega N
  let D := eighthRaw m r n e q a omega N
  let C := p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N) N N w z
  let scale := singularSeries N/Real.log (N:ℝ)
  let U := numericUpper m r n e q a omega eta uc N
  have hmu : (N:ℝ)^mu≤z := Real.rpow_le_rpow_of_exponent_le hNr.le (by norm_num [mu])
  have hz : z≤(N:ℝ) := by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hNr.le (show (19/96:ℝ)≤1 by norm_num)
  have hraw := hGain N hGN hev omega hwa.le N z hmu hz
  have hjoined : (∑ j : Cell,cellIntegral j)-eta<normalize N (A-D) :=
    hraw.trans_eq (unchanged_upper_sector m r n e q a omega N).symm
  obtain ⟨hfee,hden,hsupp,_⟩ := hCompiler N hCN hev
  change physicalDensitySum S c<D-C+uc*scale at hden
  have hcancel : normalize N (A-D)*scale=A-D := by
    dsimp only [normalize,scale]
    field_simp [(singularSeries_pos N).ne',(Real.log_pos hNr).ne'] <;> ring
  have hslot := (sub_le_sub_right eighthSlots_le_original_integral eta).trans_lt hjoined
  have hscale := mul_lt_mul_of_pos_right hslot (densityScale_pos h2)
  change (eighthSlots-eta)*scale<normalize N (A-D)*scale at hscale
  rw [hcancel] at hscale
  have hU : physicalDensitySum S c<U := by
    change physicalDensitySum S c<A-eighthSlots*scale-C+(eta+uc)*scale
    linarith only [hscale,hden]
  obtain ⟨⟨hband,hH⟩,hSharp⟩ := hNB N hBN
  obtain ⟨hX,happrox,hB⟩ := hband hev
  have hAP := hSharp hev S c (fun d hd => ⟨P4AUpperTaggedBetaAttachment.support_squarefree _ _ _ _ hd,
    P4AUpperTaggedBetaAttachment.support_coprime_target _ _ _ _ hd,
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d⟩)
  rw [P1OriginalSharpFiniteReceiver.above_eq_middle N S c (fun d _ => hsupp d),
    P1OriginalSharpFiniteReceiver.read_density,←P1OriginalSharpFiniteReceiver.same_normalization] at hAP
  refine ⟨?_,hjoined,hfee,hU,hsupp,hAP,hX,happrox,?_⟩
  · intro t ht
    obtain ⟨_,hp,hm,hfloor⟩ := hWords (bank m) nu beta hnu hbeta hb8 hell hwa.le N hWN t ht
    exact ⟨mul_nonneg hp hH.le,mul_lt_mul_of_pos_right hm hH,
      (sub_le_sub_right eighthSlots_le_original_integral eta).trans_lt hfloor⟩
  · intro zeta
    have hω : nu*beta^2≤19/96 := hvv ▸ mul_le_mul_of_nonneg_left hbsq.le hnu.le
    have h := hB zeta m r n e q a k nu beta hnu hbeta (hb8.le.trans (by norm_num))
      hω hell hsupp
    exact ⟨h,h.trans (add_le_add_right (add_le_add_right
      (mul_le_mul_of_nonneg_left hU.le hX) _) _)⟩

end
end ImbalancedChen.P1OriginalFinite87PhysicalReserve
