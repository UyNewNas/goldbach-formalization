import ImbalancedChen.P4BOriginalFiniteSignedTrim
import ImbalancedChen.P4BOriginalFiniteSmoothSchedule
import ImbalancedChen.P4AOriginalFiniteFallbackCanonical
import ImbalancedChen.P5zElevenErrorTransport

/-! Count on the literal trim of the original labelled-prime pair, with the
same finite high fallback, ordered third, enlarged fifth and rectangle.
The exact remaining HB expression uses the two original medium branches
and the signed proper-power correction. -/
namespace ImbalancedChen.P4BOriginalFiniteTrimmedCount
noncomputable section
open Classical Filter
open scoped BigOperators

open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (Q coefficient weight mass)
open P4BOriginalFiniteSignedTrim (trimmedWeight pairLicence)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalNewFifthUnion (data)
open P4AFallbackCanonicalBanks (bank)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (roughPrimeReserve properPowerReserve)
open P5Z.OriginalPrimeAtlasReserveBranches
  (mediumAtlas noMediumAtlas originalMediumLow originalMediumHigh original_prime_discrepancy_mode_carriers)

/-- One pre-target tolerance for a given coarse bank and physical exponents.
Every aligned index satisfying it inherits the range proved for the actual
rectangle. No new beta or aligned index is selected in this statement. -/
theorem exists_fine_tolerance (m r n : ℕ) (e : ℚ) (he : 0≤e) (q : ℕ)
    (a omega ell : ℝ) (hw : 0<omega) (hL : ell<1/1000) :
    ∃ t : ℝ,0<t ∧ ∀ k : ℕ,alignedWidth (jointIndex (bank m) (data e q a).m) k≤t →
      ∀ N : ℕ,2≤N → ∀ d : ℕ,
      coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
      (d:ℝ)<(N:ℝ)^(599/1000:ℝ) := by
  obtain ⟨t,ht,H⟩ := P4AOriginalFiniteFallbackPhysicalRange.data_physical_range
    (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m)
    (P4AOriginalFull87HistoryCore.width r) (P4AOriginalFull87HistoryCore.width_pos r) n
    (data e q a) he omega ell hw hL
  refine ⟨t,ht,?_⟩
  intro k hk N hN
  let M := jointIndex (bank m) (data e q a).m
  have hp : 0<alignedWidth M k :=
    div_pos (logPrimeMeshStep_pos (by norm_num : (0:ℝ)<19/96) M) (by positivity)
  exact (H (alignedWidth M k) hp hk).2 N N hN
    (P4AOriginalFull87RawChronology.cutoff N) (fun _ => [])

/-- The independent low-product transfer has every prescribed logarithmic
accuracy on all sufficiently fine aligned rectangles of this actual bank.
The test threshold depends only on the trim exponent, A and tolerance. -/
theorem eventually_original_trim_on_fine_rectangles (kappa0 : ℝ)
    (hk : 0<kappa0) (hk1 : kappa0<1) (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ (m r n : ℕ) (e : ℚ),0≤e → ∀ (q : ℕ) (a omega ell : ℝ),
      0<omega → ell<1/1000 → ∃ t : ℝ,0<t ∧
      ∀ k : ℕ,alignedWidth (jointIndex (bank m) (data e q a).m) k≤t →
      ∀ N≥N0,∀ b kappa s : ℝ,0<b → 0<s → 2*s≤baseline b kappa-19/96 →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      |Part3.primeProductSignedError 2 N N (Q omega N) c (weight b kappa s N)-
        Part3.primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kappa s kappa0 N)|
        ≤delta*(N:ℝ)/Real.log (N:ℝ)^A := by
  obtain ⟨Ns,Hs⟩ := eventually_atTop.mp
    (P4BOriginalFiniteSignedTrim.eventually_signed_trim kappa0 hk hk1 A delta hd)
  refine ⟨max 2 Ns,le_max_left _ _,?_⟩
  intro m r n e he q a omega ell hw hL
  obtain ⟨t,ht,Ht⟩ := exists_fine_tolerance m r n e he q a omega ell hw hL
  refine ⟨t,ht,?_⟩
  intro k hk' N hN b kappa s hb hs hgap
  exact Hs N ((le_max_right 2 Ns).trans hN) b kappa s hb hs hgap m r n e q a omega k
    ((N:ℝ)^ell) (Ht k hk' N ((le_max_left 2 Ns).trans hN))

/-- On any simultaneously selected physical coefficient with its printed
599/1000 range, the *same* mass X_s multiplies the density; the signed
test is the literal eta-completed independent profile. The two integer
endpoints and the signed trim share one prescribed additive eta H_N. -/
theorem exists_same_coefficient_trimmed_count {b kappa0 : ℝ}
    (hb : (1:ℝ)/2<b) (hb1 : b<1) (hk : 0<kappa0) (hk1 : kappa0<1)
    (hgate : (19/96:ℝ)<baseline b kappa0)
    (eta sMax : ℝ) (heta : 0<eta) (hsMax : 0<sMax) :
    ∃ s0 : ℝ,0<s0 ∧ s0≤sMax ∧ ∃ N0 : ℕ,2≤N0 ∧
    ∀ s : ℝ,0<s → s≤s0 → ∀ N≥N0,Even N →
      0≤mass b kappa0 s N ∧
      |mass b kappa0 s N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (nu beta : ℝ),
        0<nu → 0<beta → beta≤1 → nu*beta^2≤19/96 →
        let omega := nu*beta^2
        let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
        (∀ d : ℕ,c d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) →
        (RealB b N:ℝ)≤mass b kappa0 s N*physicalDensitySum (Q omega N) c+
          Part3.primeProductSignedError 2 N N (Q omega N) c (trimmedWeight b kappa0 s kappa0 N)+
          eta*singularNormalization N := by
  let h := (baseline b kappa0-19/96)/2
  have hpos : 0<h := half_pos (sub_pos.mpr hgate)
  obtain ⟨s0,hs0,hmax,Nc,hNc,Hc⟩ :=
    P4BOriginalFiniteSmoothSchedule.exists_same_coefficient_count
      hb hb1 hk hk1 hgate (eta/2) (min sMax h) (half_pos heta) (lt_min hsMax hpos)
  obtain ⟨Nt,Ht⟩ := eventually_atTop.mp
    (P4BOriginalFiniteSignedTrim.eventually_signed_trim kappa0 hk hk1 3 1 (by norm_num))
  obtain ⟨Ne,He⟩ := eventually_atTop.mp
    (p5z_eventually_logCube_le_singularNormalization 1 (eta/2) (half_pos heta))
  refine ⟨s0,hs0,hmax.trans (min_le_left _ _),max Nc (max Nt Ne),
    hNc.trans (le_max_left _ _),?_⟩
  intro s hs hss N hN hev
  have hcs := (le_max_left Nc (max Nt Ne)).trans hN
  have hts := (le_max_right Nc (max Nt Ne)).trans hN
  obtain ⟨hX,hprec,hcount⟩ := Hc s hs hss N hcs hev
  have hs' := hss.trans (hmax.trans (min_le_right _ _))
  have hgap : 2*s≤baseline b kappa0-19/96 := by
    dsimp only [h] at hs'
    linarith
  refine ⟨hX,hprec.trans (by linarith),?_⟩
  intro m r n e q a k nu beta hnu hp hone hw
  dsimp only
  intro hactive
  have ht := Ht N ((le_max_left Nt Ne).trans hts) b kappa0 s (by linarith) hs hgap
    m r n e q a (nu*beta^2) k ((N:ℝ)^(nu*beta)) hactive
  have hdis := (le_abs_self _).trans (ht.trans (He N ((le_max_right Nt Ne).trans hts)))
  have hroot := hcount m r n e q a k nu beta hnu hp hone hw
  dsimp only at hroot
  linarith only [hdis,hroot]

/-- The trimmed physical discrepancy equals the original medium and
no-medium complete-word sums with the original signed proper-power
correction. Every labelled chart uses precisely the same Q and c. -/
theorem eventually_trimmed_exact_atlas (K : ℕ) (hK : 2≤K)
    {b kappa : ℝ} (hb : 0<b) :
    ∀ᶠ N : ℕ in atTop,∀ s : ℝ,∀ hs : 0<s,∀ hgap : 2*s≤baseline b kappa-19/96,
      ∀ (kappa0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (level : ℝ),
      let L := pairLicence hb hs hgap N
      let S := Q omega N
      let c := coefficient m r n e q a omega k N level
      let cc := fun d => (c d:ℂ)
      (Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℂ) =
        ∑ js∈chartBank N 2,
          (mediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js+
           noMediumAtlas L K N N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S cc js-
           properPowerReserve L K N N kappa0 S cc js) := by
  obtain ⟨Nr,Hr⟩ := P4BActualUpperRoughPrimeReserveZero.exists_actual_upper_roughPrimeReserve_zero
    (kappa:=kappa) K hK hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
  filter_upwards [eventually_ge_atTop Nr,eventually_ge_atTop (2:ℕ)] with N hNr hN
  intro s hs hgap kappa0 zeta m r n e q a omega k level
  let L := pairLicence hb hs hgap N
  let S := Q omega N
  let c := coefficient m r n e q a omega k N level
  let cc := fun d => (c d:ℂ)
  have ha := original_prime_discrepancy_mode_carriers L K N N kappa0 zeta S c
  rw [← P4BArbitraryWidthUpperPairProfile.original_signed_source b kappa s hN S c] at ha
  have hr : ∀ js∈chartBank N 2,roughPrimeReserve L K N N kappa0 S cc js=0 :=
    Hr N hNr s hs (by simpa only [one_mul] using hgap) kappa0 S cc
  have hz : (∑ js∈chartBank N 2,roughPrimeReserve L K N N kappa0 S cc js)=0 :=
    Finset.sum_eq_zero hr
  rw [Finset.sum_add_distrib,hz,add_zero] at ha
  have hd := P4BOriginalFiniteSignedTrim.difference_eq_trim hb hs hgap hN kappa0 S c
  rw [Complex.ofReal_sub] at hd
  change (Part3.primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N):ℂ) = _
  linear_combination ha - hd

end
end ImbalancedChen.P4BOriginalFiniteTrimmedCount
