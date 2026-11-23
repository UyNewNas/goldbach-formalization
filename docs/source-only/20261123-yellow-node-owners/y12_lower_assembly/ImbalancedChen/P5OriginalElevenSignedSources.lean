import ImbalancedChen.P5OriginalFineSwitchedCosts
import ImbalancedChen.P5OriginalU5SharedAttachment
import ImbalancedChen.P5OriginalU5NativeRootCover
import ImbalancedChen.Part5OriginalH430AllTaggedHistoryUnits
import ImbalancedChen.P5JointNativeSignedRegroup
import ImbalancedChen.P5OriginalSameMaskPairedNativeGain
import ImbalancedChen.CurrentChenP5U6CausalLevelGeometry
import ImbalancedChen.CurrentChenOrdinaryInitialLedger
import ImbalancedChen.SingletonPrimeProductTransportP5

/-! The actual signed count on the manuscript mask. The two starts and the
two pair rows share the selected lower bank. All six switched prime-product
tests use the same Fine attachment. Finite signed discrepancies and density
evaluations that still have to be paid are terms in the resulting inequality. -/
namespace ImbalancedChen.P5OriginalElevenSignedSources
noncomputable section
open Classical Filter
open scoped BigOperators
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank select)
open P2OriginalLowerCompactStartCapConstructor (CompactStart boxedPlan startCutoff baselineCap)
open P2OriginalLowerNestedBufferedStages (JointCompactStarts)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P5OriginalFineSwitchedCosts (seventhError eighthError ninthError)
open P4BOriginalFineAttachedUpper (Selection)
open P5OriginalU5CausalFinite (fullProjectedMainSum)
open P5OriginalU5AllMarkHBReserves (branches)
open P5OriginalU5ClassicalComplement (beyond)
open P5JointNativeSignedRegroup (LowerData lowerRows mainTerm signedAP signedCentre fallback)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand originalReceiver)
open Part5OriginalH430AllTaggedHistoryUnits (units)
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open P5U6CausalLevelGeometry (attachedSmallCutoff attachedSmallLevel residual physicalLevel)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)

abbrev adoptedMask (N : ℕ) := Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)

def startingDomain (R : PairRange) (j : Fin 2) : CompactStart :=
  (⟨R.epsilon,R.epsilon_pos,R.epsilon_lt_a⟩ : JointCompactStarts).at j

def startingPolicy (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    (j : Fin 2) (N : ℕ) : List ℕ → Bool :=
  let S := startingDomain R j
  P2LowerCapPlanIntegerRetention.retainEven (boxedPlan S (select S bank buffer) buffer buffer)
    (S.epsilon : ℝ) (startCutoff S.start : ℝ) (baselineCap buffer) N

/-- A complete physical starting row, with the original prime prefix and
its explicit prime and centre correction cost. -/
def startingValue (N : ℕ) (z w L : ℝ) (policy : List ℕ → Bool) : ℝ :=
  let cap := Nat.ceil z
  let Q := actualLowerSmallRoughModuli policy N cap w z
  let c := actualLowerSmallRoughRho policy N cap w z L
  let S := P5S1OriginalLower.active policy N cap w z L
  ((chenAdditivePrimeCarrier N).card : ℝ) * physicalDensitySum Q c +
    Part3.primeProductSignedError 1 N N S c (P5S1SingletonPP.singletonWeight N (fun _ => 1)) -
    chenInitialCorrectionCost N S

def startFloor (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (β δ : ℝ) (j : Fin 2) (N : ℕ) : ℝ :=
  let v := (startCutoff (startingDomain R j).start : ℝ)
  let ν := baselineCap buffer
  max ((currentChenOrdinaryInitialConstant v - δ)*singularNormalization N)
    (startingValue N ((N:ℝ)^v) ((N:ℝ)^(ν*β^2)) ((N:ℝ)^(ν*β)) (startingPolicy R bank buffer j N))

theorem two_starts_at (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) {buffer : ℚ}
    (hb : 0≤buffer) (hub : buffer≤1/1000) {β δ : ℝ} (hβ : 0<β) (hβ8 : β<1/8)
    {N : ℕ} (hN : 2≤N) (hev : Even N)
    (h1 : (currentChenOrdinaryInitialConstant (417/5000) - δ)*singularNormalization N ≤ currentChenUpsilon1 N)
    (h2 : (currentChenOrdinaryInitialConstant (19/125) - δ)*singularNormalization N ≤ currentChenUpsilon2 N) :
      3*startFloor R bank buffer β δ 0 N + startFloor R bank buffer β δ 1 N ≤
        3*currentChenUpsilon1 N + currentChenUpsilon2 N := by
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hbR : (0:ℝ)≤buffer := by exact_mod_cast hb
  have hubR : (buffer:ℝ)≤1/1000 := by exact_mod_cast hub
  have hν : 0<baselineCap buffer := by dsimp [baselineCap]; linarith
  have huν : baselineCap buffer ≤ 1 := by dsimp [baselineCap]; linarith
  have hsq : β^2 ≤ (1/8:ℝ)*(1/8) := by
    simpa only [pow_two] using mul_self_le_mul_self hβ.le hβ8.le
  have hw : baselineCap buffer * β^2 ≤ 417/5000 :=
    (mul_le_mul huν hsq (sq_nonneg _) zero_le_one).trans (by norm_num)
  have hbb : β^2≤β := by nlinarith only [mul_nonneg hβ.le (show 0≤1-β by linarith)]
  have hf (v : ℝ) (hv : (417/5000:ℝ) ≤ v) (f : List ℕ → Bool) :
      startingValue N ((N:ℝ)^v) ((N:ℝ)^(baselineCap buffer*β^2)) ((N:ℝ)^(baselineCap buffer*β)) f ≤
        ((chenSiftedPrimeSource N ((N:ℝ)^v)).card:ℝ) := by
    unfold startingValue
    rw [P5S1SingletonPP.primeProductSignedError_singleton_eq]
    apply P5S1OriginalLower.causal_primitive_lower _ _ _ _ _ _ hev
      (Real.one_lt_rpow hn (mul_pos hν hβ))
      (Real.rpow_le_rpow_of_exponent_le hn.le (mul_le_mul_of_nonneg_left hbb hν.le))
      (Real.rpow_le_rpow_of_exponent_le hn.le (hw.trans hv)) (Nat.le_ceil _)
  have hs1 := hf (417/5000) le_rfl (startingPolicy R bank buffer 0 N)
  have hs2 := hf (19/125) (by norm_num) (startingPolicy R bank buffer 1 N)
  rw [←currentChenUpsilon1_eq_actual_sifted_card N hev] at hs1
  rw [←currentChenUpsilon2_eq_actual_sifted_card N hev] at hs2
  have hm1 : startFloor R bank buffer β δ 0 N ≤ currentChenUpsilon1 N :=
    max_le h1 hs1
  have hm2 : startFloor R bank buffer β δ 1 N ≤ currentChenUpsilon2 N :=
    max_le h2 hs2
  linarith only [hm1,hm2]

/-- Both original tagged roots retain every rough quotient, including all
overlap and rejected-position debt. Each root uses its own actual Q. -/
def historyCost (N n m : ℕ) (t : ℝ) : ℝ :=
  (∑ p ∈ originalBand N .U3, units N n m .U3 t p) +
    ∑ p ∈ originalBand N .U4, units N n m .U4 t p

theorem history_cost_eq {N n m : ℕ} {t : ℝ} (hN : 2≤N) (ht : 0≤t)
    (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) :
    currentChenUpsilon3 N + currentChenUpsilon4 N = historyCost N n m t := by
  rw [Part5OriginalH430TaggedArithmeticReceivers.original_U34_eq_tagged_card,
    Part5OriginalH430TaggedArithmeticReceivers.original_tagged_card]
  simp only [Nat.cast_add,Nat.cast_sum]
  unfold historyCost
  apply congrArg₂ (·+·)
  · exact Finset.sum_congr rfl (fun p hp =>
      (Part5OriginalH430AllTaggedHistoryUnits.units_eq hN ht hu hn hp).symm)
  · exact Finset.sum_congr rfl (fun p hp =>
      (Part5OriginalH430AllTaggedHistoryUnits.units_eq hN ht hu hn hp).symm)

def sixth (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ) (β : ℝ) (N : ℕ) :
    LowerData := ⟨selectedPolicy R bank buffer true N, attachedSmallCutoff N β, attachedSmallLevel N β⟩

/-- At an uncropped sixth row only the three elementary attachment gates
are needed by the finite lower polynomial. They already hold on the entire
half-open rectangle for its original, piecewise physical residual. -/
theorem sixth_all_gates (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (buffer : ℚ)
    {N : ℕ} (hN : 2≤N) {β : ℝ} (hβ : 0<β) (hβ8 : β<1/8) (E : ℕ × ℕ → Prop)
    {t : ℕ × ℕ} (ht : t ∈ lowerRows N E) :
    let D := sixth R bank buffer β N
    1<D.L t ∧ D.w t≤D.L t ∧ D.w t≤P5CausalRhoQuotientBridge.cutoff N := by
  let x := currentChenUpsilon6LogCoordinates N t
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  obtain ⟨hc,ha,hh,hb,hd⟩ := Finset.mem_filter.mp ((Finset.mem_filter.mp ht).1)
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hc
  have hpow (p : ℕ) (hp : 0<p) : (N:ℝ)^(Real.log (p:ℝ)/Real.log (N:ℝ)) = p := by
    apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hNr) (by exact_mod_cast hp)).mp
    exact div_mul_cancel₀ _ (Real.log_pos hNr).ne'
  have hp0 : (N:ℝ)^(x 0) = (t.1:ℝ) := hpow _ (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hp1 : (N:ℝ)^(x 1) = (t.2:ℝ) := hpow _ (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  rw [←hp0] at ha hh
  rw [←hp1] at hb hd
  have h0 := (Real.rpow_le_rpow_left_iff hNr).mp ha
  have h1 := (Real.rpow_lt_rpow_left_iff hNr).mp hh
  have h2 := (Real.rpow_le_rpow_left_iff hNr).mp hb
  have h3 := (Real.rpow_lt_rpow_left_iff hNr).mp hd
  have hv := P5U6CausalLevelGeometry.physicalLevel_bounds h0 h1.le h2 h3.le
  have hR : 0<residual x := by dsimp [residual]; linarith only [hv.1,h1,h3]
  have huR : residual x ≤ 1/2 := by dsimp [residual]; linarith only [hv.2,h0,h2]
  have hbb : β^2≤β := by nlinarith only [mul_nonneg hβ.le (show 0≤1-β by linarith)]
  have hsq : β^2 ≤ (1/8:ℝ)*(1/8) := by
    simpa only [pow_two] using mul_self_le_mul_self hβ.le hβ8.le
  have hcap : residual x*β^2 ≤ 417/5000 :=
    (mul_le_mul huR hsq (sq_nonneg _) (by norm_num)).trans (by norm_num)
  exact ⟨Real.one_lt_rpow hNr (mul_pos hR hβ), Real.rpow_le_rpow_of_exponent_le hNr.le
    (mul_le_mul_of_nonneg_left hbb hR.le), Real.rpow_le_rpow_of_exponent_le hNr.le hcap⟩

def jointValue (D : LowerData) (grid N : ℕ) (η : ℚ) : ℝ :=
  mainTerm D grid N η (adoptedMask N) (trueLogarithmicIntegral N) +
    signedAP D grid N η (adoptedMask N) (trueLogarithmicIntegral N) -
    signedCentre D grid N η (adoptedMask N) - fallback grid N (adoptedMask N)

def fifthValue (t τ ζ B β : ℝ) (K N : ℕ) (P : P5OriginalU5PlateauPrimeBV.Policy) : ℝ :=
  fullProjectedMainSum N P + (branches t τ ζ 6 N K β P (beyond B N β P)).re

/-- The five real tolerances remain independent. Inside each sufficiently
large even N the result holds for every native bank, every retained history
grid and every joint near-cap grid. Six upper errors are signed and keep
their actual Fine Q and rho. -/
theorem exists_common_original_signed_count
    (a extra βmax : ℝ) (ha : 0<a) (ha' : a≤1/800) (he : 0<extra) (hβmax : 0<βmax)
    (ft : ℝ→ℝ) (hft : ∀ x : ℝ, 0<x → 0<ft x) (qMin mMin : ℕ)
    {δs δ5 δ7 δ8 δ9 : ℝ} (hs : 0<δs) (h5 : 0<δ5) (h7 : 0<δ7) (h8 : 0<δ8) (h9 : 0<δ9)
    (t τ : ℝ) (ht : 0<t) (hu : t<1) (hτ : t<τ) (K : ℕ)
    {buffer : ℚ} (hb : 0<buffer) (hub : buffer≤1/1000) :
    ∃ B ceiling : ℝ, 0≤B ∧ 0<ceiling ∧ ceiling≤βmax ∧ ceiling≤(buffer:ℝ) ∧
    ∃ (m r n : ℕ) (e : ℚ) (q : ℕ) (ηPP : ℝ),
      0<e ∧ (e:ℝ)<1/2048 ∧ qMin≤q ∧ 0<q ∧ 256∣q ∧ mMin≤refinedMesh q ∧
      0<ηPP ∧ ηPP≤P4AOriginalFiniteFallbackCommonGroups.gap m (P4AOriginalNewFifthUnion.data e q a) ∧
      ∃ s : Selection m r n e q a 1 (19/96) ηPP ceiling extra ft,
        ∀ᶠ N : ℕ in atTop, Even N →
        ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh) (ζ : ℝ)
          (nH mH grid : ℕ) (tH : ℝ) (ηJ : ℚ),
          0≤tH → tH≤1/12 → 1/((nH:ℝ)+1)≤11/384 → 0<ηJ →
          3*startFloor R bank buffer s.beta δs 0 N + startFloor R bank buffer s.beta δs 1 N -
            historyCost N nH mH tH +
            (fifthValue t τ ζ B s.beta K N (selectedPolicy R bank buffer false N) - δ5*singularNormalization N) +
            jointValue (sixth R bank buffer s.beta N) grid N ηJ -
            2*((currentK*p5U7OriginalOmegaIntegral 1+δ7)*singularNormalization N + seventhError s N) -
            ((currentK*currentChenUpsilon8HarmonicIntegral+δ8)*singularNormalization N + eighthError s N) -
            ((currentK*currentChenUpsilon9HarmonicIntegral+δ9)*singularNormalization N + ninthError s N)
            ≤ currentChenPairedPrimeSum N (adoptedMask N) := by
  obtain ⟨b,hb',B,hB,hfifth⟩ := P5OriginalU5SharedAttachment.normalized_count_for_every_small_beta
    t τ ht hu hτ K h5
  let ceiling := min (min βmax (buffer:ℝ)) b
  have hc : 0<ceiling := lt_min (lt_min hβmax (by exact_mod_cast hb)) hb'
  obtain ⟨m,r,n,e,q,ηPP,he0,he',hq,hq0,hd,hm,hη,hgap,⟨s⟩⟩ :=
    P4BOriginalFineAttachedUpper.exists_counting_selection a extra ceiling ha ha' he hc ft hft qMin mMin
  refine ⟨B,ceiling,hB,hc,(min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _),m,r,n,e,q,ηPP,he0,he',hq,hq0,hd,hm,hη,hgap,s,?_⟩
  have hf := hfifth s.beta s.pos s.lt_eighth (s.lt_ceiling.trans_le (min_le_right _ _))
  have hupp := P5OriginalFineSwitchedCosts.three_costs s he0.le zero_lt_one (by norm_num) h7 h8 h9
  filter_upwards [hf,hupp,eventually_currentChenUpsilon1_ge_ordinary_mean δs hs,
    eventually_currentChenUpsilon2_ge_ordinary_mean δs hs,eventually_ge_atTop (2:ℕ)]
    with N h5N h789N ho1 ho2 hN
  intro hev R mesh bank ζ nH mH grid tH ηJ htH huH hnH hηJ
  have hstart := two_starts_at R bank hb.le hub s.pos s.lt_eighth hN hev (ho1 hev) (ho2 hev)
  have hhist := history_cost_eq (m:=mH) hN htH huH hnH
  have h6j := P5JointNativeSignedRegroup.original_paired_lower_same_sigma (n:=grid)
    (sixth R bank buffer s.beta N) (by omega) hηJ (adoptedMask N) (trueLogarithmicIntegral N)
    (fun _ hp => sixth_all_gates R bank buffer hN s.pos s.lt_eighth (adoptedMask N) hp)
  obtain ⟨hu7,hu8,hu9⟩ := h789N hev
  have hfN := h5N hev (selectedPolicy R bank buffer false N) ζ
  dsimp only [P5JointNativeSignedRegroup.otherRows] at h6j
  dsimp only [jointValue,fifthValue]
  linarith only [hstart,hhist,hfN,h6j,hu7,hu8,hu9]

end
end ImbalancedChen.P5OriginalElevenSignedSources
