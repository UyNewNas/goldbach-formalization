import ImbalancedChen.P4AOriginalR17EighthSignedTransport
import ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint

/-! Original 87 physical integrals and all eight archived slots on the
R17-corrected whole-third tree. The physical third cutoff can be taken
after the common mesh. The ordinary threshold is uniform for omega ≤ a. -/
namespace ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope (mu)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalFull87ActualSavedEndpoint (Scheduled)
open P4AOriginalFull87UnionHistory (sixthPolicy policy)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87OrdinarySignedGain (common_history_on_trim)
open P4AOriginalR17EighthParent (orderedSixth orderedEighth)
open P4AOriginalR17EighthSignedTransport (raw_difference)
open P4AOriginalVariableFifthPhysicalLedger (raw physical)
open P5OriginalCommonPositivePresieve (normalize)

def Ordinary (gain eps : ℝ) : Prop :=
  Scheduled (fun r n e q a N => ∀ omega : ℝ, omega≤a →
    ∀ (cap : ℕ) (z : ℝ), (N:ℝ)^mu≤z → z≤cap →
      gain-eps<normalize N (raw (orderedSixth n e q a omega N) N cap 0 z -
        raw (orderedEighth r n e q a omega N) N cap 0 z))

def PositivePresieve (gain nu eps betaMax : ℝ) : Prop :=
  ∃ beta : ℝ, 0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2≤(19/96:ℝ)/nu ∧
    Scheduled (fun r n e q a N => ∀ omega : ℝ, omega≤a →
      ∀ cap : ℕ, (N:ℝ)^(19/96:ℝ)≤cap →
      let w := (N:ℝ)^(nu*beta^2)
      let z := (N:ℝ)^(19/96:ℝ)
      let L := (N:ℝ)^(nu*beta)
      1<w ∧ w≤z ∧ normalize N (physical (orderedEighth r n e q a omega N) N cap w z L) <
        normalize N (raw (orderedSixth n e q a omega N) N cap 0 z)-gain+eps)

/-- Refine only the existing common third mesh thresholds. The signed
coefficient equality then holds at every modulus of the later carrier. -/
private theorem with_common_history (gain eps : ℝ)
    (h : Scheduled (fun r n e q a N => ∀ (cap : ℕ) (z : ℝ), (N:ℝ)^mu≤z → z≤cap →
      gain-eps<normalize N (raw (sixthPolicy n e q a N) N cap 0 z -
        raw (policy (width r) n e q a N) N cap 0 z))) :
    Ordinary gain eps := by
  obtain ⟨r0,hr⟩ := h
  refine ⟨r0,?_⟩
  intro r hrr
  obtain ⟨n0,hn⟩ := hr r hrr
  obtain ⟨eh,heh,hist⟩ := common_history_on_trim r
  refine ⟨n0,?_⟩
  intro n hnn
  obtain ⟨eo,heo,hgain⟩ := hn n hnn
  refine ⟨min eo eh,lt_min heo heh,?_⟩
  intro e he he0
  obtain ⟨qo,hqo,hg⟩ := hgain e he (he0.trans_le (min_le_left _ _))
  obtain ⟨qh,hqh,hh⟩ := hist e he (he0.trans_le (min_le_right _ _))
  refine ⟨max qo qh,hqo.trans_le (le_max_left _ _),?_⟩
  intro q hqq a ha
  obtain ⟨N0,hN0,hN⟩ := hg q ((le_max_left _ _).trans hqq) a ha
  have hreal := hh q ((le_max_right _ _).trans hqq) a ha
  refine ⟨N0,hN0,?_⟩
  intro N hNN hEven omega hc cap z hz hcap
  have h2 := hN0.trans hNN
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  rw [raw_difference r n e q a omega he.le hc hreal N hNr cap 0 z]
  exact hN N hNN hEven cap z hz hcap

theorem original_ordinary_source (eps : ℝ) (heps : 0<eps) :
    Ordinary (∑ c : Cell,cellIntegral c) eps :=
  with_common_history _ eps (P4AOriginalFull87UnionActualGain.exists_ordinary_source_gain eps heps)

theorem original_ordinary_saved (eps : ℝ) (heps : 0<eps) :
    Ordinary (savedGain:ℝ) eps :=
  with_common_history _ eps (P4AOriginalFull87ActualSavedEndpoint.union_ordinary_saved_gain eps heps)

private theorem positive_projection (gain nu eps betaMax : ℝ) (hnu : 0<nu)
    (heps : 0<eps) (hmax : 0<betaMax) (hOrd : Ordinary gain (eps/2)) :
    PositivePresieve gain nu eps betaMax := by
  have hnr : nu*((19/96:ℝ)/nu)=(19/96:ℝ) := by field_simp [hnu.ne'] <;> ring
  obtain ⟨beta,hb,hb8,hbmax,hbr,Nb,_,hbeta⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve nu ((19/96:ℝ)/nu) (eps/2) betaMax
      hnu (div_pos (by norm_num) hnu) (half_pos heps) hmax
  obtain ⟨r0,hr⟩ := hOrd
  refine ⟨beta,hb,hb8,hbmax,hbr,r0,?_⟩
  intro r hrr
  obtain ⟨n0,hn⟩ := hr r hrr
  refine ⟨n0,?_⟩
  intro n hnn
  obtain ⟨e0,he0,he⟩ := hn n hnn
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq a ha
  obtain ⟨Na,hNa,hold⟩ := hq q hqq a ha
  refine ⟨max Na Nb,hNa.trans (le_max_left _ _),?_⟩
  intro N hN hEven omega hcut cap hcap
  have h2 : 2≤N := hNa.trans ((le_max_left _ _).trans hN)
  have hNr : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hz := Real.rpow_le_rpow_of_exponent_le hNr.le (show mu≤(19/96:ℝ) by norm_num [mu])
  have hraw := hold N ((le_max_left _ _).trans hN) hEven omega hcut cap _ hz hcap
  rw [P5OriginalCommonPositivePresieve.normalize_sub] at hraw
  let S := orderedEighth r n e q a omega (N:ℝ)
  have hres := hbeta N ((le_max_right _ _).trans hN) hEven cap
    (by simpa only [hnr] using hcap) (S false)
  dsimp only at hres
  simp only [hnr] at hres
  change physical S N cap ((N:ℝ)^(nu*beta^2)) ((N:ℝ)^(19/96:ℝ)) ((N:ℝ)^(nu*beta)) ≤
    raw S N cap 0 ((N:ℝ)^(19/96:ℝ))+(eps/2)*singularSeries N/Real.log (N:ℝ) at hres
  have hnorm := P5OriginalCommonPositivePresieve.normalize_mono N h2 hres
  rw [P5OriginalCommonPositivePresieve.normalize_add,
    P5OriginalCommonPositivePresieve.normalize_reserve N h2] at hnorm
  refine ⟨Real.one_lt_rpow hNr (mul_pos hnu (sq_pos_of_pos hb)),?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hNr.le
    simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
  · dsimp only [S] at hnorm
    linarith only [hnorm,hraw]

theorem original_positive_source (nu eps betaMax : ℝ) (hnu : 0<nu)
    (heps : 0<eps) (hmax : 0<betaMax) :
    PositivePresieve (∑ c : Cell,cellIntegral c) nu eps betaMax :=
  positive_projection _ _ _ _ hnu heps hmax (original_ordinary_source (eps/2) (half_pos heps))

theorem original_positive_saved (nu eps betaMax : ℝ) (hnu : 0<nu)
    (heps : 0<eps) (hmax : 0<betaMax) :
    PositivePresieve (savedGain:ℝ) nu eps betaMax :=
  positive_projection _ _ _ _ hnu heps hmax (original_ordinary_saved (eps/2) (half_pos heps))

end
end ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
