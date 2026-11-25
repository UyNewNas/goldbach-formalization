import ImbalancedChen.P4AOriginalR17OrdinarySource
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

def PositivePresieve (gain nu eps betaMax : ℝ) : Prop :=
  ∃ beta : ℝ, 0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2≤(19/96:ℝ)/nu ∧
    Scheduled (fun r n e q a N => ∀ omega : ℝ, omega≤a →
      ∀ cap : ℕ, (N:ℝ)^(19/96:ℝ)≤cap →
      let w := (N:ℝ)^(nu*beta^2)
      let z := (N:ℝ)^(19/96:ℝ)
      let L := (N:ℝ)^(nu*beta)
      1<w ∧ w≤z ∧ normalize N (physical (orderedEighth r n e q a omega N) N cap w z L) <
        normalize N (raw (orderedSixth n e q a omega N) N cap 0 z)-gain+eps)

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
