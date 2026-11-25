import ImbalancedChen.P4AOriginalFull87ScheduleDefinitions
import ImbalancedChen.P4AOriginalR17EighthSignedTransport
import ImbalancedChen.P4AOriginalFull87UnionActualGain

/-! Source-only relocation of the existing ordinary integral source.
All formulas and proof bodies are retained. The existing common-history
helper is public solely so the original saved endpoint can still call it. -/
namespace ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope (mu)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
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

/-- Refine only the existing common third mesh thresholds. The signed
coefficient equality then holds at every modulus of the later carrier. -/
theorem with_common_history (gain eps : ℝ)
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

end
end ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
