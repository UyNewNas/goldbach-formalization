import ImbalancedChen.P4AOriginalFull87SavedGain
import ImbalancedChen.P4AOriginalFull87UnionActualGain

/-! The archived slots 15–22 at the original physical sixth-to-eighth
splice. The enriched fifth bank is the old grid-400 bank together with
the two original new-fifth banks on the common refined mesh. -/
namespace ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
noncomputable section
open scoped BigOperators
open VariableEnvelope (mu)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourcePrimeTests (cellIntegral)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87Saved86 (savedGain)
open P4AOriginalFull87SavedGain (original_saved_gain_le_integral)
open P4AOriginalVariableFifthPhysicalLedger (raw physical)
open P5OriginalCommonPositivePresieve (normalize)

inductive FifthBank
  | original
  | enlarged

def sixth : FifthBank → ℕ → ℚ → ℕ → ℝ → ℝ → Bool → List ℕ → Bool
  | .original => P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
  | .enlarged => P4AOriginalFull87UnionHistory.sixthPolicy

def eighth : FifthBank → ℝ → ℕ → ℚ → ℕ → ℝ → ℝ → Bool → List ℕ → Bool
  | .original => P4AOriginalFull87LicensedSixthPolicy.policy
  | .enlarged => P4AOriginalFull87UnionHistory.policy

/-- The trim and resolution, rational strip, common mesh and its
displacement are chosen before the even arithmetic target. -/
def Scheduled (P : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop) : Prop :=
  ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
  ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
  ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N → P r n e q om N

private theorem scheduled_mono {P Q : ℕ → ℕ → ℚ → ℕ → ℝ → ℕ → Prop}
    (h : Scheduled P) (himp : ∀ r n e q om N, P r n e q om N → Q r n e q om N) :
    Scheduled Q := by
  obtain ⟨r0,hr⟩ := h
  refine ⟨r0,?_⟩
  intro r hr0
  obtain ⟨n0,hn⟩ := hr r hr0
  refine ⟨n0,?_⟩
  intro n hn0
  obtain ⟨e0,he0,he⟩ := hn n hn0
  refine ⟨e0,he0,?_⟩
  intro e hep hee
  obtain ⟨q0,hq0,hq⟩ := he e hep hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨N0,hN0,hN⟩ := hq q hqq om hom
  exact ⟨N0,hN0,fun N hNN hEven => himp r n e q om N (hN N hNN hEven)⟩

def Ordinary (b : FifthBank) (gain eps : ℝ) : Prop :=
  Scheduled (fun r n e q om N =>
    ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      gain - eps < normalize N (raw (sixth b n e q om (N : ℝ)) N cap 0 z -
        raw (eighth b (width r) n e q om (N : ℝ)) N cap 0 z))

def PositivePresieve (b : FifthBank) (gain nu eps betaMax : ℝ) : Prop :=
  ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧ beta^2 ≤ (19/96 : ℝ)/nu ∧
    Scheduled (fun r n e q om N =>
      ∀ cap : ℕ, (N : ℝ)^(19/96 : ℝ) ≤ cap →
        let w := (N : ℝ)^(nu * beta^2)
        let z := (N : ℝ)^(19/96 : ℝ)
        let L := (N : ℝ)^(nu * beta)
        1 < w ∧ w ≤ z ∧ normalize N (physical (eighth b (width r) n e q om (N : ℝ)) N cap w z L) <
          normalize N (raw (sixth b n e q om (N : ℝ)) N cap 0 z) - gain + eps)

private theorem ordinary_source (b : FifthBank) (eps : ℝ) (heps : 0 < eps) :
    Ordinary b (∑ c : Cell, cellIntegral c) eps := by
  cases b with
  | original => exact P4AOriginalFull87ActualGain.exists_ordinary_source_gain eps heps
  | enlarged => exact P4AOriginalFull87UnionActualGain.exists_ordinary_source_gain eps heps

private theorem positive_source (b : FifthBank) (nu eps betaMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) :
    PositivePresieve b (∑ c : Cell, cellIntegral c) nu eps betaMax := by
  cases b with
  | original => exact P4AOriginalFull87ActualGain.exists_positive_presieve_source_gain nu eps betaMax hnu heps hMax
  | enlarged => exact P4AOriginalFull87UnionActualGain.exists_positive_presieve_source_gain nu eps betaMax hnu heps hMax

/-- All eight original ledger slots on the same ordinary signed
physical histories of the chosen, fully evaluated policy. -/
theorem exists_ordinary_saved_gain (b : FifthBank) (eps : ℝ) (heps : 0 < eps) :
    Ordinary b (savedGain : ℝ) eps := by
  apply scheduled_mono (ordinary_source b eps heps)
  intro r n e q om N h cap z hz hcap
  exact (sub_le_sub_right original_saved_gain_le_integral eps).trans_lt (h cap z hz hcap)

/-- A single positive-presieve projection on the complete eighth tree,
with its own ordinary sixth parent and the same original eight slots. -/
theorem exists_positive_presieve_saved_gain (b : FifthBank) (nu eps betaMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) :
    PositivePresieve b (savedGain : ℝ) nu eps betaMax := by
  obtain ⟨beta,hb,hb8,hbM,hbn,h⟩ := positive_source b nu eps betaMax hnu heps hMax
  refine ⟨beta,hb,hb8,hbM,hbn,scheduled_mono h ?_⟩
  intro r n e q om N hr cap hcap
  obtain ⟨hw,hwz,hcost⟩ := hr cap hcap
  exact ⟨hw,hwz,hcost.trans_le (add_le_add_right (sub_le_sub_left original_saved_gain_le_integral _) _)⟩

/-- Density consumer on the concrete joined fifth bank. This is the
ordinary statement used when the compiler pays the later beta loss. -/
theorem union_ordinary_saved_gain (eps : ℝ) (heps : 0 < eps) :
    Scheduled (fun r n e q om N => ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      (savedGain : ℝ) - eps < normalize N
        (raw (P4AOriginalFull87UnionHistory.sixthPolicy n e q om (N : ℝ)) N cap 0 z -
         raw (P4AOriginalFull87UnionHistory.policy (width r) n e q om (N : ℝ)) N cap 0 z)) :=
  exists_ordinary_saved_gain .enlarged eps heps

theorem union_positive_presieve_saved_gain (nu eps betaMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) :
    PositivePresieve .enlarged (savedGain : ℝ) nu eps betaMax :=
  exists_positive_presieve_saved_gain .enlarged nu eps betaMax hnu heps hMax

end
end ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
