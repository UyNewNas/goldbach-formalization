import ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import ImbalancedChen.P2OriginalSixthElevenLogSemantics
import ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent structural constructor, frozen before peer range proofs.
The original historical parent and corrected above-mu second/third actions
are retained as a causal Boolean union. Fourth/fifth candidates are the
ORIGINAL row formulas with ORIGINAL eligibility/licence; their finite maxima
are re-seeded at the common actual third/fourth ancestor. Nothing identifies
the old parents by fiat. Eleven sixth source cells use their literal oldCap,
newCap and PhysicalCell, re-tested against this actual fifth ancestor.

The union and finite maxima are actual per-prefix rules. Their finite
source/trace identities and old-branch containment are supplied separately.
The numerical adopted common compact partition, completeness/nonemptiness
of licensed records and preservation of archived gains are NOT asserted.
No range theorem, PP estimate, K or final density inequality is imported.
-/

namespace ImbalancedChen.P5OriginalCommonRefinedConstructor

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

structure OriginalData where
  e : ℚ
  chi : ℝ
  m : ℕ
  omega : ℝ
  rows4 : Finset ProducerRow
  licensed4 : ProducerRow → Prop
  J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m)
  rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)

def old3 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  HistoricalThirdCoarse.policy (d.e : ℝ) d.chi d.m d.omega N

def fallback23 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  finalPolicy (d.e : ℝ) d.chi d.m d.omega N

/-- A causal union of actual prefix decisions; neither old policy is
silently replaced by the other. Both global even decisions are true. -/
def common3 (d : OriginalData) (N : ℝ) (positive : Bool) (pre : List ℕ) : Bool :=
  old3 d N positive pre || fallback23 d N positive pre

def originalSeed (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  seedExponent (d.e : ℝ) d.chi d.m d.omega N pre

/-- Literal level used by the corrected fallback after its third node. -/
def fallbackSeed (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if thirdGuard N pre then
    v (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1 +
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2)
  else if secondGuard N pre then
    v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)
  else originalSeed d N pre

/-- Frozen actual common third exponent; all later seeds use this value. -/
def lambda3 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  max (originalSeed d N pre) (fallbackSeed d N pre)

def exponent4 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if pre.length = 4 then
    finiteMax d.rows4
      (fun r => producerEligible d.licensed4 r (primeHistoryLogCoordinates N 4 pre))
      (fun r => r.bufferedCandidate (d.e : ℝ) (primeHistoryLogCoordinates N 4 pre))
      (lambda3 d N pre)
  else lambda3 d N pre

def level4 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := N ^ exponent4 d N pre

def policy4 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (common3 d N) (frozenParityRosserPolicy false 4 (level4 d N))

def exponent5 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  let inherited := exponent4 d N (rosserAncestor 4 pre)
  if pre.length = 5 then
    finiteMax d.rows5
      (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega
        d.J5 r (primeHistoryLogCoordinates N 5 pre))
      (fun r => P1OriginalVariableFifthContinuation.candidate (d.e : ℝ) r.selected
        (primeHistoryLogCoordinates N 5 pre)) inherited
  else inherited

def level5 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := N ^ exponent5 d N pre

/-- Fifth admission is changed after the same retained rank-four parent. -/
def policy5 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (common3 d N) (frozenParityRosserPolicy false 5 (level5 d N))

def actualParent5 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  exponent5 d N (rosserAncestor 5 pre)

abbrev SixthCell := Certificates.P2OriginalSixthElevenLogSemantics.Cell

def eligibleSixth (d : OriginalData) (N : ℝ) (c : SixthCell) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  pre.length = 6 ∧
    Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < actualParent5 d N pre ∧
    actualParent5 d N pre ≤ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t

/-- One explicitly selected finite supplier over the exact eleven original
source families. Each old comparison is re-tested on the real new parent. -/
def lambda6 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
    (fun c => eligibleSixth d N c pre)
    (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c
      (primeHistoryLogCoordinates N 6 pre)) (actualParent5 d N pre)

def level6 (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := N ^ lambda6 d N pre

def policy6 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (policy5 d N) (frozenParityRosserPolicy false 6 (level6 d N))

def policy8 (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  P5OriginalAdoptedEighthPhysicalMasks.familyPolicy N (lambda3 d N) (lambda6 d N) (policy5 d N)

def rho (d : OriginalData) (N enumerationCap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho ((policy8 d (N : ℝ)) false) N enumerationCap w z L

def moduli (d : OriginalData) (N enumerationCap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli ((policy8 d (N : ℝ)) false) N enumerationCap w z

theorem common3_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    common3 d N true pre = true := by
  simp [common3, old3, HistoricalThirdCoarse.policy_even]

theorem policy4_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy4 d N true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 4 _ _
    (common3_even d N) (fun q => frozenParityRosserPolicy_upper_even 4 _ q) pre

theorem policy5_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy5 d N true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 4 _ _
    (common3_even d N) (fun q => frozenParityRosserPolicy_upper_even 5 _ q) pre

theorem policy6_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy6 d N true pre = true := by
  exact UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (policy5_even d N) (fun q => frozenParityRosserPolicy_upper_even 6 _ q) pre

theorem policy8_even (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy8 d N true pre = true := by
  exact P5OriginalAdoptedEighthPhysicalMasks.family_even N (lambda3 d N) (lambda6 d N)
    (policy5 d N) (policy5_even d N) pre

theorem actualParent5_le_lambda6 (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    actualParent5 d N pre ≤ lambda6 d N pre := finiteMax_seed_le _ _ _ _

theorem eligibleSixth_newCap_le_lambda6 (d : OriginalData) (N : ℝ)
    (c : SixthCell) (pre : List ℕ) (hc : eligibleSixth d N c pre) :
    Certificates.P2OriginalSixthElevenLogSemantics.newCap c
      (primeHistoryLogCoordinates N 6 pre) ≤ lambda6 d N pre := by
  exact finiteMax_row_le _ _ _ _ c (List.mem_toFinset.mpr
    (Certificates.P2OriginalSixthElevenLogSemantics.allCells_complete c)) hc

theorem eligibleSixth_actualParent_lt_newCap (d : OriginalData) (N : ℝ)
    (c : SixthCell) (pre : List ℕ) (hc : eligibleSixth d N c pre) :
    actualParent5 d N pre < Certificates.P2OriginalSixthElevenLogSemantics.newCap c
      (primeHistoryLogCoordinates N 6 pre) := hc.2.2.2.trans_lt hc.2.1.positiveGap

theorem lambda6_eq_parent_of_no_eligible (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hn : ∀ c ∈ Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset,
      ¬eligibleSixth d N c pre) : lambda6 d N pre = actualParent5 d N pre :=
  finiteMax_eq_seed_of_outside _ _ _ _ hn

/-- A real rank-seven test reads THIS selected sixth cap on THIS ancestor. -/
theorem policy6_rank_seven (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 7) :
    policy6 d N false pre = decide (ordinaryRosserPrefixAdmissible false
      (N ^ lambda6 d N (rosserAncestor 6 pre)) pre) := by
  simp [policy6, firstExitDepthSplicePolicy, hlen, frozenParityRosserPolicy,
    ancestorFrozenPolicy, ordinaryParityRosserPolicy, oddFirstExitPolicy, level6]

end
end ImbalancedChen.P5OriginalCommonRefinedConstructor
