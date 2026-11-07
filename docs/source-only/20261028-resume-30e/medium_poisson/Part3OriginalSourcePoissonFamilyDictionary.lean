import ImbalancedChen.Part3OriginalTrimmedCleanE3Assembly
import ImbalancedChen.Part3MediumGenuinePoissonFibre
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.

The source fibre is the peer's independently defined literal common-d
restored S3 m-sum, with actual lambdaTrim and paperMWeight. The physical
block family was constructed independently from source keys/active d,
three q pieces and actual signed H. This file proves the pointwise
coefficient/physical-modulus/residue/h dictionary between them. It then
instantiates the literal source Poisson identity at the actual key H,
retaining the diagonal restriction, exact zero mode and omitted error.
The remaining whole finite carrier rearrangement is not an assumption.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGenuinePoissonFibre20261028

namespace ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028

/-- The literal source (q,d),(r,n1),(s,n2), unchanged by the block map. -/
def sourceFibre (q small r s n1 n2 : ℕ) : FibreIndex := ((q,small),((r,n1),(s,n2)))

def physicalIndex (q r s n1 n2 : ℕ) (h : ℤ) : Index :=
  { q := q, w1 := r, w2 := s, n1 := n1, n2 := n2, h := h }

/-- One actual signed frequency of the independent literal Poisson fibre. -/
def sourceMode (atom : MediumAtom) (z y : ℝ) (k : Key)
    (v : FibreIndex) (h : ℤ) : ℂ :=
  headCoefficient atom (strictReceiverCutoff z) y k v *
    (if compatible v then
      paperPsiNonzeroMode (atom.V / (completeL v : ℝ))
        ((constructedResidue atom v : ℝ) / (completeL v : ℝ)) h else 0)

/-- Raw source frequency equals the actual lambdaTrim family term.
The source primitive-q licence is arithmetic data from fibreCarrier;
no SourceBind or E2 identity is a hypothesis. -/
theorem sourceMode_eq_actual_family_term {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hA : MediumAdmissible b σ κ c0 atom) (Csep : ℕ)
    (j : Fin 3) (small : ℕ) (hd : small ∈ activeD atom k) (negative : Bool)
    (q r s n1 n2 : ℕ) (h : ℤ) (hq : q.Coprime atom.residue.natAbs) :
    sourceMode atom z y k (sourceFibre q small r s n1 n2) h =
      coefficientPhysicalTerm (poissonAtlasBlock atom z y k hA Csep j small hd negative)
        (physicalIndex q r s n1 n2 h) := by
  have hpsi : (paperQWeight atom q : ℂ) = paperPsiComplex ((q : ℝ) / atom.Q1) := rfl
  unfold sourceMode coefficientPhysicalTerm headCoefficient completeL
    constructedResidue leftModulus rightModulus compatible fullPhysicalL fullPhysicalResidue
  simp only [sourceFibre, physicalIndex, poissonAtlasBlock_atom,
    poissonAtlasBlock_d, poissonAtlasBlock_lambda, hq, true_and, hpsi]
  by_cases hc : ComplexCRT.Compatible ((q * small) * r) ((q * small) * s) n1 n2
  · simp only [if_pos hc]
    ring
  · simp only [if_neg hc, mul_zero]

/-- The peer's literal finite-H packet is exactly the sum of its actual
frequency payloads; both signed directions and h=0=0 are unchanged. -/
theorem head_retained_eq_source_modes (atom : MediumAtom) (z y : ℝ)
    (k : Key) (H : ℕ) (v : FibreIndex) :
    headCoefficient atom (strictReceiverCutoff z) y k v * retainedModes atom H v =
      ∑ h ∈ signedWindow H, sourceMode atom z y k v h := by
  unfold sourceMode retainedModes
  by_cases hc : compatible v
  · simp only [if_pos hc]
    rw [Finset.mul_sum]
  · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]

/-- Select the actual key's real H using floor(H). For nonzero integer
frequencies, h.natAbs<=floor(H) is the exact real h.natAbs<=H test. -/
def sourceKeyH (atom : MediumAtom) (k : Key) : ℕ := Nat.floor (keyRealH atom k)

/-- Actual primitive off-diagonal restored S3 source, before any claim
that its raw carrier equals the complete block sum. Zero, retained and
omitted terms stay in one exact equation on the independent source. -/
theorem literal_offDiagonal_source_at_actual_keyH
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (∑ t ∈ offDiagonalCarrier atom k,
      S3FullTerm atom (strictReceiverCutoff z) y k t) =
      ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
        headCoefficient atom (strictReceiverCutoff z) y k v *
          (zeroMode atom v + retainedModes atom (sourceKeyH atom k) v +
            omittedModes atom (sourceKeyH atom k) v)
        else 0 :=
  offDiagonal_Poisson_source_identity hA (strictReceiverCutoff z) y k
    (fun _ => sourceKeyH atom k)

/-- Actual source h-window selected from the key; no omitted series is
silently absorbed into a new finite coefficient or spectral estimate. -/
theorem literal_offDiagonal_retained_modes_dictionary
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (k : Key) :
    (∑ t ∈ offDiagonalCarrier atom k,
      S3FullTerm atom (strictReceiverCutoff z) y k t) =
      ∑ v ∈ fibreCarrier atom k, if v.2.1.2 ≠ v.2.2.2 then
        headCoefficient atom (strictReceiverCutoff z) y k v * zeroMode atom v +
          (∑ h ∈ signedWindow (sourceKeyH atom k), sourceMode atom z y k v h) +
          headCoefficient atom (strictReceiverCutoff z) y k v *
            omittedModes atom (sourceKeyH atom k) v
        else 0 := by
  rw [literal_offDiagonal_source_at_actual_keyH hA z y k]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h12 : v.2.1.2 ≠ v.2.2.2
  · simp only [if_pos h12, mul_add]
    rw [head_retained_eq_source_modes]
  · simp only [if_neg h12]

end ImbalancedChen.Part3.OriginalSourcePoissonFamilyDictionary20261028
