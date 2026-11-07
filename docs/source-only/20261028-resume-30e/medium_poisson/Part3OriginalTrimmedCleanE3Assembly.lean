import ImbalancedChen.Part3OriginalLambdaTrimPoissonFamily
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.

This version keeps B.lambdaD, hence the actual lambdaTrim of genuineBlock.
It does not use the previous actualBlock operation, which replaces that
coefficient by the untrimmed Lambda. The raw kernel is independently formed
from the full original physical lcm/CRT Poisson term; typed E3 is the
pre-existing coefficient/weight sum. A separate primitive-q mask agrees
with the actual preliminary source and is automatic on clean E3.
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
open ImbalancedChen.Part3.OriginalGevreyCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028

namespace ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028

/-- Actual coefficient and primitive-q source mask; nonclean full
moduli/residue/h stay unchanged. B.lambdaD is not overwritten. -/
def coefficientPhysicalTerm (B : FixedBlock) (t : Index) : ℂ :=
  if t.q.Coprime B.atom.residue.natAbs ∧
      ComplexCRT.Compatible (t.q * B.d * t.w1) (t.q * B.d * t.w2) t.n1 t.n2 then
    B.lambdaD t.w1 * star (B.lambdaD t.w2) *
      B.atom.alpha t.n1 * star (B.atom.alpha t.n2) *
      paperPsiComplex ((t.q : ℝ) / B.atom.Q1) *
      paperPsiNonzeroMode (B.atom.V / (fullPhysicalL B t : ℝ))
        ((fullPhysicalResidue B t : ℝ) / (fullPhysicalL B t : ℝ)) t.h
  else 0

def coefficientRawSum (B : FixedBlock) : ℂ :=
  ∑ r ∈ rawBox B, coefficientPhysicalTerm B (pack r)

def coefficientCleanSum (B : FixedBlock) : ℂ :=
  ∑ r ∈ cleanBox B, coefficientPhysicalTerm B (pack r)

def coefficientNoncleanSum (B : FixedBlock) : ℂ :=
  ∑ r ∈ noncleanBox B, coefficientPhysicalTerm B (pack r)

/-- Literal full sum equals clean plus full nonclean payload. -/
theorem coefficientRawSum_eq_clean_add_nonclean (B : FixedBlock) :
    coefficientRawSum B = coefficientCleanSum B + coefficientNoncleanSum B := by
  unfold coefficientRawSum coefficientCleanSum coefficientNoncleanSum cleanBox noncleanBox
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hc : pack r ∈ B.carrier <;> simp [hc]

/-- Pointwise clean assembly with the ACTUAL source lambdaTrim field. -/
theorem coefficient_clean_summand_eq_V_div_d_E3 (B : FixedBlock)
    {t : Index} (ht : t ∈ B.carrier) :
    coefficientPhysicalTerm B t =
      (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) *
        ((actualProfile B).coeff t * (actualProfile B).weight t) := by
  have hc : B.clean t := (Finset.mem_filter.mp ht).2
  have hprimitive : t.q.Coprime B.atom.residue.natAbs := hc.1
  have hcompat := E3_clean_CRT_compatible hc
  obtain ⟨hq, hw1, hw2, hh⟩ := cleanCarrier_data ht
  have hphase := actual_E3_CRT_phase_eq_typed B ht
  have hscalar := cleanPoisson_scalar_eq ht
  have harg : (B.atom.V / (fullPhysicalL B t : ℝ)) * (t.h : ℝ) =
      (t.h : ℝ) * B.atom.V / ((t.q * B.d * t.w1 * t.w2 : ℕ) : ℝ) := by
    rw [E3_clean_complete_lcm hc]
    push_cast
    ring
  unfold coefficientPhysicalTerm
  rw [if_pos ⟨hprimitive, hcompat⟩]
  unfold paperPsiNonzeroMode
  rw [if_neg hh, hphase, Complex.real_smul, hscalar, harg]
  change _ = (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) *
    (((B.lambdaD t.w1 * Complex.conj (B.lambdaD t.w2) *
      B.atom.alpha t.n1 * Complex.conj (B.atom.alpha t.n2) /
        ((t.q * t.w1 * t.w2 : ℕ) : ℂ)) * B.firstPhase t) *
      (paperPsiComplex ((t.q : ℝ) / B.atom.Q1) *
        (𝓕 paperPsiComplex) ((t.h : ℝ) * B.atom.V /
          ((t.q * B.d * t.w1 * t.w2 : ℕ) : ℝ)) *
        Complex.exp (((2 * Real.pi *
          ((B.atom.residue : ℝ) * (t.h : ℝ) /
            ((t.q * B.d * t.w1 * t.w2 * t.n1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)))
  simp only [div_eq_mul_inv, Complex.star_def]
  ring

/-- Exact clean source sum, with coefficient-preserving actualProfile. -/
theorem coefficientCleanSum_eq_V_div_d_E3 (B : FixedBlock) :
    coefficientCleanSum B =
      (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) * (actualProfile B).E3 := by
  unfold coefficientCleanSum FixedBlock.E3
  rw [actualProfile_carrier]
  rw [← cleanBox_image B,
    Finset.sum_image (fun r _ r' _ h => pack_injective h), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact coefficient_clean_summand_eq_V_div_d_E3 B (Finset.mem_filter.mp hr).2

/-- Source normalization includes all nonclean terms with the same V. -/
theorem coefficientRawSum_div_V (B : FixedBlock) :
    coefficientRawSum B / (B.atom.V : ℂ) =
      (actualProfile B).E3 / (B.d : ℂ) +
        coefficientNoncleanSum B / (B.atom.V : ℂ) := by
  rw [coefficientRawSum_eq_clean_add_nonclean, add_div,
    coefficientCleanSum_eq_V_div_d_E3]
  have hV : (B.atom.V : ℂ) ≠ 0 := by exact_mod_cast B.V_pos.ne'
  have hd : (B.d : ℂ) ≠ 0 := by exact_mod_cast B.d_pos.ne'
  push_cast
  field_simp [hV, hd]
  ring

/-- A genuinely constructed finite source family, with actual key,
active d, q chart and signed h windows. -/
def genuineRawE2 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℂ :=
  ∑ i : SourceBlockIndex atom z y,
    coefficientRawSum (genuineBlock atom z y hA Csep i) / (atom.V : ℂ)

def genuineTypedE3 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℂ :=
  ∑ i : SourceBlockIndex atom z y,
    (actualProfile (genuineBlock atom z y hA Csep i)).E3 / (i.2.1.val : ℂ)

def genuineNoncleanE2 {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℂ :=
  ∑ i : SourceBlockIndex atom z y,
    coefficientNoncleanSum (genuineBlock atom z y hA Csep i) / (atom.V : ℂ)

/-- Every nonclean general-D/root summand survives the global assembly.
The raw family is independently constructed; no final SourceBind equality
is a hypothesis or a definition of the typed E3 array. -/
theorem genuineRawE2_eq_typed_plus_nonclean {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) :
    genuineRawE2 atom z y hA Csep =
      genuineTypedE3 atom z y hA Csep + genuineNoncleanE2 atom z y hA Csep := by
  unfold genuineRawE2 genuineTypedE3 genuineNoncleanE2
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [genuineBlock_atom, genuineBlock_d] using
    coefficientRawSum_div_V (genuineBlock atom z y hA Csep i)

end ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
