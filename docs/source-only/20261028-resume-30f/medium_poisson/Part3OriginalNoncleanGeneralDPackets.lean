import ImbalancedChen.Part3OriginalSourcePhysicalAbelCaller
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
The entire actual nonclean complement is partitioned by its genuine
tail gcd D=gcd(d*w1,d*w2). Every packet retains the original full CRT
residue, complete lcm and nonzero Fourier mode. D is not set equal to
the preliminary smooth d; neither canonical inverse transport nor a
spectral estimate on these packets is asserted.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalTrimmedCleanE3Assembly20261028
open ImbalancedChen.Part3.OriginalPoissonSourceCorrections20261028
open ImbalancedChen.Part3.OriginalSourcePhysicalAbelCaller20261028

namespace ImbalancedChen.Part3.OriginalNoncleanGeneralDPackets20261028

attribute [local instance] Classical.propDecidable

def actualTailGcd (B : FixedBlock) (r : Raw) : ℕ :=
  Nat.gcd (B.d * (pack r).w1) (B.d * (pack r).w2)

def noncleanDCarrier (B : FixedBlock) : Finset ℕ :=
  (noncleanBox B).image (actualTailGcd B)

/-- The payload here is still coefficientPhysicalTerm: its complete
lcm and constructed CRT root have not been replaced by clean formulas. -/
def noncleanGeneralDPacket (B : FixedBlock) (D : ℕ) : ℂ :=
  ∑ r ∈ (noncleanBox B).filter (fun r => actualTailGcd B r = D),
    coefficientPhysicalTerm B (pack r)

theorem preliminary_d_dvd_actualTailGcd (B : FixedBlock) (r : Raw) :
    B.d ∣ actualTailGcd B r := by
  exact Nat.dvd_gcd (dvd_mul_right B.d (pack r).w1)
    (dvd_mul_right B.d (pack r).w2)

theorem noncleanGeneralDPacket_disjoint (B : FixedBlock) {D E : ℕ} (hDE : D ≠ E) :
    Disjoint ((noncleanBox B).filter (fun r => actualTailGcd B r = D))
      ((noncleanBox B).filter (fun r => actualTailGcd B r = E)) := by
  apply Finset.disjoint_left.mpr
  intro r hr hs
  exact hDE ((Finset.mem_filter.mp hr).2.symm.trans (Finset.mem_filter.mp hs).2)

/-- Exhaustive finite general-D partition of the actual complement. -/
theorem coefficientNoncleanSum_eq_generalD (B : FixedBlock) :
    coefficientNoncleanSum B =
      ∑ D ∈ noncleanDCarrier B, noncleanGeneralDPacket B D := by
  unfold coefficientNoncleanSum noncleanGeneralDPacket
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single (actualTailGcd B r)]
  · simp
  · intro D hD hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    exact False.elim (hnot (Finset.mem_image.mpr ⟨r, hr, rfl⟩))

def actualFamilyGeneralD {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) : ℂ :=
  ∑ i : SourceBlockIndex atom z y,
    (∑ D ∈ noncleanDCarrier (genuineBlock atom z y hA Csep i),
      noncleanGeneralDPacket (genuineBlock atom z y hA Csep i) D) / (atom.V : ℂ)

theorem genuineNoncleanE2_eq_actualFamilyGeneralD {b : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (z y : ℝ) (hA : MediumAdmissible b σ κ c0 atom)
    (Csep : ℕ) :
    genuineNoncleanE2 atom z y hA Csep = actualFamilyGeneralD atom z y hA Csep := by
  unfold genuineNoncleanE2 actualFamilyGeneralD
  simp_rw [coefficientNoncleanSum_eq_generalD]

/-- Exact whole original source: genuine physical clean Abel caller,
all actual general-D/root packets and all correction terms. -/
theorem literalS3Normalized_eq_Abel_generalD_corrections
    {b : ℕ} {σ κ c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible b σ κ c0 atom) (z y : ℝ) (Csep : ℕ) :
    literalS3Normalized atom z y = actualFamilyAbel atom z y hA Csep +
      actualFamilyGeneralD atom z y hA Csep + sourceCorrectionsNormalized atom z y := by
  rw [literalS3Normalized_eq_actual_Abel_nonclean_corrections hA z y Csep,
    genuineNoncleanE2_eq_actualFamilyGeneralD]

end ImbalancedChen.Part3.OriginalNoncleanGeneralDPackets20261028
