import ImbalancedChen.Part3ActualCompletedSourceLanes
import ImbalancedChen.Part3PrimaryDyadicActualMode
import ImbalancedChen.Part3PrimaryDyadicCommonAssembly

/-!
# The actual medium source in one common Poisson dictionary

This module consumes the existing actual medium-atom carrier and the proved
primary/sign/dyadic source partition. The source coefficients are the original
finite products of lambda and omega. No coefficient acquires a future m,
primary-key-specific cutoff, or spectral-height argument.

The whole y=0 contribution keeps its complete m series. Every nonzero-y
primary block uses the same explicit J, the accepted positive/reflected m
blocks, and the complementary Poisson tail. The residue sign in signedResidue,
the y sign in a primary key, and the m sign in blockKernel remain independent.

MediumAtom has no positivity fields. Output licensing is consequently proved
under the explicit Q2 > 0 hypothesis, using membership in the genuine quotient
image. The identities themselves need no positive or nonempty source carrier.

This is an actual finite-source specialization of the 1106 manuscript's
coefficient-independent completion and common signed interval construction.
It does not identify this completedPiece with the missing OriginalData/six-piece
energy, choose the original family's global J, prove a spectral kernel identity,
instantiate external J/A, or estimate a zero term or tail.
-/

namespace ImbalancedChen.Part3.ActualModeCommonPoissonLanes20261126

noncomputable section
open Classical Finset
open scoped BigOperators
open ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open ActualSeparatedRowPacketMatchSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly
open ActualModeBetaPositiveCountSourceOnly
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

/-- The full actual carrier, before discarding the separate y=0 source.
Its nonzero filter is definitionally the already installed actualNonzeroSource. -/
def actualSource (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) : Finset Source :=
  carrier (g * l) (signedResidue residueNegative e.residue)
    (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
    (Icc (Int.ceil (-scaleF e D g)) (Int.floor (scaleF e D g)))

theorem nonzero_actualSource (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) :
    nonzeroSource (actualSource e D delta g l Z residueNegative) =
      actualNonzeroSource e D delta g l Z residueNegative := rfl

/-- Positivity follows from the actual divisible quotient image. This also
handles q=0: a purported member would contradict the positive original factor. -/
theorem baseCarrier_positive (e : MediumAtom) (q : ℕ) (hQ2 : 0 < e.Q2)
    {t : ℕ} (ht : t ∈ baseCarrier e q) : 0 < t := by
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  have hsFactor : s ∈ factorCarrier e.Q2 := (mem_filter.mp hs).1
  have hsDiv : q ∣ s := (mem_filter.mp hs).2
  have hsLower : Nat.ceil e.Q2 ≤ s := (mem_Icc.mp hsFactor).1
  have hsPos : 0 < s := (Nat.ceil_pos.mpr hQ2).trans_le hsLower
  have hprod : s / q * q = s := Nat.div_mul_cancel hsDiv
  apply Nat.pos_of_ne_zero
  intro hz
  rw [hz, zero_mul] at hprod
  exact hsPos.ne' hprod.symm

/-- The same actual source supplies a positive output level and the residue
unit gate. No independent arbitrary-beta support hypothesis is introduced. -/
theorem actualSource_output_licensed (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) (hQ2 : 0 < e.Q2) {s : Source}
    (hs : s ∈ actualSource e D delta g l Z residueNegative) :
    0 < (output s).1 ∧ e.residue.natAbs.Coprime (output s).1 := by
  constructor
  · exact output_positive_level
      (fun t ht => baseCarrier_positive e (D / delta) hQ2 ht) hs
  · have h : (signedResidue residueNegative e.residue).natAbs.Coprime (output s).1 :=
      output_residue_coprime hs
    simpa only [ActualM2FinitePoissonAdapterSourceOnly.signedResidue_natAbs] using h

/-- A nonzero grouped coefficient has a witness in the original full actual
carrier, with nonzero y, positive z, and the original residue-coprime gate. -/
theorem actual_nonzero_beta_witness (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) (hQ2 : 0 < e.Q2)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {zy : Output}
    (hb : beta (actualNonzeroSource e D delta g l Z residueNegative)
      lambda omega zy ≠ 0) :
    ∃ s ∈ actualSource e D delta g l Z residueNegative, output s = zy ∧
      zy.2 ≠ 0 ∧ 0 < zy.1 ∧ e.residue.natAbs.Coprime zy.1 := by
  obtain ⟨s, hs, hout⟩ := mem_image.mp (beta_ne_zero_mem_image hb)
  change s ∈ nonzeroSource (actualSource e D delta g l Z residueNegative) at hs
  have hbase : s ∈ actualSource e D delta g l Z residueNegative := (mem_filter.mp hs).1
  have hy : (output s).2 ≠ 0 := (mem_filter.mp hs).2
  have hz := actualSource_output_licensed e D delta g l Z residueNegative hQ2 hbase
  exact ⟨s, hbase, hout, hout ▸ hy, hout ▸ hz.1, hout ▸ hz.2⟩

/-- Primary keys are computed from the nonzero source; every block uses the
same cutoff J and the same fixed residue a in the physical kernel. -/
def primaryMLanes (a : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (J : ℕ) (M N C : ℝ) : ℂ :=
  ∑ key ∈ keys a S,
    sourceMLanes (block a S key) lambda omega J M N C a

/-- The existing exact primary partition followed by the actual joint-beta
pushforward and accepted kernel lanes. There is no interchange of infinite sums. -/
theorem nonzero_source_eq_primary_m_lanes (a : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) :
    (∑ s ∈ nonzeroSource S, weight lambda omega s * completedKernel M N C a (output s)) =
      primaryMLanes a S lambda omega J M N C := by
  unfold primaryMLanes
  rw [finite_source_assembly]
  apply sum_congr rfl
  intro key _hkey
  rw [weighted_pushforward]
  exact joint_beta_eq_common_m_lanes (block a S key) lambda omega hM J N C a

/-- The y=0 source keeps all m. Only its disjoint nonzero complement is
assembled by primary/sign/dyadic keys and then by the common m lanes. -/
theorem source_eq_zero_add_primary_m_lanes (a : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) :
    (∑ s ∈ S, weight lambda omega s * completedKernel M N C a (output s)) =
      (∑ zy ∈ (zeroSource S).image output,
        beta (zeroSource S) lambda omega zy * completedKernel M N C a zy) +
      primaryMLanes a S lambda omega J M N C := by
  rw [sum_zero_nonzero]
  exact congrArg₂ (· + ·)
    (weighted_pushforward (zeroSource S) lambda omega (completedKernel M N C a))
    (nonzero_source_eq_primary_m_lanes a S lambda omega hM J N C)

/-- The literal completed mode at the installed actual medium-atom carrier.
The complete zero-y term and every primary block have identical source data;
the same explicit J is used for every output level and both m signs. -/
theorem actual_completedPiece_eq_zero_add_primary_m_lanes
    (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N B C : ℝ) :
    let a := signedResidue residueNegative e.residue
    let S := actualSource e D delta g l Z residueNegative
    completedPiece (g * l) a (baseCarrier e (D / delta))
      (e.sharedSmoothFrequencyBound Z D) lambda omega M N B C (scaleF e D g) =
      (∑ zy ∈ (zeroSource S).image output,
        beta (zeroSource S) lambda omega zy * completedKernel M N C a zy) +
      primaryMLanes a S lambda omega J M N C := by
  dsimp only
  rw [completedPiece_eq_source]
  exact source_eq_zero_add_primary_m_lanes
    (signedResidue residueNegative e.residue)
    (actualSource e D delta g l Z residueNegative) lambda omega hM J N C

end

end ImbalancedChen.Part3.ActualModeCommonPoissonLanes20261126
