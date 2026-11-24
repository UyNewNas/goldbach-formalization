import ImbalancedChen.P5OriginalTaylorProfileDerivatives
import ImbalancedChen.P5OriginalFourthFifthSourceInputs
import ImbalancedChen.P1HistoricalFifthFullOriginalFloorEnvelope

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The old Taylor kernel is the SIGNED difference of the original raw mask
and raw fifteen-mask-plus-W envelope, including the full reciprocal-prime
weight.  It is identified with the literal strict-own-cube kernel on the
original Taylor argument range.  Its comparison with the actual fourth
ancestor uses the existing one-sided majorant and original fourth rows.
No structural equality with the dynamic ancestor is assumed, and no
positive part replaces this signed Taylor kernel.

This does not assert that any stored oldQ80 is a Taylor lower bound.
-/
namespace ImbalancedChen.P5OriginalTaylorActualSignedKernel
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P1FifthUnitBoxLiteralGainLower P1FifthUnitBoxGainDecomposition
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1HistoricalFifthIndexedOwnerArchive
open P5OldFifthPointwiseQ P5OriginalTaylorLogBounds
open P5OriginalFourthFifthSourceInputs

abbrev Point := Fin 5 → ℝ

def originalTaylorWeight (t : Point) : ℝ := (4 / t 4) * ∏ k : Fin 5, 1 / t k

def originalTaylorNewArgument (raw : FifthWireRow) (t : Point) : ℝ :=
  residual (rawCandidate 0 raw t) t

def originalTaylorOldArgument (t : Point) : ℝ := residual (rawFourth t) t

def originalTaylorSignedKernel (raw : FifthWireRow) (t : Point) : ℝ :=
  originalTaylorWeight t *
    (firstF (originalTaylorNewArgument raw t) - firstF (originalTaylorOldArgument t))

def originalTaylorMidpointLower (raw : FifthWireRow) (t : Point) : ℝ :=
  midpointLower (originalTaylorWeight t)
    (originalTaylorNewArgument raw t) (originalTaylorOldArgument t)

theorem originalTaylorWeight_nonneg (t : Point) (ht : ∀ k, 0 < t k) :
    0 ≤ originalTaylorWeight t :=
  mul_nonneg (div_nonneg (by norm_num) (ht 4).le)
    (Finset.prod_nonneg (fun k _ => one_div_nonneg.mpr (ht k).le))

/-- The reciprocal-prime factor belongs inside the signed integrand. -/
theorem originalTaylorWeight_eq_source (t : Point) :
    originalTaylorWeight t = 4 / ((∏ k : Fin 5, t k) * t 4) := by
  simp [originalTaylorWeight, Fin.prod_univ_succ, div_eq_mul_inv, mul_inv_rev]
  <;> ring

/-- The strict gate at argument exactly 2 is included.  Both terms use
their own argument; the old term is not assigned the new cube test. -/
theorem originalTaylorSignedKernel_eq_literal (raw : FifthWireRow) (t : Point)
    (ht : 0 < t 4)
    (hn : originalTaylorNewArgument raw t ∈ Icc (2 : ℝ) 4)
    (ho : originalTaylorOldArgument t ∈ Icc (2 : ℝ) 4) :
    originalTaylorSignedKernel raw t = literalRawKernel 0 raw t := by
  have hnmax : max 2 (residual (rawCandidate 0 raw t) t) =
      originalTaylorNewArgument raw t := max_eq_right hn.1
  have homax : max 2 (residual (rawFourth t) t) =
      originalTaylorOldArgument t := max_eq_right ho.1
  have hnp := gatedProfile_eq_first (rawCandidate 0 raw t) t ht
    (by rw [hnmax]; exact hn.2)
  have hop := gatedProfile_eq_first (rawFourth t) t ht
    (by rw [homax]; exact ho.2)
  have hold : old5 0 t = rawFourth t := by simp [old5]
  unfold literalRawKernel
  rw [hold, hnp, hop, hnmax, homax]
  unfold originalTaylorSignedKernel originalTaylorWeight
  ring

theorem originalTaylorMidpointLower_le_signed (raw : FifthWireRow) (t : Point)
    (ht : ∀ k, 0 < t k)
    (hn : 2 ≤ originalTaylorNewArgument raw t)
    (ho : 2 ≤ originalTaylorOldArgument t) :
    originalTaylorMidpointLower raw t ≤ originalTaylorSignedKernel raw t :=
  original_midpoint_lower _ _ _ (originalTaylorWeight_nonneg t ht) hn ho

/-- Pointwise connection to the TRUE ancestor for every source index and
its actual licensed owner.  The remaining [2,4] hypotheses are geometric
Taylor branch tests, not an old-branch integral licence. -/
theorem originalTaylorSignedKernel_le_actual_owner
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (j : P1OriginalVariableFifthContinuation.Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i 0 q chi omega)
    (t : Point) (ht : t ∈ rawOwnerDomain (archiveRow i) 0 chi (refinedMesh q) omega j)
    (hn : originalTaylorNewArgument (archiveRow i) t ∈ Icc (2 : ℝ) 4)
    (ho : originalTaylorOldArgument t ∈ Icc (2 : ℝ) 4) :
    originalTaylorSignedKernel (archiveRow i) t ≤
      rawOwnerKernel 0 chi (refinedMesh q) omega j originalRows4 originalAdmission4
        (archiveRow i) t := by
  have hp : ∀ k, 0 < t k := ht.2.1
  rw [originalTaylorSignedKernel_eq_literal _ _ (hp 4) hn ho]
  exact literalRawKernel_le_rawOwnerKernel 0 (by norm_num) chi (refinedMesh q) omega
    originalRows4 originalAdmission4 (fun r _hr hlic => originalAdmission4_geometry r hlic)
    (licensedOwners i 0 q chi omega) j
    (licensedOwner_selected_buffer i 0 q chi omega j hj)
    (archiveRow i) t ht

/-- The original signed midpoint minorant at that actual source point.
This supplies neither a whole-box integral nor a stored-floor bound. -/
theorem originalTaylorMidpointLower_le_actual_owner
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (j : P1OriginalVariableFifthContinuation.Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i 0 q chi omega)
    (t : Point) (ht : t ∈ rawOwnerDomain (archiveRow i) 0 chi (refinedMesh q) omega j)
    (hn : originalTaylorNewArgument (archiveRow i) t ∈ Icc (2 : ℝ) 4)
    (ho : originalTaylorOldArgument t ∈ Icc (2 : ℝ) 4) :
    originalTaylorMidpointLower (archiveRow i) t ≤
      rawOwnerKernel 0 chi (refinedMesh q) omega j originalRows4 originalAdmission4
        (archiveRow i) t :=
  (originalTaylorMidpointLower_le_signed _ _ ht.2.1 hn.1 ho.1).trans
    (originalTaylorSignedKernel_le_actual_owner i q chi omega j hj t ht hn ho)

/-- The actual signed Taylor integrand is integrable on its original owner
piece, by equality to the already integrable literal kernel.  This supplies
the integral connection without an integrability or ancestor-equality input.
The original Taylor range tests must still be instantiated on a source box. -/
theorem originalTaylorIntegral_le_actual_owner
    (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (j : P1OriginalVariableFifthContinuation.Label5 (refinedMesh q))
    (hj : j ∈ licensedOwners i 0 q chi omega)
    (hrange : ∀ t ∈ rawOwnerDomain (archiveRow i) 0 chi (refinedMesh q) omega j,
      originalTaylorNewArgument (archiveRow i) t ∈ Icc (2 : ℝ) 4 ∧
      originalTaylorOldArgument t ∈ Icc (2 : ℝ) 4) :
    (∫ t in rawOwnerDomain (archiveRow i) 0 chi (refinedMesh q) omega j,
      originalTaylorSignedKernel (archiveRow i) t) ≤
      rawOwnerIntegral (archiveRow i) 0 chi (refinedMesh q) omega j
        originalRows4 originalAdmission4 := by
  have hg := P1HistoricalFifthTypedBaseGeometry.archiveRow_baseGeometry i
  have hmeas := rawOwnerDomain_measurable (archiveRow i) 0 chi (refinedMesh q) omega j
  have hL := integrableOn_literalRawKernel_rawOwner (archiveRow i) hg.1 hg.2.2.1
    0 chi (refinedMesh q) omega j
  have hT : IntegrableOn (originalTaylorSignedKernel (archiveRow i))
      (rawOwnerDomain (archiveRow i) 0 chi (refinedMesh q) omega j) := by
    exact hL.congr_fun (fun t ht =>
      (originalTaylorSignedKernel_eq_literal _ _ (ht.2.1 4)
        (hrange t ht).1 (hrange t ht).2).symm) hmeas
  have hA := P5LicensedRawOwnerActualGain.integrableOn_licensed_rawOwner
    i 0 (by norm_num) q chi omega hw hwr j hj originalRows4 originalAdmission4
  apply setIntegral_mono_on hT hA hmeas
  intro t ht
  exact originalTaylorSignedKernel_le_actual_owner i q chi omega j hj t ht
    (hrange t ht).1 (hrange t ht).2

end
end ImbalancedChen.P5OriginalTaylorActualSignedKernel
