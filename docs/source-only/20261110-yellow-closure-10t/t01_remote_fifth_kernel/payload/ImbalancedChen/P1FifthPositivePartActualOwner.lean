import ImbalancedChen.P1FifthUnitBoxLiteralGainLower

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The archived Jensen floor concerns a nonnegative positive-part gain. The
previous literalRawKernel is signed and can be negative when the saved MI
loses to old15. This file supplies the exact pointwise and integral bridge
from its positive part to the actual fifth gain on the SAME original owner.
It does not prove a numerical Jensen floor for that positive part, nor the
loss from restricting a full archived child to the original owner.
-/

namespace ImbalancedChen.P1FifthPositivePartActualOwner

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthGrid400UnitBoxPartition P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower
open P1OriginalVariableFifthContinuation P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1ActualVariableFifthProfiles
open P1ActualVariableFifthUntruncatedDomination

abbrev Point := Fin 5 → ℝ

def literalPositiveRawKernel (e : ℝ) (raw : FifthWireRow) (t : Point) : ℝ :=
  max 0 (literalRawKernel e raw t)

theorem literalPositiveRawKernel_nonneg (e : ℝ) (raw : FifthWireRow) (t : Point) :
    0 ≤ literalPositiveRawKernel e raw t :=
  le_max_left _ _

theorem continuousOn_literalPositiveRawKernel (e a b : ℝ) (ha : 0 < a)
    (raw : FifthWireRow) :
    ContinuousOn (literalPositiveRawKernel e raw)
      (P1LiteralVariableFifthCompactSupplier.positiveCube a b) := by
  exact continuousOn_const.max (continuousOn_literalRawKernel e a b ha raw)

theorem integrableOn_literalPositiveRawKernel_rawOwner (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1)) :
    IntegrableOn (literalPositiveRawKernel (e : ℝ) raw)
      (rawOwnerDomain raw e chi m omega j) := by
  have hc := continuousOn_literalPositiveRawKernel (e : ℝ) (1 / 400) (19 / 96)
    (by norm_num) raw
  have hi := hc.integrableOn_compact
    (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))
  exact hi.mono_set (rawOwnerDomain_subset_positiveCube raw hgrid hpositive e chi m omega j)

theorem literalPositiveRawKernel_le_rawOwnerKernel
    (e : ℚ) (he : 0 ≤ (e : ℝ)) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (raw : FifthWireRow) (t : Point) (ht : t ∈ rawOwnerDomain raw e chi m omega j) :
    literalPositiveRawKernel (e : ℝ) raw t ≤
      rawOwnerKernel e chi m omega j rows4 licensed4 raw t := by
  have hnonneg : 0 ≤ rawOwnerKernel e chi m omega j rows4 licensed4 raw t := by
    exact rawGainKernel_nonneg (e : ℝ)
      (originalVariableFourthProfile e chi omega m j rows4 licensed4) raw t ht.2.1
  exact max_le hnonneg
    (literalRawKernel_le_rawOwnerKernel e he chi m omega rows4 licensed4
      hgeometry J5 j hj raw t ht)

def literalPositiveRawOwnerIntegral (raw : FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1)) : ℝ :=
  ∫ t in rawOwnerDomain raw e chi m omega j,
    literalPositiveRawKernel (e : ℝ) raw t

theorem literalPositiveRawOwnerIntegral_le_actual
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) (hkey : KeyInjective records)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (RefinedCell q))
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true)
    (raw : FifthWireRow) (hr : raw ∈ records) (j : RefinedCell q)
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells
      e chi (refinedMesh q) omega J5) :
    literalPositiveRawOwnerIntegral raw e chi (refinedMesh q) omega j ≤
      rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hli := integrableOn_literalPositiveRawKernel_rawOwner raw (hgrid raw hr)
    (hpositive raw hr) e chi (refinedMesh q) omega j
  have hai := (integrableOn_actualKernel_fullCell e he chi (refinedMesh q) omega
    homega homegaRho J5 j hj rows4 licensed4 (decodedFamily records q)).mono_set
      (s := rawOwnerDomain raw e chi (refinedMesh q) omega j) inter_subset_right
  have hri : IntegrableOn (rawOwnerKernel e chi (refinedMesh q) omega j
      rows4 licensed4 raw)
      (rawOwnerDomain raw e chi (refinedMesh q) omega j) := by
    apply hai.congr_fun _ (rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
    intro t ht
    exact actualKernel_eq_rawOwnerKernel records q hq hgrid hmask hkey e chi omega
      rows4 licensed4 hgate j raw hr t ht
  exact setIntegral_mono_on hli hri
    (rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
    (fun t ht => literalPositiveRawKernel_le_rawOwnerKernel e
      (by exact_mod_cast he) chi (refinedMesh q) omega rows4 licensed4
      hgeometry J5 j hj raw t ht)

end
end ImbalancedChen.P1FifthPositivePartActualOwner
