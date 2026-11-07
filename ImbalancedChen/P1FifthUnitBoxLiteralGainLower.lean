import ImbalancedChen.P1FifthUnitBoxGainDecomposition
import ImbalancedChen.P1OriginalOld15Majorant

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A literal raw MI-minus-old15 kernel is a conservative LOWER bound for the
actual original variable-fourth/fifth gain, not an identity of old policies.
The real old4<=old15 theorem supplies the parent comparison from actual
selected Gamma/history and licensed fourth-row Geometry.

Positive integer lower keys put each complete saved unit box, after ambient
clipping, inside one fixed closed positive cube. Both genuine moving
own-cube profiles are continuous there; this proves real integrability,
including the apparent own-cube gate boundaries. The finite family sum
then lies below the same actual whole selected fifth integral.

The key, positive-endpoint and decoded-gate passing flags are NOT executed
on the historical payload. Saved A/B/gapSum fields never supply a gain.
-/
namespace ImbalancedChen.P1FifthUnitBoxLiteralGainLower

open P1OriginalPrefixRowDecodeSoundness

/-- A finite integer endpoint condition, independent of masks/statistics. -/
def positiveUnitKeyCheck (raw : Array FifthWireRow) : Bool :=
  raw.toList.all (fun row => decide (∀ i : Fin 5, 1 ≤ row.lo i))

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthRawBoxSelectorEquivalence
open P1FifthGrid400UnitBoxPartition P1FifthUnitBoxGainDecomposition
open P1OriginalVariableFifthContinuation P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1ActualVariableFifthProfiles
open P1ActualVariableFifthUntruncatedDomination

abbrev Point := Fin 5 → ℝ

theorem positiveUnitKeyCheck_sound (raw : Array FifthWireRow)
    (hc : positiveUnitKeyCheck raw = true) :
    ∀ row ∈ raw.toList, ∀ i : Fin 5, 1 ≤ row.lo i := by
  simpa only [positiveUnitKeyCheck, List.all_eq_true, decide_eq_true_eq] using hc

/-- The source variable MI remains pointwise. No stored constant cap is decoded. -/
def literalRawKernel (e : ℝ) (raw : FifthWireRow) (t : Point) : ℝ :=
  (primeOwnCubeGatedProfile (rawCandidate e raw t) t -
    primeOwnCubeGatedProfile (P1LiteralVariableFifthCompactSupplier.old5 e t) t) *
      ∏ i, 1 / t i

theorem continuous_rawCandidate (e : ℝ) (raw : FifthWireRow) :
    Continuous (rawCandidate e raw) := by
  have hsum : Continuous (fun t : Point => ∑ i ∈ maskSlots 5 raw.mask.toNat, t i) := by fun_prop
  exact (VariableEnvelope.continuous_v.comp hsum).sub continuous_const

theorem continuousOn_literalRawKernel (e a b : ℝ) (ha : 0 < a) (raw : FifthWireRow) :
    ContinuousOn (literalRawKernel e raw)
      (P1LiteralVariableFifthCompactSupplier.positiveCube a b) := by
  have hprod : ContinuousOn (fun t : Point => ∏ i, 1 / t i)
      (P1LiteralVariableFifthCompactSupplier.positiveCube a b) := by
    apply continuousOn_finsetProd Finset.univ
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun t ht => (ha.trans_le (ht i (mem_univ _)).1).ne')
  exact ((P1LiteralVariableFifthCompactSupplier.continuousOn_movingOwnCubeProfile
    a b ha _ (continuous_rawCandidate e raw)).sub
    (P1LiteralVariableFifthCompactSupplier.continuousOn_movingOwnCubeProfile
      a b ha _ (P1LiteralVariableFifthCompactSupplier.continuous_old5 e))).mul hprod

theorem rawOwnerDomain_subset_positiveCube (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hpositive : ∀ i, 1 ≤ raw.lo i) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (j : Fin 5 → Fin (m + 1)) :
    rawOwnerDomain raw e chi m omega j ⊆
      P1LiteralVariableFifthCompactSupplier.positiveCube (1 / 400) (19 / 96) := by
  intro t ht i _hi
  have hlo : (raw.lo i : ℝ) / 400 ≤ t i := by
    simpa [FifthWireRow.lower, hgrid] using (ht.1 i).1
  have hkey : (1 : ℝ) ≤ (raw.lo i : ℝ) := by exact_mod_cast hpositive i
  have hupper := (mem_logPrimeBox.mp ht.2.2.1 i).2
  constructor
  · linarith
  · exact hupper.le

/-- Genuine compact integrability of each literal raw-row kernel; the
historical endpoint positivity is explicit, and no integral is assumed. -/
theorem integrableOn_literalRawKernel_rawOwner (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hpositive : ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1)) :
    IntegrableOn (literalRawKernel (e : ℝ) raw) (rawOwnerDomain raw e chi m omega j) := by
  have hc := continuousOn_literalRawKernel (e : ℝ) (1 / 400) (19 / 96)
    (by norm_num) raw
  have hi := hc.integrableOn_compact
    (isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc))
  exact hi.mono_set (rawOwnerDomain_subset_positiveCube raw hgrid hpositive e chi m omega j)

/-- The actual licensed old4 is bounded above by old15. The new local
retained level is max(actual old4,MI), so MI is below it even if this row
loses. Both canonical gated profiles use their own strict cube tests. -/
theorem literalRawKernel_le_rawOwnerKernel
    (e : ℚ) (he : 0 ≤ (e : ℝ)) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (Fin 5 → Fin (m + 1))) (j : Fin 5 → Fin (m + 1))
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5)
    (raw : FifthWireRow) (t : Point) (ht : t ∈ rawOwnerDomain raw e chi m omega j) :
    literalRawKernel (e : ℝ) raw t ≤ rawOwnerKernel e chi m omega j rows4 licensed4 raw t := by
  have hold := P1OriginalOld15Majorant.actualOriginalFourth_le_old15 e he chi m omega
    rows4 licensed4 hgeometry J5 j hj t ht.2.2.2.1 ht.2.2.2.2
  have hnew : rawCandidate (e : ℝ) raw t ≤
      max (originalVariableFourthProfile e chi omega m j rows4 licensed4 t)
        (rawCandidate (e : ℝ) raw t) := le_max_right _ _
  have hp : ∀ i, 0 < t i := ht.2.1
  apply mul_le_mul_of_nonneg_right
  · exact sub_le_sub
      (p1PrimeOwnCubeGatedProfile_mono t (hp (Fin.last 4)) hnew)
      (p1PrimeOwnCubeGatedProfile_mono t (hp (Fin.last 4)) hold)
  · exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hp i).le)

def literalRawOwnerIntegral (raw : FifthWireRow) (e : ℚ) (chi : ℝ)
    (m : ℕ) (omega : ℝ) (j : Fin 5 → Fin (m + 1)) : ℝ :=
  ∫ t in rawOwnerDomain raw e chi m omega j, literalRawKernel (e : ℝ) raw t

/-- A real integral lower bound; both sides are proved integrable on the
same actual raw box and original owner/history carrier. -/
theorem literalRawOwnerIntegral_le_actual
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
    (hj : j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5) :
    literalRawOwnerIntegral raw e chi (refinedMesh q) omega j ≤
      rawOwnerIntegral raw e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hli := integrableOn_literalRawKernel_rawOwner raw (hgrid raw hr)
    (hpositive raw hr) e chi (refinedMesh q) omega j
  have hai := (integrableOn_actualKernel_fullCell e he chi (refinedMesh q) omega
    homega homegaRho J5 j hj rows4 licensed4 (decodedFamily records q)).mono_set
      (s := rawOwnerDomain raw e chi (refinedMesh q) omega j) inter_subset_right
  have hri : IntegrableOn (rawOwnerKernel e chi (refinedMesh q) omega j rows4 licensed4 raw)
      (rawOwnerDomain raw e chi (refinedMesh q) omega j) := by
    apply hai.congr_fun _ (rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
    intro t ht
    exact actualKernel_eq_rawOwnerKernel records q hq hgrid hmask hkey e chi omega
      rows4 licensed4 hgate j raw hr t ht
  exact setIntegral_mono_on hli hri (rawOwnerDomain_measurable raw e chi (refinedMesh q) omega j)
    (fun t ht => literalRawKernel_le_rawOwnerKernel e (by exact_mod_cast he)
      chi (refinedMesh q) omega rows4 licensed4 hgeometry J5 j hj raw t ht)

/-- The whole raw-row lower sum is sound only with genuine key separation,
endpoint positivity and original gate/owner/Geometry licences. No numerical
value or full-table passing witness is supplied by this theorem. -/
theorem sum_literalRawOwnerIntegrals_le_fullSelectedIntegral
    (records : Finset FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) (hkey : KeyInjective records)
    (hpositive : ∀ raw ∈ records, ∀ i, 1 ≤ raw.lo i)
    (e : ℚ) (he : 0 ≤ e) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry)
    (J5 : Finset (RefinedCell q))
    (hgate : ∀ r ∈ decodedFamily records q, gateCheck e (refinedMesh q) r = true) :
    (∑ raw ∈ records, ∑ j ∈
      P1OriginalCoarseFifthContinuation.selectedFifthCells e chi (refinedMesh q) omega J5,
      literalRawOwnerIntegral raw e chi (refinedMesh q) omega j) ≤
      fullSelectedIntegral e chi (refinedMesh q) omega rows4 licensed4 J5 (decodedFamily records q) := by
  rw [fullSelectedIntegral_eq_sum_raw_owner_integrals records q hq hgrid hmask hkey
    e chi omega rows4 licensed4 hgate he homega homegaRho J5]
  apply Finset.sum_le_sum
  intro raw hr
  apply Finset.sum_le_sum
  intro j hj
  exact literalRawOwnerIntegral_le_actual records q hq hgrid hmask hkey hpositive
    e he chi omega homega homegaRho rows4 licensed4 hgeometry J5 hgate raw hr j hj

end
end ImbalancedChen.P1FifthUnitBoxLiteralGainLower
