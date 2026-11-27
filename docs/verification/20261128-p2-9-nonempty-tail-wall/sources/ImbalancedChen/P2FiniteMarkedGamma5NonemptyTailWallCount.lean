import ImbalancedChen.P2FiniteMarkedGamma5GateAffine
import ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport
import ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall
import Mathlib.Order.Filter.Finite

/-!
One ordinary count for all nonproduct walls of an original Gamma5
tuple with nonempty tail. The tuple is the bounded labelled prime
enumerator in its original old/fresh/tail order, with the original
one-sided physical proper-strip predicate. A common threshold works
for every physical width up to one at fixed root-cell exponent.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount

noncomputable section
open Filter Finset Real
open P2FiniteMarkedGamma5RadialRoughMass (cut norm)
open P2FiniteMarkedGamma5PhysicalExtension (Slot PhysicalPoint logPoint)
open P2FiniteMarkedGamma5LogExtension (Gate program margin)
open P2FiniteMarkedGamma5NonradialSupport (properStrip)
open P2FiniteMarkedGamma5GateAffine (numbering reservable reducedForm intercept gate_strip_adapter)
open P2FiniteMarkedGamma5OmittedPrimeWall (BoundedTuple remaining wallTuples exists_wallTuples_payment)
open scoped Classical BigOperators Topology

abbrev Tuple (N k r : ℕ) := BoundedTuple N (k + (1 + r))

def tagged {N k r : ℕ} (t : Tuple N k r) : PhysicalPoint k r :=
  fun s => ((t (numbering k r s)).val : ℝ)

private def baseTuples (N k r : ℕ) : Finset (Tuple N k r) :=
  (Part3.labelledPrimeTuples ((k + (1 + r)) + 1) (2 * N)).filter fun t =>
    (∀ i, cut N ≤ ((t i).val : ℝ)) ∧
      Part3.labelledProduct t ≤ 2 * N ∧ (Part3.labelledProduct t).Coprime N

/-- The finite carrier demands neither profile nonvanishing nor a
history witness. Thus every supported inner tuple meeting these same
integer conditions and one original nonproduct strip is included. -/
def properTuples (N k r : ℕ) (Q width : ℝ) : Finset (Tuple N k r) :=
  (baseTuples N k r).filter fun t =>
    properStrip (log Q) (log (N : ℝ)) width (logPoint (tagged t))

private def gates (r : ℕ) := (program r).erase Gate.product

private def gateTuples (N k r : ℕ) (Q width : ℝ) (g : Gate r) :
    Finset (Tuple N k r) :=
  (baseTuples N k r).filter fun t =>
    -width < margin (log Q) (log (N : ℝ)) (logPoint (tagged t)) g ∧
    margin (log Q) (log (N : ℝ)) (logPoint (tagged t)) g ≤ 0

private theorem gate_reservable {k r : ℕ} (hr : 0 < r) {g : Gate r}
    (hg : g ∈ gates r) : reservable k g := by
  have hne : g ≠ .product := (mem_erase.mp hg).1
  cases g <;> simp_all [reservable]

/-- Select the slot and the affine reserve for this gate before N, Q
or width. The physical strip width divided by log N eventually lies
below the fixed affine width for every 0 < width ≤ 1. -/
private theorem one_gate {k r : ℕ} (hr : 0 < r) (ν : ℝ) {g : Gate r}
    (hg : g ∈ gates r) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q width : ℝ), log Q / log (N : ℝ) = ν →
      0 < width → width ≤ 1 →
        norm N * ((gateTuples N k r Q width g).card : ℝ) ≤ η := by
  obtain ⟨o, hn, Hform⟩ := gate_strip_adapter (k := k) g (mem_erase.mp hg).2
    (gate_reservable hr hg)
  let j := numbering k r o
  let L := fun _ : Fin 1 => reducedForm (numbering k r) o g
  let c := fun _ : Fin 1 => intercept ν g
  obtain ⟨δ, hδ, H⟩ := exists_wallTuples_payment
    (d := k + (1 + r)) (by omega) j L c (fun _ => hn) hη
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [H, hlog.eventually_ge_atTop (1 / δ),
    eventually_gt_atTop (1 : ℕ)] with N hpaid hlarge hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNlog := log_pos hNr
  change 1 / δ ≤ log (N : ℝ) at hlarge
  intro Q width hQ _hw hw1
  have hwidth : width / log (N : ℝ) ≤ δ := by
    apply (div_le_iff₀ hNlog).mpr
    exact hw1.trans (by simpa only [mul_comm δ] using (div_le_iff₀ hδ).mp hlarge)
  have hsub : gateTuples N k r Q width g ⊆ wallTuples N j L c δ := by
    intro t ht
    obtain ⟨hbase, hlo, hhi⟩ := mem_filter.mp ht
    obtain ⟨hprime, hfloor, hcap, hcop⟩ := mem_filter.mp hbase
    refine mem_filter.mpr ⟨hprime, hfloor, hcap, hcop, ?_⟩
    change ∃ i : Fin 1, |L i (actualPrimeTupleLog N (remaining j t)) - c i| ≤ δ
    exact ⟨0, (Hform N Q ν width (fun i => (t i).val) hNlog hQ hlo hhi).trans hwidth⟩
  have hnrm : 0 ≤ norm N := div_nonneg hNlog.le (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) hnrm).trans hpaid

private theorem cover (N k r : ℕ) (Q width : ℝ) :
    properTuples N k r Q width ⊆
      (gates r).biUnion (gateTuples N k r Q width) := by
  intro t ht
  obtain ⟨hbase, g, hg, hne, hlo, hhi⟩ := mem_filter.mp ht
  exact mem_biUnion.mpr ⟨g, mem_erase.mpr ⟨hne, hg⟩,
    mem_filter.mpr ⟨hbase, hlo, hhi⟩⟩

/-- At fixed old and tail ranks and root-cell exponent there is one
threshold for all Q with the specified log ratio and all allowed widths.
Overlap of walls incurs only the fixed finite union bound. -/
theorem eventually_properTuples_payment (k r : ℕ) (hr : 0 < r) (ν : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q width : ℝ), log Q / log (N : ℝ) = ν →
      0 < width → width ≤ 1 →
        norm N * ((properTuples N k r Q width).card : ℝ) ≤ ε := by
  let e := ε / (((gates r).card : ℝ) + 1)
  have hden : 0 < ((gates r).card : ℝ) + 1 := by positivity
  have he : 0 < e := div_pos hε hden
  have Hall : ∀ᶠ N : ℕ in atTop, ∀ g ∈ gates r, ∀ (Q width : ℝ),
      log Q / log (N : ℝ) = ν → 0 < width → width ≤ 1 →
        norm N * ((gateTuples N k r Q width g).card : ℝ) ≤ e :=
    (eventually_all_finset (gates r)).mpr (fun _ hg => one_gate hr ν hg he)
  filter_upwards [Hall, eventually_gt_atTop (1 : ℕ)] with N H hN
  intro Q width hQ hw hw1
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hnrm : 0 ≤ norm N := div_nonneg (log_pos hNr).le (Nat.cast_nonneg _)
  have hcount : ((properTuples N k r Q width).card : ℝ) ≤
      ∑ g ∈ gates r, ((gateTuples N k r Q width g).card : ℝ) := by
    exact_mod_cast (card_le_card (cover N k r Q width)).trans card_biUnion_le
  calc
    _ ≤ norm N * ∑ g ∈ gates r, ((gateTuples N k r Q width g).card : ℝ) :=
      mul_le_mul_of_nonneg_left hcount hnrm
    _ = _ := mul_sum ..
    _ ≤ ∑ _g ∈ gates r, e := sum_le_sum (fun g hg => H g hg Q width hQ hw hw1)
    _ = ((gates r).card : ℝ) * e := by simp
    _ ≤ (((gates r).card : ℝ) + 1) * e :=
      mul_le_mul_of_nonneg_right (by linarith) he.le
    _ = ε := by
      dsimp only [e]
      rw [mul_comm, div_mul_cancel₀ _ hden.ne']

end
end ImbalancedChen.P2FiniteMarkedGamma5NonemptyTailWallCount
