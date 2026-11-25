import ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport
import ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget
import ImbalancedChen.FinitePrimeGeometryCore
import Mathlib.Algebra.BigOperators.Fin

/-! Exact normalized affine forms of the original Gamma5 nonproduct gates.
The omitted and witness slots are selected from the gate and ranks alone.
The unit-tail exceptions are identified separately. -/
namespace ImbalancedChen.P2FiniteMarkedGamma5GateAffine

noncomputable section
open Finset Real
open P2SeedOmegaLiteralFibre (a0 a2)
open P2FiniteMarkedGamma5LogExtension (Gate program mem_program margin)
open P2FiniteMarkedGamma5PhysicalExtension (Slot PhysicalPoint logPoint)
open P2FiniteMarkedGamma5EulerWordBudget (slotEquiv)
open P2FiniteMarkedGamma5NonradialSupport (properStrip)
open scoped Classical BigOperators

private def oldMask {k r : ℕ} : Slot k r → ℝ
  | .inl _ => 1
  | .inr _ => 0

private def atom {k r : ℕ} (s : Slot k r) : Slot k r → ℝ :=
  fun i => if s = i then 1 else 0

private abbrev fresh {k r : ℕ} (i : Fin 2) : Slot k r := .inr (.inl i)
private abbrev tail {k r : ℕ} (i : Fin r) : Slot k r := .inr (.inr i)

/-- Coefficients on the full tagged coordinates; every old slot gets its
own coefficient. The product case is excluded in every wall theorem. -/
def coeff {k r : ℕ} : Gate r → Slot k r → ℝ
  | .lower i => a0 • oldMask + atom (fresh i)
  | .upper i => (-a2) • oldMask - atom (fresh i)
  | .pairOrder => atom (fresh 1) - atom (fresh 0)
  | .badSquare => oldMask + (2 : ℝ) • atom (fresh 0) + atom (fresh 1)
  | .rough i => a0 • oldMask + atom (tail i)
  | .tailOrder i j => atom (tail j) - atom (tail i)
  | .product => 0

def intercept {r : ℕ} (ν : ℝ) : Gate r → ℝ
  | .lower _ | .rough _ => a0 * ν
  | .upper _ => -a2 * ν
  | .badSquare => ν
  | _ => 0

def reservable (k : ℕ) {r : ℕ} : Gate r → Prop
  | .pairOrder => 0 < k ∨ 0 < r
  | .badSquare => 0 < r
  | .product => False
  | _ => True

/-- The only proper faces without an unused coordinate have zero tails.
The pair-order exception additionally has no old coordinate. -/
theorem not_reservable_iff {k r : ℕ} {g : Gate r} (hg : g ≠ .product) :
    ¬ reservable k g ↔
      (g = .badSquare ∧ r = 0) ∨ (g = .pairOrder ∧ k = 0 ∧ r = 0) := by
  cases g <;> simp_all [reservable]

/-- A missing coefficient and a surviving nonzero one. Distinct tail
indices are required by program membership; their prime values may agree. -/
theorem reserve_and_witness {k r : ℕ} {g : Gate r} (hg : g ∈ program r)
    (hres : reservable k g) :
    ∃ o h : Slot k r, coeff g o = 0 ∧ coeff g h ≠ 0 := by
  cases g with
  | lower i =>
    fin_cases i
    · exact ⟨fresh 1, fresh 0, by norm_num [coeff, oldMask, atom, fresh]⟩
    · exact ⟨fresh 0, fresh 1, by norm_num [coeff, oldMask, atom, fresh]⟩
  | upper i =>
    fin_cases i
    · exact ⟨fresh 1, fresh 0, by norm_num [coeff, oldMask, atom, fresh]⟩
    · exact ⟨fresh 0, fresh 1, by norm_num [coeff, oldMask, atom, fresh]⟩
  | pairOrder =>
    rcases hres with hk | hr
    · exact ⟨.inl ⟨0, hk⟩, fresh 1, by norm_num [coeff, atom, fresh]⟩
    · exact ⟨tail ⟨0, hr⟩, fresh 1, by norm_num [coeff, atom, tail, fresh]⟩
  | badSquare =>
    exact ⟨tail ⟨0, hres⟩, fresh 1, by norm_num [coeff, oldMask, atom, tail, fresh]⟩
  | rough i =>
    exact ⟨fresh 0, tail i, by simp [coeff, oldMask, atom, tail, fresh]⟩
  | tailOrder i j =>
    have hij : i < j := mem_program.mp hg
    exact ⟨fresh 0, tail j, by simp [coeff, atom, fresh, tail, ne_of_lt hij]⟩
  | product => exact hres.elim

private def dot {k r : ℕ} (a z : Slot k r → ℝ) := ∑ i, a i * z i

private theorem dot_old {k r : ℕ} (z : Slot k r → ℝ) :
    dot oldMask z = ∑ i, z (.inl i) := by
  simp [dot, Fintype.sum_sum_type, oldMask]

private theorem dot_atom {k r : ℕ} (j : Slot k r) (z : Slot k r → ℝ) :
    dot (atom j) z = z j := by
  simp [dot, atom, ite_mul]

private theorem dot_add {k r : ℕ} (a b z : Slot k r → ℝ) :
    dot (a+b) z = dot a z + dot b z := by simp [dot, add_mul, sum_add_distrib]

private theorem dot_sub {k r : ℕ} (a b z : Slot k r → ℝ) :
    dot (a-b) z = dot a z - dot b z := by simp [dot, sub_mul, sum_sub_distrib]

private theorem dot_smul {k r : ℕ} (c : ℝ) (a z : Slot k r → ℝ) :
    dot (c • a) z = c * dot a z := by simp [dot, mul_sum, mul_assoc, smul_eq_mul]

/-- The original margin divided by log N is exactly L minus its fixed
intercept. The equality also covers points on strict faces. -/
private theorem normalized_margin {k r : ℕ} (x : PhysicalPoint k r)
    (g : Gate r) (hg : g ≠ .product) {Q N ν : ℝ} (hlog : log Q / log N = ν) :
    margin (log Q) (log N) (logPoint x) g / log N =
      dot (coeff g) (fun s => log (x s) / log N) - intercept ν g := by
  rw [← hlog]
  cases g <;>
    simp_all only [coeff, intercept, margin, logPoint, dot_add, dot_sub, dot_smul,
      dot_old, dot_atom, fresh, tail, div_eq_mul_inv, ← Finset.sum_mul] <;> ring

/-- The canonical numbering preserves each old, fresh and rough slot
and places the result in a successor-sized Fin type for succAbove. -/
def numbering (k r : ℕ) : Slot k r ≃ Fin ((k + (1 + r)) + 1) :=
  (slotEquiv k r).trans (finCongr (by omega))

def reducedForm {d k r : ℕ} (e : Slot k r ≃ Fin (d + 1))
    (o : Slot k r) (g : Gate r) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin d, coeff g (e.symm ((e o).succAbove i)) • ContinuousLinearMap.proj i

private theorem reducedForm_apply {d k r : ℕ} (e : Slot k r ≃ Fin (d + 1))
    (o : Slot k r) (g : Gate r) (w : Fin d → ℝ) :
    reducedForm e o g w =
      ∑ i : Fin d, coeff g (e.symm ((e o).succAbove i)) * w i := by
  unfold reducedForm
  generalize (univ : Finset (Fin d)) = S
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => simp [sum_insert hi, ih, smul_eq_mul]

theorem reducedForm_ne_zero {d k r : ℕ} (e : Slot k r ≃ Fin (d + 1))
    {o h : Slot k r} {g : Gate r} (ho : coeff g o = 0) (hh : coeff g h ≠ 0) :
    reducedForm e o g ≠ 0 := by
  have hne : e h ≠ e o := by
    intro he
    exact hh (by rw [e.injective he]; exact ho)
  obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
  intro hz
  have hval := congrArg (fun F : (Fin d → ℝ) →L[ℝ] ℝ =>
    F (fun j => if j = i then 1 else 0)) hz
  have hc : coeff g (e.symm ((e o).succAbove i)) = 0 := by
    simpa [reducedForm_apply, mul_ite] using hval
  exact hh (by simpa only [hi, Equiv.symm_apply_apply] using hc)

/-- Equality to the remaining ordered prime log vector used by the
actual affine reserve. No target or coordinate coprimality is used in
this identity; exclusions enter in the separate counting bound. -/
theorem normalized_margin_eq_reduced {d k r : ℕ} (e : Slot k r ≃ Fin (d+1))
    (o : Slot k r) (g : Gate r) (hg : g ≠ .product) (ho : coeff g o = 0)
    (p : Fin (d+1) → ℕ) (N : ℕ) {Q ν : ℝ} (hlog : log Q / log (N : ℝ) = ν) :
    margin (log Q) (log (N : ℝ))
        (logPoint (fun s : Slot k r => (p (e s) : ℝ))) g / log (N : ℝ) =
      reducedForm e o g (actualPrimeTupleLog N (fun i => p ((e o).succAbove i))) -
        intercept ν g := by
  rw [normalized_margin _ _ hg hlog, reducedForm_apply]
  congr 1
  unfold dot
  let f := fun j : Fin (d+1) => coeff g (e.symm j) * (log (p j : ℝ) / log (N : ℝ))
  calc
    _ = ∑ j : Fin (d+1), f j := by
      simpa only [f, Equiv.symm_apply_apply] using e.sum_comp f
    _ = _ := by
      rw [Fin.sum_univ_succAbove f (e o)]
      simp only [f, Equiv.symm_apply_apply, ho, zero_mul, zero_add, actualPrimeTupleLog]

/-- The slot and nonzero form depend only on the rank and original
gate. Width, scale, physical point and the common root-cell parameter
are all supplied after this choice. -/
theorem gate_strip_adapter {k r : ℕ} (g : Gate r) (hg : g ∈ program r)
    (hres : reservable k g) :
    ∃ o : Slot k r, reducedForm (numbering k r) o g ≠ 0 ∧
      ∀ (N : ℕ) (Q ν width : ℝ) (p : Fin ((k + (1 + r)) + 1) → ℕ),
        0 < log (N : ℝ) → log Q / log (N : ℝ) = ν →
        -width < margin (log Q) (log (N : ℝ))
          (logPoint (fun s : Slot k r => (p (numbering k r s) : ℝ))) g →
        margin (log Q) (log (N : ℝ))
          (logPoint (fun s : Slot k r => (p (numbering k r s) : ℝ))) g ≤ 0 →
        |reducedForm (numbering k r) o g
            (actualPrimeTupleLog N (fun i => p (((numbering k r) o).succAbove i))) -
          intercept ν g| ≤ width / log (N : ℝ) := by
  obtain ⟨o, h, ho, hh⟩ := reserve_and_witness hg hres
  refine ⟨o, reducedForm_ne_zero _ ho hh, ?_⟩
  intro N Q ν width p hN hlog hlo hhi
  have hg' : g ≠ .product := by rintro rfl; exact hres
  rw [← normalized_margin_eq_reduced _ _ _ hg' ho p N hlog]
  rw [abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨hlo.le, by linarith⟩) hN.le

/-- A witness of the original one-sided strip is either one of the
two unit-tail cases, or has an omitted-slot affine wall witness. -/
theorem physical_properStrip_cases {k r : ℕ} (N : ℕ) (Q ν width : ℝ)
    (p : Fin ((k + (1 + r)) + 1) → ℕ) (hN : 0 < log (N : ℝ))
    (hlog : log Q / log (N : ℝ) = ν)
    (hs : properStrip (log Q) (log (N : ℝ)) width
      (logPoint (fun s : Slot k r => (p (numbering k r s) : ℝ)))) :
    ∃ g ∈ program r, g ≠ .product ∧
      ((g = .badSquare ∧ r = 0) ∨ (g = .pairOrder ∧ k = 0 ∧ r = 0) ∨
        ∃ o : Slot k r, reducedForm (numbering k r) o g ≠ 0 ∧
          |reducedForm (numbering k r) o g
            (actualPrimeTupleLog N (fun i => p (((numbering k r) o).succAbove i))) -
            intercept ν g| ≤ width / log (N : ℝ)) := by
  obtain ⟨g, hg, hproper, hlo, hhi⟩ := hs
  refine ⟨g, hg, hproper, ?_⟩
  by_cases hr : reservable k g
  · obtain ⟨o, hn, H⟩ := gate_strip_adapter g hg hr
    exact Or.inr (Or.inr ⟨o, hn, H N Q ν width p hN hlog hlo hhi⟩)
  · rcases (not_reservable_iff hproper).mp hr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end
end ImbalancedChen.P2FiniteMarkedGamma5GateAffine
