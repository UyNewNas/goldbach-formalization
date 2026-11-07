import ImbalancedChen.Part5SavedParent394700BuchstabData

/-!
SOURCEONLY / UNCOMPILED / NOT PASS. 2026-10-24.
Written after the user suspended all local compilation.
No Lean, lake, runtime, checker, audit or certificate arithmetic was executed.

This API exposes only structural identities for the actual Data definitions.
It does not assert any row's integer certificate, positivity or BernsteinGood.
The original row and basis lists are neither copied nor recomputed.
The degree n, initial basis index k, coefficients and output coordinate i
remain explicit. Zero-default coordinate equality also needs equal lengths.
-/

namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace FiniteBernsteinCoordinate

/-- Ragged addition preserves all entries, using zero only outside a list. -/
theorem getD_addList (a b : List ℤ) (i : ℕ) :
    (addList a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp [addList]
  | cons x xs ih =>
      cases b with
      | nil => simp [addList]
      | cons y ys =>
          cases i with
          | zero => simp [addList]
          | succ i =>
              simpa only [primitive_addList_cons_cons, List.getD_cons_succ] using ih ys i

theorem getD_scaleList (c : ℤ) (a : List ℤ) (i : ℕ) :
    (scaleList c a).getD i 0 = c * a.getD i 0 := by
  induction a generalizing i with
  | nil => simp [scaleList]
  | cons x xs ih =>
      cases i with
      | zero => simp [scaleList]
      | succ i =>
          simpa only [scaleList, List.map_cons, List.getD_cons_succ] using ih i

/-- The exact scalar coordinate of the original ordered Bernstein fold. -/
def column (n i : ℕ) : ℕ → List ℤ → ℤ :=
  fun k bs =>
    List.rec (motive := fun _ => ℕ → ℤ)
      (fun _ => 0)
      (fun b _bs ih j => b * (bernsteinList n j).getD i 0 + ih (j + 1)) bs k

theorem getD_bernsteinSumFrom (n i k : ℕ) (bs : List ℤ) :
    (bernsteinSumFrom n k bs).getD i 0 = column n i k bs := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
      change
        (addList (scaleList b (bernsteinList n k))
          (bernsteinSumFrom n (k + 1) bs)).getD i 0 =
        b * (bernsteinList n k).getD i 0 + column n i (k + 1) bs
      rw [getD_addList, getD_scaleList, ih]

theorem getD_bernsteinSumFrom_cons (n i k : ℕ) (b : ℤ) (bs : List ℤ) :
    (bernsteinSumFrom n k (b :: bs)).getD i 0 =
      b * (bernsteinList n k).getD i 0 +
        (bernsteinSumFrom n (k + 1) bs).getD i 0 := by
  rw [primitive_bernsteinSumFrom_cons, getD_addList, getD_scaleList]

/-- Exact length, including any trailing zeros and multiplication by zero. -/
theorem length_addList (a b : List ℤ) :
    (addList a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [addList]
  | cons x xs ih =>
      cases b with
      | nil => simp [addList]
      | cons y ys =>
          simpa only [primitive_addList_cons_cons, List.length_cons,
            Nat.succ_max_succ] using congrArg Nat.succ (ih ys)

theorem length_scaleList (c : ℤ) (a : List ℤ) :
    (scaleList c a).length = a.length := by
  simp only [scaleList, List.length_map]

theorem length_bernsteinSumFrom_cons (n k : ℕ) (b : ℤ) (bs : List ℤ) :
    (bernsteinSumFrom n k (b :: bs)).length =
      max (bernsteinList n k).length (bernsteinSumFrom n (k + 1) bs).length := by
  rw [primitive_bernsteinSumFrom_cons, length_addList, length_scaleList]

/-- Equal lengths prevent zero-default projection from losing trailing zeros. -/
theorem ext_getD (a b : List ℤ) (hlen : a.length = b.length)
    (h : ∀ i, i < a.length → a.getD i 0 = b.getD i 0) : a = b := by
  apply List.ext_getElem hlen
  intro i hia hib
  calc
    a[i]'hia = a.getD i 0 := List.getElem_eq_getD 0
    _ = b.getD i 0 := h i hia
    _ = b[i]'hib := (List.getElem_eq_getD 0).symm

end FiniteBernsteinCoordinate
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
