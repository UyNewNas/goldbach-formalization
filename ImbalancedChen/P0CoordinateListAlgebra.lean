import ImbalancedChen.Part5SavedParent394700BuchstabCoordinateAPI

/-!
SOURCE_WRITTEN / UNCOMPILED / NOT ROOT_ACCEPTED. 2026-10-24.

Structural composition laws for the actual ragged integer-list operations.
The imported CoordinateAPI is the SOURCEONLY candidate in
20261024y-P5-SharedCoordinateAPI-SOURCEONLY, to be staged under its module name.
No finite certificate, positivity assertion, row constant, or bound is added.
In particular scalar zero preserves list length; it does not yield [].
-/

namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace P0CoordinateListAlgebra

theorem addList_comm (a b : List ℤ) : addList a b = addList b a := by
  induction a generalizing b with
  | nil => exact (primitive_addList_nil_right b).symm
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          simp only [primitive_addList_cons_cons, ih, add_comm]

theorem addList_assoc (a b c : List ℤ) :
    addList (addList a b) c = addList a (addList b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          cases c with
          | nil =>
              simp only [primitive_addList_nil_right]
          | cons z zs =>
              simp only [primitive_addList_cons_cons, ih, add_assoc]

theorem addList_interchange (a b c d : List ℤ) :
    addList (addList a b) (addList c d) =
      addList (addList a c) (addList b d) := by
  calc
    addList (addList a b) (addList c d) =
        addList a (addList b (addList c d)) := addList_assoc _ _ _
    _ = addList a (addList (addList b c) d) := by rw [addList_assoc b c d]
    _ = addList a (addList (addList c b) d) := by rw [addList_comm b c]
    _ = addList a (addList c (addList b d)) := by rw [addList_assoc c b d]
    _ = addList (addList a c) (addList b d) := (addList_assoc _ _ _).symm

theorem scaleList_one (a : List ℤ) : scaleList 1 a = a := by
  simp [scaleList]

/-- The exact zero object retains all trailing zero coordinates. -/
theorem scaleList_zero (a : List ℤ) :
    scaleList 0 a = a.map (fun _ => (0 : ℤ)) := by
  simp [scaleList]

theorem scaleList_mul (c d : ℤ) (a : List ℤ) :
    scaleList c (scaleList d a) = scaleList (c * d) a := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      change (c * (d * x)) :: scaleList c (scaleList d xs) =
        ((c * d) * x) :: scaleList (c * d) xs
      rw [ih, mul_assoc]

/-- Scalar multiplication distributes over ragged, zero-default addition. -/
theorem scaleList_addList (c : ℤ) (a b : List ℤ) :
    scaleList c (addList a b) = addList (scaleList c a) (scaleList c b) := by
  induction a generalizing b with
  | nil => rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          change (c * (x + y)) :: scaleList c (addList xs ys) =
            (c * x + c * y) :: addList (scaleList c xs) (scaleList c ys)
          rw [ih, mul_add]

theorem scaleList_add_scalar (c d : ℤ) (a : List ℤ) :
    scaleList (c + d) a = addList (scaleList c a) (scaleList d a) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
      change ((c + d) * x) :: scaleList (c + d) xs =
        (c * x + d * x) :: addList (scaleList c xs) (scaleList d xs)
      rw [ih, add_mul]

theorem scaleList_append (c : ℤ) (a b : List ℤ) :
    scaleList c (a ++ b) = scaleList c a ++ scaleList c b := by
  simp only [scaleList, List.map_append]

/-- Coefficients from a second chunk start after the first chunk's length. -/
theorem column_append (n i k : ℕ) (xs bs : List ℤ) :
    FiniteBernsteinCoordinate.column n i k (xs ++ bs) =
      FiniteBernsteinCoordinate.column n i k xs +
        FiniteBernsteinCoordinate.column n i (k + xs.length) bs := by
  induction xs generalizing k with
  | nil => simp [FiniteBernsteinCoordinate.column]
  | cons a xs ih =>
      change a * (bernsteinList n k).getD i 0 +
          FiniteBernsteinCoordinate.column n i (k + 1) (xs ++ bs) =
        (a * (bernsteinList n k).getD i 0 +
          FiniteBernsteinCoordinate.column n i (k + 1) xs) +
            FiniteBernsteinCoordinate.column n i (k + (xs.length + 1)) bs
      rw [ih]
      have hk : k + (xs.length + 1) = (k + 1) + xs.length := by omega
      rw [hk, add_assoc]

/-- Exact list equality allows composition without erasing trailing zeros. -/
theorem bernsteinSumFrom_append (n k : ℕ) (xs bs : List ℤ) :
    bernsteinSumFrom n k (xs ++ bs) =
      addList (bernsteinSumFrom n k xs)
        (bernsteinSumFrom n (k + xs.length) bs) := by
  induction xs generalizing k with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero,
      primitive_bernsteinSumFrom_nil, primitive_addList_nil]
  | cons a xs ih =>
      change addList (scaleList a (bernsteinList n k))
          (bernsteinSumFrom n (k + 1) (xs ++ bs)) =
        addList (addList (scaleList a (bernsteinList n k))
          (bernsteinSumFrom n (k + 1) xs))
            (bernsteinSumFrom n (k + (xs.length + 1)) bs)
      rw [ih]
      have hk : k + (xs.length + 1) = (k + 1) + xs.length := by omega
      rw [hk, addList_assoc]

/-- Scaling a coefficient chunk commutes with its ordered Bernstein fold. -/
theorem bernsteinSumFrom_scaleList (n k : ℕ) (c : ℤ) (bs : List ℤ) :
    bernsteinSumFrom n k (scaleList c bs) =
      scaleList c (bernsteinSumFrom n k bs) := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih =>
      change addList (scaleList (c * b) (bernsteinList n k))
          (bernsteinSumFrom n (k + 1) (scaleList c bs)) =
        scaleList c (addList (scaleList b (bernsteinList n k))
          (bernsteinSumFrom n (k + 1) bs))
      rw [ih, scaleList_addList, scaleList_mul]

/-- Two coefficient chunks at the same initial index combine pointwise. -/
theorem bernsteinSumFrom_addList (n k : ℕ) (xs ys : List ℤ) :
    bernsteinSumFrom n k (addList xs ys) =
      addList (bernsteinSumFrom n k xs) (bernsteinSumFrom n k ys) := by
  induction xs generalizing k ys with
  | nil => rfl
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp only [primitive_addList_nil_right, primitive_bernsteinSumFrom_nil]
      | cons y ys =>
          change addList (scaleList (x + y) (bernsteinList n k))
              (bernsteinSumFrom n (k + 1) (addList xs ys)) =
            addList (addList (scaleList x (bernsteinList n k))
              (bernsteinSumFrom n (k + 1) xs))
                (addList (scaleList y (bernsteinList n k))
                  (bernsteinSumFrom n (k + 1) ys))
          rw [scaleList_add_scalar, ih, addList_interchange]

end P0CoordinateListAlgebra
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

