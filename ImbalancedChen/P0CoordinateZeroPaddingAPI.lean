import ImbalancedChen.Part5SavedParent394700BuchstabAll32
import ImbalancedChen.Part5SavedParent394700BuchstabCoordinateAPI
import ImbalancedChen.P0CoordinateListAlgebra

/-!
SOURCEONLY / UNCOMPILED / NOT PASS. 2026-10-24.
Exact zero-padding laws for the original ragged integer-list certificate API.
Imports are candidate module mappings pinned in the companion checkpoint.
Zero-default coordinate equality never implies raw list equality without
an equal-length premise. positiveList is STRICT positive; a zero suffix
fails that Boolean check, even though the real polynomial is unchanged.
-/

namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
namespace P0CoordinateZeroPaddingAPI

/-- Append exactly m zero coefficients, retaining their list positions. -/
def zeroPad (a : List ℤ) (m : ℕ) : List ℤ := a ++ List.replicate m 0

/-- Extend to a requested length; a request below the old length retains it. -/
def padTo (a : List ℤ) (N : ℕ) : List ℤ := zeroPad a (N - a.length)

@[simp] theorem zeroPad_zero (a : List ℤ) : zeroPad a 0 = a := by
  simp only [zeroPad, List.replicate_zero, List.append_nil]

@[simp] theorem length_zeroPad (a : List ℤ) (m : ℕ) :
    (zeroPad a m).length = a.length + m := by
  simp only [zeroPad, List.length_append, List.length_replicate]

theorem getD_replicate_zero (m i : ℕ) :
    (List.replicate m (0 : ℤ)).getD i 0 = 0 := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
      cases i with
      | zero => simp only [List.replicate_succ, List.getD_cons_zero]
      | succ i =>
          simpa only [List.replicate_succ, List.getD_cons_succ] using ih i

/-- The suffix contributes zero at every index, including indices outside
both original and extended lists. -/
@[simp] theorem getD_zeroPad (a : List ℤ) (m i : ℕ) :
    (zeroPad a m).getD i 0 = a.getD i 0 := by
  induction a generalizing i with
  | nil => simp [zeroPad, getD_replicate_zero]
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [zeroPad, List.cons_append, List.getD_cons_succ] using ih i

@[simp] theorem length_padTo (a : List ℤ) (N : ℕ) :
    (padTo a N).length = max a.length N := by
  rw [padTo, length_zeroPad]
  omega

@[simp] theorem getD_padTo (a : List ℤ) (N i : ℕ) :
    (padTo a N).getD i 0 = a.getD i 0 := by
  exact getD_zeroPad a (N - a.length) i

/-- Equal normalization lengths license raw list extensionality. -/
theorem padTo_ext_iff (a b : List ℤ) (N : ℕ)
    (ha : a.length ≤ N) (hb : b.length ≤ N) :
    padTo a N = padTo b N ↔ ∀ i : ℕ, a.getD i 0 = b.getD i 0 := by
  constructor
  · intro h i
    have hi := congrArg (fun xs : List ℤ => xs.getD i 0) h
    simpa only [getD_padTo] using hi
  · intro h
    apply FiniteBernsteinCoordinate.ext_getD
    · rw [length_padTo, length_padTo]
      omega
    · intro i hi
      simpa only [getD_padTo] using h i

/-- This converse explicitly requires equality of the ORIGINAL lengths. -/
theorem eq_of_zeroPad_eq (a b : List ℤ) (m r : ℕ)
    (hlen : a.length = b.length) (h : zeroPad a m = zeroPad b r) : a = b := by
  apply FiniteBernsteinCoordinate.ext_getD a b hlen
  intro i hi
  have he := congrArg (fun xs : List ℤ => xs.getD i 0) h
  simpa only [getD_zeroPad] using he

theorem column_replicate_zero (n i k m : ℕ) :
    FiniteBernsteinCoordinate.column n i k (List.replicate m 0) = 0 := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
      change 0 * (bernsteinList n k).getD i 0 +
        FiniteBernsteinCoordinate.column n i (k + 1) (List.replicate m 0) = 0
      rw [ih, zero_mul, zero_add]

/-- Degree and initial index stay fixed; appended coefficients do not shift
the original chunk and contribute zero to its exact scalar column. -/
@[simp] theorem column_zeroPad (n i k : ℕ) (bs : List ℤ) (m : ℕ) :
    FiniteBernsteinCoordinate.column n i k (zeroPad bs m) =
      FiniteBernsteinCoordinate.column n i k bs := by
  rw [zeroPad, P0CoordinateListAlgebra.column_append, column_replicate_zero, add_zero]

@[simp] theorem getD_bernsteinSumFrom_zeroPad (n k : ℕ) (bs : List ℤ) (m i : ℕ) :
    (bernsteinSumFrom n k (zeroPad bs m)).getD i 0 =
      (bernsteinSumFrom n k bs).getD i 0 := by
  rw [FiniteBernsteinCoordinate.getD_bernsteinSumFrom,
    FiniteBernsteinCoordinate.getD_bernsteinSumFrom, column_zeroPad]

/-- Exact support length visited by m new zero coefficients. It is not
assumed to be n+1, since raw basis lengths and out-of-degree indices matter. -/
def zeroBasisSpan (n k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => max (bernsteinList n k).length (zeroBasisSpan n (k + 1) m)

theorem length_bernsteinSumFrom_replicate_zero (n k m : ℕ) :
    (bernsteinSumFrom n k (List.replicate m 0)).length = zeroBasisSpan n k m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
      rw [List.replicate_succ, FiniteBernsteinCoordinate.length_bernsteinSumFrom_cons, ih]
      rfl

/-- The exact raw length after padding follows the ragged maximum rule. -/
theorem length_bernsteinSumFrom_zeroPad (n k : ℕ) (bs : List ℤ) (m : ℕ) :
    (bernsteinSumFrom n k (zeroPad bs m)).length =
      max (bernsteinSumFrom n k bs).length (zeroBasisSpan n (k + bs.length) m) := by
  rw [zeroPad, P0CoordinateListAlgebra.bernsteinSumFrom_append,
    FiniteBernsteinCoordinate.length_addList, length_bernsteinSumFrom_replicate_zero]

/-- Raw fold equality includes exactly the zero suffix needed by the new
basis support. It does not silently discard the fold's trailing zeros. -/
theorem bernsteinSumFrom_zeroPad_exact (n k : ℕ) (bs : List ℤ) (m : ℕ) :
    bernsteinSumFrom n k (zeroPad bs m) =
      zeroPad (bernsteinSumFrom n k bs)
        (zeroBasisSpan n (k + bs.length) m - (bernsteinSumFrom n k bs).length) := by
  apply FiniteBernsteinCoordinate.ext_getD
  · rw [length_bernsteinSumFrom_zeroPad, length_zeroPad]
    omega
  · intro i hi
    rw [getD_bernsteinSumFrom_zeroPad, getD_zeroPad]

/-- Scalar multiplication preserves the zero suffix and its exact length. -/
theorem scaleList_zeroPad (c : ℤ) (a : List ℤ) (m : ℕ) :
    scaleList c (zeroPad a m) = zeroPad (scaleList c a) m := by
  apply FiniteBernsteinCoordinate.ext_getD
  · rw [FiniteBernsteinCoordinate.length_scaleList, length_zeroPad,
      length_zeroPad, FiniteBernsteinCoordinate.length_scaleList]
  · intro i hi
    rw [FiniteBernsteinCoordinate.getD_scaleList, getD_zeroPad,
      getD_zeroPad, FiniteBernsteinCoordinate.getD_scaleList]

/-- Padding two ragged summands only extends the old sum by actual zeros. -/
theorem addList_zeroPad (a b : List ℤ) (m r : ℕ) :
    addList (zeroPad a m) (zeroPad b r) =
      zeroPad (addList a b)
        (max (a.length + m) (b.length + r) - max a.length b.length) := by
  apply FiniteBernsteinCoordinate.ext_getD
  · rw [FiniteBernsteinCoordinate.length_addList, length_zeroPad, length_zeroPad,
      length_zeroPad, FiniteBernsteinCoordinate.length_addList]
    omega
  · intro i hi
    rw [FiniteBernsteinCoordinate.getD_addList, getD_zeroPad, getD_zeroPad,
      getD_zeroPad, FiniteBernsteinCoordinate.getD_addList]

theorem absSum_append (a b : List ℤ) : absSum (a ++ b) = absSum a + absSum b := by
  simp only [absSum, List.map_append, List.sum_append]

theorem absSum_replicate_zero (m : ℕ) : absSum (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simpa only [List.replicate_succ, absSum, List.map_cons, List.sum_cons,
        abs_zero, zero_add] using ih

@[simp] theorem absSum_zeroPad (a : List ℤ) (m : ℕ) :
    absSum (zeroPad a m) = absSum a := by
  rw [zeroPad, absSum_append, absSum_replicate_zero, add_zero]

/-- The actual residual check is invariant under independent zero suffixes
on the two represented lists. No raw equality of ragged lists is inferred. -/
theorem residual_zeroPad (a b : List ℤ) (m r : ℕ) :
    absSum (addList (zeroPad a m) (scaleList (-1) (zeroPad b r))) =
      absSum (addList a (scaleList (-1) b)) := by
  rw [scaleList_zeroPad, addList_zeroPad, absSum_zeroPad]

/-- Coefficient padding preserves the integer residual value of the actual
Bernstein fold, while its separate STRICT positivity check may fail. -/
theorem bernstein_residual_zeroPad (n k : ℕ) (a bs : List ℤ) (m : ℕ) :
    absSum (addList a (scaleList (-1) (bernsteinSumFrom n k (zeroPad bs m)))) =
      absSum (addList a (scaleList (-1) (bernsteinSumFrom n k bs))) := by
  rw [bernsteinSumFrom_zeroPad_exact]
  simpa only [zeroPad_zero] using
    residual_zeroPad a (bernsteinSumFrom n k bs) 0
      (zeroBasisSpan n (k + bs.length) m - (bernsteinSumFrom n k bs).length)

theorem positiveList_append (a b : List ℤ) :
    positiveList (a ++ b) = (positiveList a && positiveList b) := by
  induction a with
  | nil => simp only [List.nil_append, primitive_positiveList_nil, Bool.true_and]
  | cons x xs ih =>
      simp only [List.cons_append, primitive_positiveList_cons, ih, Bool.and_assoc]

/-- The original Boolean test is strict, so a nonempty zero suffix fails. -/
theorem positiveList_zeroPad_succ (a : List ℤ) (m : ℕ) :
    positiveList (zeroPad a (m + 1)) = false := by
  rw [zeroPad, positiveList_append, List.replicate_succ, primitive_positiveList_cons]
  norm_num

noncomputable section

theorem evalList_replicate_zero (m : ℕ) (t : ℝ) :
    evalList (List.replicate m 0) t = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [List.replicate_succ, evalList, Int.cast_zero, zero_add, ih, mul_zero]

/-- Exact Horner semantics are unchanged by output coefficient padding. -/
@[simp] theorem evalList_zeroPad (a : List ℤ) (m : ℕ) (t : ℝ) :
    evalList (zeroPad a m) t = evalList a t := by
  induction a with
  | nil => simpa only [zeroPad, List.nil_append, evalList] using evalList_replicate_zero m t
  | cons x xs ih =>
      simpa only [zeroPad, List.cons_append, evalList] using
        congrArg (fun y : ℝ => (x : ℝ) + t * y) ih

/-- Appending zero Bernstein coefficients preserves the actual folded
Horner polynomial, even when its raw list representation grows. -/
@[simp] theorem evalList_bernsteinSumFrom_zeroPad
    (n k : ℕ) (bs : List ℤ) (m : ℕ) (t : ℝ) :
    evalList (bernsteinSumFrom n k (zeroPad bs m)) t =
      evalList (bernsteinSumFrom n k bs) t := by
  rw [bernsteinSumFrom_zeroPad_exact, evalList_zeroPad]

theorem bernstein_nonnegative_transport (n k : ℕ) (bs : List ℤ) (m : ℕ) (t : ℝ) :
    0 ≤ evalList (bernsteinSumFrom n k (zeroPad bs m)) t ↔
      0 ≤ evalList (bernsteinSumFrom n k bs) t := by
  rw [evalList_bernsteinSumFrom_zeroPad]

/-- Transport the genuine certificate's NONNEGATIVE CONCLUSION to an output
polynomial padded by zeros. The check is still on the original homogeneous
list: padding q itself changes its normalization exponent in that check. -/
theorem integer_certificate_zeroPad_nonneg_on_interval
    (n : ℕ) (M A B D : ℤ) (q bs : List ℤ) (m : ℕ)
    (hM : 0 < M) (hD : 0 < D) (hB : 0 < B)
    (hb : positiveList bs = true)
    (hid : absSum (addList (scaleList M (homogeneousAffine A B D q))
      (scaleList (-1) (bernsteinSumFrom n 0 bs))) = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ((A : ℝ) / D) (((A : ℝ) + B) / D)) :
    0 ≤ evalList (zeroPad q m) t := by
  rw [evalList_zeroPad]
  exact integer_Bernstein_certificate_on_interval n M A B D q bs hM hD hB hb hid ht

end
end P0CoordinateZeroPaddingAPI
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly
