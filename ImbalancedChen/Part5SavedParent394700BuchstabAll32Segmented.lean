import ImbalancedChen.Part5SavedParent394700BuchstabRow00Segmented
import ImbalancedChen.Part5SavedParent394700BuchstabRow01
import ImbalancedChen.Part5SavedParent394700BuchstabRow02
import ImbalancedChen.Part5SavedParent394700BuchstabRow03
import ImbalancedChen.Part5SavedParent394700BuchstabRow04
import ImbalancedChen.Part5SavedParent394700BuchstabRow05
import ImbalancedChen.Part5SavedParent394700BuchstabRow06
import ImbalancedChen.Part5SavedParent394700BuchstabRow07
import ImbalancedChen.Part5SavedParent394700BuchstabRow08
import ImbalancedChen.Part5SavedParent394700BuchstabRow09
import ImbalancedChen.Part5SavedParent394700BuchstabRow10
import ImbalancedChen.Part5SavedParent394700BuchstabRow11
import ImbalancedChen.Part5SavedParent394700BuchstabRow12
import ImbalancedChen.Part5SavedParent394700BuchstabRow13
import ImbalancedChen.Part5SavedParent394700BuchstabRow14
import ImbalancedChen.Part5SavedParent394700BuchstabRow15
import ImbalancedChen.Part5SavedParent394700BuchstabRow16
import ImbalancedChen.Part5SavedParent394700BuchstabRow17
import ImbalancedChen.Part5SavedParent394700BuchstabRow18
import ImbalancedChen.Part5SavedParent394700BuchstabRow19
import ImbalancedChen.Part5SavedParent394700BuchstabRow20
import ImbalancedChen.Part5SavedParent394700BuchstabRow21
import ImbalancedChen.Part5SavedParent394700BuchstabRow22
import ImbalancedChen.Part5SavedParent394700BuchstabRow23
import ImbalancedChen.Part5SavedParent394700BuchstabRow24
import ImbalancedChen.Part5SavedParent394700BuchstabRow25
import ImbalancedChen.Part5SavedParent394700BuchstabRow26
import ImbalancedChen.Part5SavedParent394700BuchstabRow27
import ImbalancedChen.Part5SavedParent394700BuchstabRow28
import ImbalancedChen.Part5SavedParent394700BuchstabRow29
import ImbalancedChen.Part5SavedParent394700BuchstabRow30
import ImbalancedChen.Part5SavedParent394700BuchstabRow31

/- SOURCEONLY all32 assembly; exact draft supplier pins are recorded in the CP.
   Strict source/object qualification and compilation remain pending. -/
namespace ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSegmentedSourceOnly
open ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSourceOnly

open Set
open scoped unitInterval
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

/-- All32 identities are integer/List computations, with no real functions,
Polynomial operations, Finsupp, or Classical instance inside this decision. -/
theorem finiteBernsteinGood : ∀ k : Fin 32, BernsteinGood k := by
  intro k
  fin_cases k
  · exact FiniteBernsteinResource.good00Segmented
  · exact FiniteBernsteinResource.good01
  · exact FiniteBernsteinResource.good02
  · exact FiniteBernsteinResource.good03
  · exact FiniteBernsteinResource.good04
  · exact FiniteBernsteinResource.good05
  · exact FiniteBernsteinResource.good06
  · exact FiniteBernsteinResource.good07
  · exact FiniteBernsteinResource.good08
  · exact FiniteBernsteinResource.good09
  · exact FiniteBernsteinResource.good10
  · exact FiniteBernsteinResource.good11
  · exact FiniteBernsteinResource.good12
  · exact FiniteBernsteinResource.good13
  · exact FiniteBernsteinResource.good14
  · exact FiniteBernsteinResource.good15
  · exact FiniteBernsteinResource.good16
  · exact FiniteBernsteinResource.good17
  · exact FiniteBernsteinResource.good18
  · exact FiniteBernsteinResource.good19
  · exact FiniteBernsteinResource.good20
  · exact FiniteBernsteinResource.good21
  · exact FiniteBernsteinResource.good22
  · exact FiniteBernsteinResource.good23
  · exact FiniteBernsteinResource.good24
  · exact FiniteBernsteinResource.good25
  · exact FiniteBernsteinResource.good26
  · exact FiniteBernsteinResource.good27
  · exact FiniteBernsteinResource.good28
  · exact FiniteBernsteinResource.good29
  · exact FiniteBernsteinResource.good30
  · exact FiniteBernsteinResource.good31

/-- Explicit first subcertificate, useful even before assembling all32. -/
theorem firstBernsteinGood : BernsteinGood (0 : Fin 32) := by
  exact FiniteBernsteinResource.good00Segmented

noncomputable section

/-- Dense coefficients interpreted as the actual real Horner function. -/
def evalList : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: ac, t => (a : ℝ) + t * evalList ac t

theorem eval_addList (a b : List ℤ) (t : ℝ) :
    evalList (addList a b) t = evalList a t + evalList b t := by
  induction a generalizing b with
  | nil => simp [addList, evalList]
  | cons x a ih =>
      cases b with
      | nil => simp [addList, evalList]
      | cons y b =>
          simp only [addList, evalList, ih, Int.cast_add]
          ring

theorem eval_scaleList (j : ℤ) (a : List ℤ) (t : ℝ) :
    evalList (scaleList j a) t = (j : ℝ) * evalList a t := by
  induction a with
  | nil => simp [scaleList, evalList]
  | cons x a ih =>
      change (((j * x : ℤ) : ℝ) + t * evalList (scaleList j a) t) =
        (j : ℝ) * ((x : ℝ) + t * evalList a t)
      rw [ih, Int.cast_mul]
      ring

private theorem eval_derivativeFrom (a : List ℤ) (t : ℝ) :
    ∀ n : ℕ, evalList (derivativeFrom n a) t =
      (n : ℝ) * evalList a t + t * evalList (derivList a) t := by
  induction a with
  | nil => intro n; simp [derivativeFrom, derivList, evalList]
  | cons x a ih =>
      intro n
      change ((((n : ℤ) * x : ℤ) : ℝ) +
        t * evalList (derivativeFrom (n + 1) a) t) =
          (n : ℝ) * ((x : ℝ) + t * evalList a t) +
            t * evalList (derivativeFrom 1 a) t
      rw [ih (n + 1), ih 1]
      push_cast
      ring

/-- The integer derivative list is the genuine real derivative. -/
private theorem hasDerivAt_evalList (a : List ℤ) (t : ℝ) :
    HasDerivAt (evalList a) (evalList (derivList a) t) t := by
  induction a with
  | nil => simpa [evalList, derivList, derivativeFrom] using hasDerivAt_const t (0 : ℝ)
  | cons x a ih =>
      have h := (hasDerivAt_const t (x : ℝ)).add ((hasDerivAt_id t).mul ih)
      change HasDerivAt (fun y : ℝ => (x : ℝ) + y * evalList a y)
        (evalList (derivativeFrom 1 a) t) t
      convert! h using 1
      simpa only [Nat.cast_one, zero_add, one_mul] using eval_derivativeFrom a t 1

/-- Structural semantic bridge for the finite residual checker. -/
private theorem eval_residualList (j : ℤ) (a b : List ℤ) (t : ℝ) :
    evalList (residualList j a b) t =
      ((j : ℝ) + t) * evalList (derivList a) t - evalList b t := by
  simp only [residualList, eval_addList, eval_scaleList, evalList,
    Int.cast_zero, Int.cast_neg, Int.cast_one, zero_add]
  ring

private theorem eval_zero (a : List ℤ) :
    evalList a 0 = (((a.head?).getD 0 : ℤ) : ℝ) := by
  cases a <;> simp [evalList]

private theorem eval_one (a : List ℤ) : evalList a 1 = (a.sum : ℝ) := by
  induction a with
  | nil => simp [evalList]
  | cons x a ih => simp [evalList, ih]

private theorem absSum_nonneg (a : List ℤ) : 0 ≤ absSum a := by
  induction a with
  | nil => simp [absSum]
  | cons x a ih =>
      have h : absSum (x :: a) = |x| + absSum a := by simp [absSum]
      rw [h]
      exact add_nonneg (abs_nonneg x) ih

/-- Coefficient l1 is a uniform bound on the actual real function on [0,1]. -/
private theorem abs_evalList_le (a : List ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |evalList a t| ≤ (absSum a : ℝ) := by
  induction a with
  | nil => simp [evalList, absSum]
  | cons x a ih =>
      have ha : (0 : ℝ) ≤ (absSum a : ℝ) := by exact_mod_cast absSum_nonneg a
      have hsum : absSum (x :: a) = |x| + absSum a := by simp [absSum]
      change |(x : ℝ) + t * evalList a t| ≤ _
      calc
        _ ≤ |(x : ℝ)| + |t * evalList a t| := abs_add_le _ _
        _ = |(x : ℝ)| + t * |evalList a t| := by rw [abs_mul, abs_of_nonneg ht.1]
        _ ≤ |(x : ℝ)| + t * (absSum a : ℝ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left ih ht.1)
        _ ≤ |(x : ℝ)| + (absSum a : ℝ) :=
          add_le_add le_rfl
            (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 ha)
        _ = (absSum (x :: a) : ℝ) := by simp [hsum]

private theorem eval_mulList (a b : List ℤ) (t : ℝ) :
    evalList (mulList a b) t = evalList a t * evalList b t := by
  induction a with
  | nil => simp [mulList, evalList]
  | cons c cs ih =>
      rw [mulList, eval_addList, eval_scaleList]
      simp only [evalList, Int.cast_zero, zero_add, ih]
      ring

private theorem eval_powList (a : List ℤ) (n : ℕ) (t : ℝ) :
    evalList (powList a n) t = evalList a t ^ n := by
  induction n with
  | zero => simp [powList, evalList]
  | succ n ih =>
      rw [powList, eval_mulList, ih, pow_succ]
      ring

/-- The all-integer affine transform is homogeneous of degree List.length.
The extra power of D makes the empty-list and cons induction uniform. -/
private theorem eval_homogeneousAffine (A B D : ℤ) (a : List ℤ)
    (hD : (D : ℝ) ≠ 0) (t : ℝ) :
    evalList (homogeneousAffine A B D a) t =
      (D : ℝ)^a.length * evalList a (((A : ℝ) + (B : ℝ) * t) / (D : ℝ)) := by
  induction a with
  | nil => simp [homogeneousAffine, evalList]
  | cons c cs ih =>
      rw [homogeneousAffine, eval_addList, eval_mulList, ih]
      simp only [evalList, Int.cast_mul, Int.cast_pow, List.length_cons,
        mul_zero, add_zero]
      simp only [pow_succ]
      field_simp [hD]

private theorem eval_bernsteinList (n k : ℕ) (t : ℝ) :
    evalList (bernsteinList n k) t =
      (n.choose k : ℝ) * t^k * (1-t)^(n-k) := by
  have hx : evalList [0, 1] t = t := by simp [evalList]
  have hy : evalList [1, -1] t = 1 - t := by simp [evalList]; ring
  have hfast : Nat.fast_choose n k = n.choose k :=
    (Nat.choose_eq_descFactorial_div_factorial n k).symm
  rw [bernsteinList, eval_scaleList, eval_mulList, eval_powList, eval_powList, hx, hy]
  rw [hfast]
  norm_num only [Int.cast_natCast]
  ring

/-- Reuse the fixed mathlib Bernstein basis positivity theorem itself. -/
private theorem eval_bernsteinList_nonneg (n k : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ evalList (bernsteinList n k) t := by
  have hb := bernstein_nonneg (n := n) (ν := k) (x := ⟨t, ht⟩)
  simpa only [eval_bernsteinList, bernstein_apply] using hb

private theorem eval_bernsteinSum_nonneg (n k : ℕ) (bs : List ℤ)
    (hb : positiveList bs = true) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ evalList (bernsteinSumFrom n k bs) t := by
  revert hb
  induction bs generalizing k with
  | nil => intro hb; simp [bernsteinSumFrom, evalList]
  | cons b bs ih =>
      intro hb
      change (decide (0 < b) && positiveList bs) = true at hb
      have hh := Eq.mp (Bool.and_eq_true_eq_eq_true_and_eq_true _ _) hb
      have hb0 : 0 < b := of_decide_eq_true hh.1
      have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0.le
      rw [bernsteinSumFrom, eval_addList, eval_scaleList]
      exact add_nonneg (mul_nonneg hbR (eval_bernsteinList_nonneg n k ht))
        (ih (k + 1) hh.2)

/-- A computable zero coefficient checker entails equality of the actual
Horner functions. It is not an equality of noncomputable Polynomial values. -/
private theorem eval_eq_of_zero_difference (a b : List ℤ)
    (hzero : absSum (addList a (scaleList (-1) b)) = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : evalList a t = evalList b t := by
  have h := abs_evalList_le (addList a (scaleList (-1) b)) ht
  rw [hzero] at h
  have he : evalList (addList a (scaleList (-1) b)) t = 0 := by
    exact abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg _))
  rw [eval_addList, eval_scaleList] at he
  norm_num only [Int.cast_neg, Int.cast_one] at he
  linarith only [he]

/-- Generic pure-integer List certificate -> actual Horner nonnegativity.
All real algebra and fixed mathlib Bernstein positivity are outside decide. -/
theorem integer_Bernstein_certificate_sound
    (n : ℕ) (M A B D : ℤ) (q bs : List ℤ)
    (hM : 0 < M) (hD : 0 < D) (hb : positiveList bs = true)
    (hid : absSum (addList (scaleList M (homogeneousAffine A B D q))
      (scaleList (-1) (bernsteinSumFrom n 0 bs))) = 0)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 ≤ evalList q (((A : ℝ) + (B : ℝ) * v) / (D : ℝ)) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have he := eval_eq_of_zero_difference
    (scaleList M (homogeneousAffine A B D q)) (bernsteinSumFrom n 0 bs) hid hv
  rw [eval_scaleList, eval_homogeneousAffine A B D q hDR.ne'] at he
  have hn := eval_bernsteinSum_nonneg n 0 bs hb hv
  have hp : 0 ≤ ((M : ℝ) * (D : ℝ)^q.length) *
      evalList q (((A : ℝ) + (B : ℝ) * v) / (D : ℝ)) := by
    rw [mul_assoc]
    exact he.symm ▸ hn
  exact nonneg_of_mul_nonneg_right hp (mul_pos hMR (pow_pos hDR _))

theorem integer_Bernstein_certificate_on_interval
    (n : ℕ) (M A B D : ℤ) (q bs : List ℤ)
    (hM : 0 < M) (hD : 0 < D) (hB : 0 < B)
    (hb : positiveList bs = true)
    (hid : absSum (addList (scaleList M (homogeneousAffine A B D q))
      (scaleList (-1) (bernsteinSumFrom n 0 bs))) = 0)
    {t : ℝ} (ht : (A : ℝ) / D ≤ t ∧ t ≤ ((A : ℝ) + B) / D) :
    0 ≤ evalList q t := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  let v : ℝ := ((D : ℝ) * t - (A : ℝ)) / (B : ℝ)
  have hleft := (div_le_iff₀ hDR).mp ht.1
  have hright := (le_div_iff₀ hDR).mp ht.2
  have hv : v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by nlinarith only [hleft]) hBR.le
    · exact (div_le_one hBR).2 (by nlinarith only [hright])
  have h := integer_Bernstein_certificate_sound n M A B D q bs hM hD hb hid hv
  have he : ((A : ℝ) + (B : ℝ) * v) / (D : ℝ) = t := by
    dsimp [v]
    field_simp [hDR.ne', hBR.ne']
    <;> ring
  simpa only [he] using h

private theorem checked_barrier_nonneg (k : Fin 32) {t : ℝ}
    (ht : (affineA k : ℝ) / affineD k ≤ t ∧
      t ≤ ((affineA k : ℝ) + affineB k) / affineD k) :
    0 ≤ evalList (barrierList (cellIndex k)) t := by
  have h := finiteBernsteinGood k
  exact integer_Bernstein_certificate_on_interval 52 bernsteinMultiplier
    (affineA k) (affineB k) (affineD k) (barrierList (cellIndex k))
    (bernsteinCoefficients k) multiplier_positive h.2.1 h.2.2.1 h.1 h.2.2.2 ht

private theorem eval_barrierList (i : ℕ) (t : ℝ) :
    evalList (barrierList i) t =
      (omegaHalf : ℝ) * ((i : ℝ) + t) - (err i : ℝ) - evalList (row i) t := by
  simp only [barrierList, eval_addList, eval_scaleList, evalList,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_neg, Int.cast_one, mul_zero, add_zero]
  ring

/-- Uniform finite subdivision cover, proved from real order by Nat induction.
No unproved endpoint-union assertion or numerical sampling is used. -/
theorem uniform_cover (n : ℕ) (a h t : ℝ) (hn : 0 < n) (hh : 0 < h)
    (hl : a ≤ t) (hr : t ≤ a + (n : ℝ) * h) :
    ∃ j : ℕ, j < n ∧ a + (j : ℝ) * h ≤ t ∧
      t ≤ a + ((j : ℝ) + 1) * h := by
  clear hh
  revert hn hr
  induction n with
  | zero => intro hn hr; omega
  | succ n ih =>
      intro hn hr
      by_cases hn0 : n = 0
      · subst n
        refine ⟨0, by omega, ?_, ?_⟩
        · simpa using hl
        · simpa using hr
      by_cases hc : t ≤ a + (n : ℝ) * h
      · obtain ⟨j, hj, hjl, hjr⟩ := ih (by omega) hc
        exact ⟨j, by omega, hjl, hjr⟩
      · refine ⟨n, by omega, (lt_of_not_ge hc).le, ?_⟩
        simpa only [Nat.cast_succ] using hr

private theorem barrier_ten_nonneg {t : ℝ}
    (ht : t ∈ Icc (15454 / 20359 : ℝ) 1) :
    0 ≤ evalList (barrierList 10) t := by
  obtain ⟨j, hj, hjl, hjr⟩ := uniform_cover 16 (15454 / 20359 : ℝ)
    (4905 / 325744 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert! ht.2 using 1; norm_num)
  let k : Fin 32 := ⟨j, by omega⟩
  have hk : k.val < 16 := by simpa only [k] using hj
  have hcell : cellIndex k = 10 := by simp only [cellIndex, if_pos hk]
  have hleft : (affineA k : ℝ) / affineD k =
      15454 / 20359 + (j : ℝ) * (4905 / 325744) := by
    simp only [affineA, affineD, if_pos hk, k, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    norm_num
    <;> ring
  have hright : ((affineA k : ℝ) + affineB k) / affineD k =
      15454 / 20359 + ((j : ℝ) + 1) * (4905 / 325744) := by
    simp only [affineA, affineB, affineD, if_pos hk, k, Int.cast_add,
      Int.cast_mul, Int.cast_natCast]
    norm_num
    <;> ring
  have h := checked_barrier_nonneg k
    (by simpa only [hleft, hright] using And.intro hjl hjr)
  simpa only [hcell] using h

private theorem barrier_eleven_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (883 / 10008)) :
    0 ≤ evalList (barrierList 11) t := by
  obtain ⟨j, hj, hjl, hjr⟩ := uniform_cover 16 (0 : ℝ)
    (883 / 160128 : ℝ) t (by norm_num) (by norm_num) ht.1
      (by convert! ht.2 using 1; norm_num)
  let k : Fin 32 := ⟨16 + j, by omega⟩
  have hk : ¬k.val < 16 := by dsimp [k]; omega
  have hjk : k.val - 16 = j := by dsimp [k]; omega
  have hcell : cellIndex k = 11 := by simp only [cellIndex, if_neg hk]
  have hleft : (affineA k : ℝ) / affineD k = (j : ℝ) * (883 / 160128) := by
    simp only [affineA, affineD, if_neg hk, hjk, Int.cast_mul, Int.cast_natCast]
    norm_num
    <;> ring
  have hright : ((affineA k : ℝ) + affineB k) / affineD k =
      ((j : ℝ) + 1) * (883 / 160128) := by
    simp only [affineA, affineB, affineD, if_neg hk, hjk,
      Int.cast_mul, Int.cast_natCast]
    norm_num
    <;> ring
  have h := checked_barrier_nonneg k
    (by simpa only [hleft, hright, zero_add] using And.intro hjl hjr)
  simpa only [hcell] using h

/-- Closed-interval MVT, requiring differentiability only on the interior. -/
private theorem abs_sub_le_of_hasDerivAt_bound
    {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ Ioo a b, |f' x| ≤ C) {x : ℝ} (hx : x ∈ Icc a b) :
    |f x - f a| ≤ C * (x - a) := by
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    exact (hd y hy').differentiableAt.differentiableWithinAt
  have hupper : ∀ y ∈ interior (Icc a b), deriv f y ≤ C := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    rw [(hd y hy').deriv]
    exact (abs_le.mp (hb y hy')).2
  have hlower : ∀ y ∈ interior (Icc a b), -C ≤ deriv f y := by
    intro y hy
    have hy' : y ∈ Ioo a b := by simpa only [interior_Icc] using hy
    rw [(hd y hy').deriv]
    exact (abs_le.mp (hb y hy')).1
  have hu := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hc hdiff hupper a ⟨le_rfl, hab⟩ x hx hx.1
  have hl := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hc hdiff hlower a ⟨le_rfl, hab⟩ x hx hx.1
  exact abs_le.mpr ⟨by linarith, hu⟩

private theorem cell_step
    (V : ℝ → ℝ) (a : ℝ) (ha : 2 ≤ a) (j : ℤ)
    (haj : (j : ℝ) = 2 * (a - 1))
    (u v : List ℤ) (B S : ℝ) (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hc : ContinuousOn V (Icc a (a + 1 / 2)))
    (hd : ∀ s ∈ Ioo a (a + 1 / 2), HasDerivAt V (V (s - 1) / (s - 1)) s)
    (hleft : |V a - evalList u 0| ≤ B)
    (hdelay : ∀ s ∈ Icc (a - 1) (a - 1 / 2),
      |V s - evalList v (2 * (s - (a - 1)))| ≤ B)
    (hresidual : ∀ t ∈ Icc (0 : ℝ) 1, |evalList (residualList j u v) t| ≤ S) :
    ∀ s ∈ Icc a (a + 1 / 2), |V s - evalList u (2 * (s - a))| ≤ 2 * B + S := by
  let f : ℝ → ℝ := fun s => V s - evalList u (2 * (s - a))
  let f' : ℝ → ℝ := fun s =>
    V (s - 1) / (s - 1) - 2 * evalList (derivList u) (2 * (s - a))
  have huc : Continuous (evalList u) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_evalList u t).continuousAt)
  have hpc : Continuous (fun s : ℝ => evalList u (2 * (s - a))) :=
    huc.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hfc : ContinuousOn f (Icc a (a + 1 / 2)) := hc.sub hpc.continuousOn
  have hfd : ∀ s ∈ Ioo a (a + 1 / 2), HasDerivAt f (f' s) s := by
    intro s hs
    have ht : HasDerivAt (fun s : ℝ => 2 * (s - a)) 2 s := by
      simpa using ((hasDerivAt_id s).sub_const a).const_mul 2
    have hp := (hasDerivAt_evalList u (2 * (s - a))).comp s ht
    dsimp only [f, f']
    convert! (hd s hs).sub hp using 1
    ring
  have hfb : ∀ s ∈ Ioo a (a + 1 / 2), |f' s| ≤ B + S := by
    intro s hs
    let t : ℝ := 2 * (s - a)
    have ht : t ∈ Icc (0 : ℝ) 1 := by dsimp [t]; constructor <;> linarith [hs.1, hs.2]
    have hden : 0 < s - 1 := by linarith [hs.1]
    have hden1 : 1 ≤ s - 1 := by linarith [hs.1]
    have hds : s - 1 ∈ Icc (a - 1) (a - 1 / 2) := by
      constructor <;> linarith [hs.1, hs.2]
    have he : |V (s - 1) - evalList v t| ≤ B := by
      convert hdelay (s - 1) hds using 1 <;> dsimp [t] <;> ring
    let R : List ℤ := residualList j u v
    have hR : |evalList R t| ≤ S := hresidual t ht
    have hEval : evalList R t =
        ((j : ℝ) + t) * evalList (derivList u) t - evalList v t :=
      eval_residualList j u v t
    have hIdentity : f' s =
        (V (s - 1) - evalList v t) / (s - 1) - evalList R t / (s - 1) := by
      rw [hEval]
      dsimp [f', t]
      rw [haj]
      field_simp [hden.ne']
      ring
    calc
      |f' s| = |(V (s - 1) - evalList v t) / (s - 1) - evalList R t / (s - 1)| :=
        congrArg abs hIdentity
      _ ≤ |(V (s - 1) - evalList v t) / (s - 1)| + |evalList R t / (s - 1)| :=
        by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le ((V (s - 1) - evalList v t) / (s - 1)) 0
              (evalList R t / (s - 1))
      _ = (|V (s - 1) - evalList v t| + |evalList R t|) / (s - 1) := by
        simp only [abs_div, abs_of_pos hden]
        ring
      _ ≤ (B + S) / (s - 1) :=
        div_le_div_of_nonneg_right (add_le_add he hR) hden.le
      _ ≤ B + S := div_le_self (add_nonneg hB hS) hden1
  intro s hs
  have hmv := abs_sub_le_of_hasDerivAt_bound (by linarith : a ≤ a + 1 / 2)
    hfc hfd hfb hs
  have hfa : |f a| ≤ B := by simpa only [f, sub_self, mul_zero] using hleft
  change |f s| ≤ _
  calc
    |f s| ≤ |f s - f a| + |f a| := by
      simpa only [sub_add_cancel] using abs_add_le (f s - f a) (f a)
    _ ≤ (B + S) * (s - a) + B := add_le_add hmv hfa
    _ ≤ (B + S) * (1 / 2) + B := by
      have hlen : s - a ≤ (1 / 2 : ℝ) := by linarith only [hs.2]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlen (add_nonneg hB hS)) le_rfl
    _ ≤ 2 * B + S := by linarith

def scaledSource (s : ℝ) : ℝ := (scale : ℝ) * (s * LiLiuPrereqBuchstab.buchstab s)

private theorem scaled_history {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    scaledSource s = (scale : ℝ) := by
  have hs0 : s ≠ 0 := ne_of_gt (by linarith : 0 < s)
  rw [scaledSource, LiLiuPrereqBuchstab.buchstab_eq_one_div hs1 hs2]
  field_simp [hs0]

private theorem scaled_continuous : ContinuousOn scaledSource (Icc (2 : ℝ) 6) := by
  exact (continuous_const.mul
    (continuous_id.mul LiLiuPrereqBuchstab.continuous_buchstab)).continuousOn

private theorem scaled_hasDeriv {s : ℝ} (hs : 2 < s) :
    HasDerivAt scaledSource (scaledSource (s - 1) / (s - 1)) s := by
  have h := (LiLiuPrereqBuchstab.hasDerivAt_mul_buchstab hs).const_mul (scale : ℝ)
  have he : (scale : ℝ) * LiLiuPrereqBuchstab.buchstab (s - 1) =
      scaledSource (s - 1) / (s - 1) := by
    dsimp only [scaledSource]
    rw [mul_div_assoc,
      mul_div_cancel_left₀ _ (ne_of_gt (by linarith : 0 < s - 1))]
  convert! h.congr_deriv he using 1

def left (i : ℕ) : ℝ := (i : ℝ) / 2
def right (i : ℕ) : ℝ := left i + 1 / 2
def value (i : ℕ) (s : ℝ) : ℝ := evalList (row i) (2 * (s - left i))

private theorem finite_good_at (i : ℕ) (hi4 : 4 ≤ i) (hi11 : i ≤ 11) :
    startValue i = endValue (i - 1) ∧
      absSum (residualList ((i - 2 : ℕ) : ℤ) (row i) (row (i - 2))) ≤ residualBound ∧
      err (i - 2) ≤ err (i - 1) ∧
      err i = 2 * err (i - 1) + residualBound := by
  let k : Fin 8 := ⟨i - 4, by omega⟩
  have h4 : k.val + 4 = i := by dsimp [k]; omega
  have h3 : k.val + 3 = i - 1 := by dsimp [k]; omega
  have h2 : k.val + 2 = i - 2 := by dsimp [k]; omega
  simpa only [h4, h3, h2] using finiteGood k

private theorem finite_nonneg_at (i : ℕ) (hi2 : 2 ≤ i) (hi11 : i ≤ 11) :
    0 ≤ err i := by
  let k : Fin 10 := ⟨i - 2, by omega⟩
  have h2 : k.val + 2 = i := by dsimp [k]; omega
  simpa only [h2] using finiteNonneg k

private theorem initial_cell (i : ℕ) (hi : i = 2 ∨ i = 3) :
    ∀ s ∈ Icc (left i) (right i),
      |scaledSource s - value i s| ≤ (err i : ℝ) := by
  rcases hi with rfl | rfl
  · intro s hs
    have hVs := scaled_history (s := s)
      (by norm_num [left, right] at hs; linarith [hs.1])
      (by norm_num [left, right] at hs; linarith [hs.2])
    simp [value, row_two, evalList, hVs, err]
  · intro s hs
    have hVs := scaled_history (s := s)
      (by norm_num [left, right] at hs; linarith [hs.1])
      (by norm_num [left, right] at hs; linarith [hs.2])
    simp [value, row_three, evalList, hVs, err]

theorem all_cells (i : ℕ) : i ≤ 11 → 2 ≤ i →
    ∀ s ∈ Icc (left i) (right i),
      |scaledSource s - value i s| ≤ (err i : ℝ) := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi11 hi2
      by_cases hi4 : i < 4
      · exact initial_cell i (by omega)
      have hi4' : 4 ≤ i := by omega
      have hcert := finite_good_at i hi4' hi11
      have hprev := ih (i - 1) (by omega) (by omega) (by omega)
      have hdelay := ih (i - 2) (by omega) (by omega) (by omega)
      have hcast1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ i)]
        norm_num
      have hcast2 : ((i - 2 : ℕ) : ℝ) = (i : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ i)]
        norm_num
      have hleft1 : left (i - 1) = left i - 1 / 2 := by
        dsimp [left]; rw [hcast1]; ring
      have hleft2 : left (i - 2) = left i - 1 := by
        dsimp [left]; rw [hcast2]; ring
      have hB : (0 : ℝ) ≤ (err (i - 1) : ℝ) := by
        exact_mod_cast finite_nonneg_at (i - 1) (by omega) (by omega)
      have hS : (0 : ℝ) ≤ (residualBound : ℝ) := by norm_num [residualBound]
      have hc : ContinuousOn scaledSource (Icc (left i) (left i + 1 / 2)) := by
        apply scaled_continuous.mono
        intro s hs
        have hiR : (i : ℝ) ≤ 11 := by exact_mod_cast hi11
        have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
        dsimp [left] at hs
        constructor <;> linarith [hs.1, hs.2]
      have hd : ∀ s ∈ Ioo (left i) (left i + 1 / 2),
          HasDerivAt scaledSource (scaledSource (s - 1) / (s - 1)) s := by
        intro s hs
        have hs2 : 2 < s := by
          have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
          dsimp [left] at hs
          linarith [hs.1]
        exact scaled_hasDeriv hs2
      have hjoin : evalList (row i) 0 = evalList (row (i - 1)) 1 := by
        rw [eval_zero, eval_one]
        exact_mod_cast hcert.1
      have hl : |scaledSource (left i) - evalList (row i) 0| ≤
          (err (i - 1) : ℝ) := by
        have hmem : left i ∈ Icc (left (i - 1)) (right (i - 1)) := by
          rw [right, hleft1]
          constructor <;> linarith
        have h := hprev (left i) hmem
        simpa only [value, hleft1, show 2 * (left i - (left i - 1 / 2)) = 1 by ring,
          ← hjoin] using h
      have hdel : ∀ s ∈ Icc (left i - 1) (left i - 1 / 2),
          |scaledSource s - evalList (row (i - 2)) (2 * (s - (left i - 1)))| ≤
            (err (i - 1) : ℝ) := by
        intro s hs
        have hmem : s ∈ Icc (left (i - 2)) (right (i - 2)) := by
          rw [right, hleft2]
          constructor <;> linarith [hs.1, hs.2]
        have h := hdelay s hmem
        have hmono : (err (i - 2) : ℝ) ≤ (err (i - 1) : ℝ) := by
          exact_mod_cast hcert.2.2.1
        simpa only [value, hleft2] using h.trans hmono
      have hr : ∀ t ∈ Icc (0 : ℝ) 1,
          |evalList (residualList ((i - 2 : ℕ) : ℤ) (row i) (row (i - 2))) t| ≤
            (residualBound : ℝ) := by
        intro t ht
        exact (abs_evalList_le _ ht).trans (by exact_mod_cast hcert.2.1)
      have hstep := cell_step scaledSource (left i)
        (by
          have hi4R : (4 : ℝ) ≤ i := by exact_mod_cast hi4'
          dsimp [left]; linarith)
        ((i - 2 : ℕ) : ℤ)
        (by simp only [Int.cast_natCast, hcast2]; dsimp [left]; ring)
        (row i) (row (i - 2)) (err (i - 1) : ℝ) (residualBound : ℝ)
        hB hS hc hd hl hdel hr
      intro s hs
      have h := hstep s hs
      change |scaledSource s - value i s| ≤ _ at h
      have he : (err i : ℝ) = 2 * (err (i - 1) : ℝ) + (residualBound : ℝ) := by
        exact_mod_cast hcert.2.2.2
      simpa only [he] using h

private theorem scaled_le_of_barrier (i : ℕ) (hi2 : 2 ≤ i) (hi11 : i ≤ 11)
    {s : ℝ} (hs : s ∈ Icc (left i) (right i))
    (hb : 0 ≤ evalList (barrierList i) (2 * (s - left i))) :
    scaledSource s ≤ (omegaNumerator : ℝ) * s := by
  have he := all_cells i hi11 hi2 s hs
  have heu := (abs_le.mp he).2
  rw [eval_barrierList] at hb
  have hhalf : (omegaNumerator : ℝ) = 2 * (omegaHalf : ℝ) := by
    exact_mod_cast omega_halves
  have ht : (i : ℝ) + 2 * (s - left i) = 2 * s := by dsimp [left]; ring
  rw [ht] at hb
  dsimp only [value] at heu
  rw [hhalf]
  nlinarith only [hb, heu]

/-- One specific original subinterval, with a complete by proof.
Its certificate is the first of the32 finite integer certificates. -/
theorem first_original_subinterval_scaled_enclosure {s : ℝ}
    (hs : s ∈ Icc (109522 / 20359 : ℝ) (3509609 / 651488)) :
    scaledSource s ≤ (omegaNumerator : ℝ) * s := by
  have hp := firstBernsteinGood
  have ht : (affineA (0 : Fin 32) : ℝ) / affineD (0 : Fin 32) ≤
        2 * (s - left 10) ∧
      2 * (s - left 10) ≤
        ((affineA (0 : Fin 32) : ℝ) + affineB (0 : Fin 32)) / affineD (0 : Fin 32) := by
    norm_num [affineA, affineB, affineD, left]
    constructor <;> linarith [hs.1, hs.2]
  have hbar := integer_Bernstein_certificate_on_interval 52 bernsteinMultiplier
    (affineA (0 : Fin 32)) (affineB (0 : Fin 32)) (affineD (0 : Fin 32))
    (barrierList (cellIndex (0 : Fin 32))) (bernsteinCoefficients (0 : Fin 32))
    multiplier_positive hp.2.1 hp.2.2.1 hp.1 hp.2.2.2 ht
  have hcell : s ∈ Icc (left 10) (right 10) := by
    norm_num [left, right]
    constructor <;> linarith [hs.1, hs.2]
  exact scaled_le_of_barrier 10 (by norm_num) (by norm_num) hcell
    (by simpa only [cellIndex, Fin.val_zero, if_pos (by norm_num : 0 < 16)] using hbar)

theorem scaled_original_parent_enclosure {s : ℝ}
    (hs : s ∈ Icc (109522 / 20359 : ℝ) (110971 / 20016)) :
    scaledSource s ≤ (omegaNumerator : ℝ) * s := by
  by_cases hmid : s ≤ (11 : ℝ) / 2
  · have hc : s ∈ Icc (left 10) (right 10) := by
      norm_num [left, right]
      constructor <;> linarith [hs.1, hmid]
    have ht : 2 * (s - left 10) ∈ Icc (15454 / 20359 : ℝ) 1 := by
      norm_num [left]
      constructor <;> linarith [hs.1, hmid]
    exact scaled_le_of_barrier 10 (by norm_num) (by norm_num) hc
      (barrier_ten_nonneg ht)
  · have hc : s ∈ Icc (left 11) (right 11) := by
      norm_num [left, right]
      constructor <;> linarith [hs.2]
    have ht : 2 * (s - left 11) ∈ Icc (0 : ℝ) (883 / 10008) := by
      norm_num [left]
      constructor <;> linarith [hs.2]
    exact scaled_le_of_barrier 11 (by norm_num) (by norm_num) hc
      (barrier_eleven_nonneg ht)

/-- ACTUAL Buchstab on the full original closed support.  No enclosure,
saved-mass inequality or final density target is a hypothesis. -/
theorem actual_buchstab_original_parent_enclosure :
    ∀ s ∈ Icc (109522 / 20359 : ℝ) (110971 / 20016),
      LiLiuPrereqBuchstab.buchstab s ≤
        (678762786914544909109774 / 2^80 : ℝ) := by
  intro s hs
  have hp : 0 < s := by linarith [hs.1]
  have hQ : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_positive
  have h := scaled_original_parent_enclosure hs
  have hout : LiLiuPrereqBuchstab.buchstab s ≤ (omegaNumerator : ℝ) / scale := by
    apply (mul_le_mul_iff_left₀ (mul_pos hQ hp)).mp
    calc
      (scale : ℝ) * s * LiLiuPrereqBuchstab.buchstab s = scaledSource s := by
        dsimp [scaledSource]
        ring
      _ ≤ (omegaNumerator : ℝ) * s := h
      _ = ((scale : ℝ) * s) * ((omegaNumerator : ℝ) / scale) := by
        field_simp [hQ.ne']
        <;> ring
  convert hout using 1 <;> norm_num [omegaNumerator, scale]


theorem first_original_subinterval_actual_omega {s : ℝ}
    (hs : s ∈ Icc (109522 / 20359 : ℝ) (3509609 / 651488)) :
    LiLiuPrereqBuchstab.buchstab s ≤
      (678762786914544909109774 / 2^80 : ℝ) := by
  have hp : 0 < s := by linarith [hs.1]
  have hQ : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast scale_positive
  have h := first_original_subinterval_scaled_enclosure hs
  have hout : LiLiuPrereqBuchstab.buchstab s ≤ (omegaNumerator : ℝ) / scale := by
    apply (mul_le_mul_iff_left₀ (mul_pos hQ hp)).mp
    calc
      (scale : ℝ) * s * LiLiuPrereqBuchstab.buchstab s = scaledSource s := by
        dsimp [scaledSource]
        ring
      _ ≤ (omegaNumerator : ℝ) * s := h
      _ = ((scale : ℝ) * s) * ((omegaNumerator : ℝ) / scale) := by
        field_simp [hQ.ne']
        <;> ring
  convert hout using 1 <;> norm_num [omegaNumerator, scale]

end
end ImbalancedChen.Certificates.SavedParent394700ActualBuchstabSegmentedSourceOnly

/- The retained unconditional actual reference-mass and original-slope
supplier follows. Its former conditional omega adapter is replaced below
by the closed actual-Buchstab theorem in this COMPLETE bundle. -/

namespace ImbalancedChen.Certificates.SavedParent394700SegmentedSourceOnly
open ImbalancedChen.Certificates.SavedParent394700SourceOnly

open MeasureTheory Set
open scoped Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def logXCertificate : RationalLogCertificate where
  argument := 888 / 881
  terms := 20
  lower := 41092445127896660640210383700713 / 2^112
  upper := 41092445127896660640210383700714 / 2^112

def logYCertificate : RationalLogCertificate where
  argument := 36480 / 36137
  terms := 20
  lower := 49051078050933585981984794825046 / 2^112
  upper := 49051078050933585981984794825047 / 2^112

def logBCertificate : RationalLogCertificate where
  argument := 20359 / 20016
  terms := 20
  lower := 88222943350053589745130122942804 / 2^112
  upper := 88222943350053589745130122942805 / 2^112

theorem logXCertificate_checked : logXCertificate.check = true := by
  norm_num [logXCertificate, RationalLogCertificate.check,
    RationalLogCertificate.Valid, logSeriesLower, logSeriesUpper,
    logParameter, Finset.sum_range_succ]

theorem logYCertificate_checked : logYCertificate.check = true := by
  norm_num [logYCertificate, RationalLogCertificate.check,
    RationalLogCertificate.Valid, logSeriesLower, logSeriesUpper,
    logParameter, Finset.sum_range_succ]

theorem logBCertificate_checked : logBCertificate.check = true := by
  norm_num [logBCertificate, RationalLogCertificate.check,
    RationalLogCertificate.Valid, logSeriesLower, logSeriesUpper,
    logParameter, Finset.sum_range_succ]

/-- The coefficient 80 cancels the existing paired integral's 1/80.
This is a reference-mass certificate, with a deliberately loose upper bound. -/
def referenceCertificate : PairedIntegralCertificate where
  K := 80
  a := 417 / 5000
  tl := 881 / 4000
  tr := 111 / 500
  ul := 36137 / 240000
  ur := 19 / 125
  Z := 20359 / 240000
  logT := logXCertificate
  logU := logYCertificate
  logZ := logBCertificate
  lower := 639725377308353184579192771110087 /
    5000000000000000000000000000000000000000
  upper := 1

theorem referenceCertificate_checked : referenceCertificate.check = true := by
  norm_num [referenceCertificate, PairedIntegralCertificate.check,
    PairedIntegralCertificate.Valid, PairedIntegralCertificate.productLower,
    PairedIntegralCertificate.productUpper, PairedIntegralCertificate.bracketLower,
    PairedIntegralCertificate.bracketUpper, logXCertificate, logYCertificate,
    logBCertificate, RationalLogCertificate.check, RationalLogCertificate.Valid,
    logSeriesLower, logSeriesUpper, logParameter, Finset.sum_range_succ]

noncomputable section

def a : ℝ := 417 / 5000
def b : ℝ := 20359 / 240000
def tl : ℝ := 881 / 4000
def tr : ℝ := 111 / 500
def ul : ℝ := 36137 / 240000
def ur : ℝ := 19 / 125

def K0 : ℝ := 67619 / 10000
def K : ℝ := 8452171 / 1250000
def C : ℝ := 70893 / 125000
def savedSaving : ℝ := 5945529223463611 / 2^80
def omegaB : ℝ := 678762786914544909109774 / 2^80

/-- Exact original rational volume proxy, including the z/w tie divisor 2!. -/
def zProxy : ℝ := 35309406125 / 284751414104646576

/-- Outward lower endpoint for the actual logarithmic reference mass. -/
def zStrong : ℝ := 639725377308353184579192771110087 /
  5000000000000000000000000000000000000000

def originalFloor : ℕ := 8414002975048

/-- The frozen ORIGINAL slope is 10000*d/Q.  It is not replaced by A/K0. -/
def savedSlope : ℝ := 10000 * (originalFloor : ℝ) / 2^80

/-- Actual reference mass Z_B = integral_B dmu4/z, on a<w<z<b. -/
def referenceMass : ℝ := pairedLocalIntegral 80 a tl tr ul ur b

theorem referenceMass_eq_literal :
    referenceMass = ∫ t in tl..tr, ∫ u in ul..ur,
      ∫ z in a..b, ∫ w in a..z, 1 / (t * u * z^2 * w) := by
  simpa [referenceMass] using
    (pairedLocalIntegral_eq_literal (80 : ℝ) a tl tr ul ur b)

theorem referenceMass_eq_logs :
    referenceMass = Real.log (tr / tl) * Real.log (ur / ul) *
      (1 / a - (1 + Real.log (b / a)) / b) := by
  have h := pairedLocalIntegral_eq (80 : ℝ)
    (a := a) (tl := tl) (tr := tr) (ul := ul) (ur := ur) (Z := b)
    (by norm_num [a]) (by norm_num [a, b])
    (by norm_num [tl]) (by norm_num [tr])
    (by norm_num [ul]) (by norm_num [ur])
  simpa [referenceMass] using h

/-- This is about the ACTUAL nested Lebesgue integral, by the existing
analytic soundness theorem, not a stored JSON number interpreted as Z. -/
theorem referenceMass_bounds : zStrong ≤ referenceMass ∧ referenceMass ≤ 1 := by
  have h := PairedIntegralCertificate.check_sound referenceCertificate
    referenceCertificate_checked
  simpa [referenceCertificate, zStrong, referenceMass, a, b, tl, tr, ul, ur] using h

theorem referenceMass_pos : 0 < referenceMass := by
  exact lt_of_lt_of_le (by norm_num [zStrong]) referenceMass_bounds.1

theorem zProxy_le_referenceMass : zProxy ≤ referenceMass := by
  exact (show zProxy ≤ zStrong by norm_num [zProxy, zStrong]).trans
    referenceMass_bounds.1

/-- Purely rational reproduction of the original saved floor.
The old route used deltaK=1/10000; division by that delta gives savedSlope. -/
theorem originalFloor_licensed :
    (originalFloor : ℝ) ≤
        2^80 * (K0 * C * zProxy - savedSaving) / 67619 ∧
      2^80 * (K0 * C * zProxy - savedSaving) / 67619 <
        (originalFloor : ℝ) + 1 := by
  norm_num [originalFloor, K0, C, zProxy, savedSaving]

theorem savedSlope_proxy_bounds :
    0 ≤ savedSlope ∧ savedSlope ≤ C * zProxy - savedSaving / K0 := by
  norm_num [savedSlope, originalFloor, K0, C, zProxy, savedSaving]

theorem savedSaving_omega_margin :
    savedSaving ≤ K0 * (C - omegaB) * zStrong := by
  norm_num [savedSaving, K0, C, omegaB, zStrong]

theorem currentK_bounds : 0 < K ∧ K ≤ K0 := by
  norm_num [K, K0]

/-- Actual old saved density mass, with Z_B still a genuine integral. -/
def anchorMass : ℝ := K0 * C * referenceMass - savedSaving

/-- Current fixed-slope saved density mass A'_B. -/
def currentMass : ℝ := anchorMass - (K0 - K) * savedSlope

/-- The literal saved-parent density from the original completion note. -/
def savedDensity (z : ℝ) : ℝ := currentMass / (referenceMass * z)

theorem anchorMass_div_anchor :
    anchorMass / K0 = C * referenceMass - savedSaving / K0 := by
  unfold anchorMass
  field_simp [show K0 ≠ 0 by norm_num [K0] ]
  <;> ring

/-- The original frozen slope is licensed by the ACTUAL saved density mass. -/
theorem savedSlope_le_actual_anchor : savedSlope ≤ anchorMass / K0 := by
  rw [anchorMass_div_anchor]
  exact savedSlope_proxy_bounds.2.trans
    (sub_le_sub_right (mul_le_mul_of_nonneg_left zProxy_le_referenceMass
      (by norm_num [C])) (savedSaving / K0))

/-- First original §5 inequality.  No saved-floor semantic target is assumed. -/
theorem actual_anchor_ge_omega : K0 * omegaB * referenceMass ≤ anchorMass := by
  have hc : 0 ≤ K0 * (C - omegaB) := by norm_num [K0, C, omegaB]
  have hg : savedSaving ≤ K0 * (C - omegaB) * referenceMass :=
    savedSaving_omega_margin.trans
      (mul_le_mul_of_nonneg_left referenceMass_bounds.1 hc)
  unfold anchorMass
  nlinarith only [hg]

theorem actual_anchor_nonneg : 0 ≤ anchorMass := by
  have hk : 0 ≤ K0 := by norm_num [K0]
  have hw : 0 ≤ omegaB := by norm_num [omegaB]
  exact (mul_nonneg (mul_nonneg hk hw) referenceMass_pos.le).trans
    actual_anchor_ge_omega

/-- Second original §5 inequality, using the ORIGINAL saved slope. -/
theorem actual_current_ge_scaled_anchor :
    (K / K0) * anchorMass ≤ currentMass := by
  have hprod : 0 ≤ (K0 - K) * (anchorMass / K0 - savedSlope) :=
    mul_nonneg (sub_nonneg.mpr currentK_bounds.2)
      (sub_nonneg.mpr savedSlope_le_actual_anchor)
  have hid : currentMass - (K / K0) * anchorMass =
      (K0 - K) * (anchorMass / K0 - savedSlope) := by
    unfold currentMass
    field_simp [show K0 ≠ 0 by norm_num [K0] ]
    <;> ring
  linarith only [hprod, hid]

theorem actual_current_ge_omega : K * omegaB * referenceMass ≤ currentMass := by
  have hc : 0 ≤ K / K0 := by norm_num [K, K0]
  calc
    K * omegaB * referenceMass =
        (K / K0) * (K0 * omegaB * referenceMass) := by
      field_simp [show K0 ≠ 0 by norm_num [K0] ]
      <;> ring
    _ ≤ (K / K0) * anchorMass :=
      mul_le_mul_of_nonneg_left actual_anchor_ge_omega hc
    _ ≤ currentMass := actual_current_ge_scaled_anchor

/-- The concrete saved-parent density has a proved rational omega barrier.
The reference mass is strictly positive; no division by a zero mass occurs. -/
theorem savedDensity_ge_omegaB {z : ℝ} (hz : 0 < z) :
    K * omegaB / z ≤ savedDensity z := by
  unfold savedDensity
  apply (le_div_iff₀ (mul_pos referenceMass_pos hz)).2
  have hid : K * omegaB / z * (referenceMass * z) =
      K * omegaB * referenceMass := by
    field_simp [hz.ne']
  rw [hid]
  exact actual_current_ge_omega

/-- Closed parent support.  The original open ordered parent differs only
on its endpoint/ordering walls, of Lebesgue measure zero. -/
def parentClosure : Set (Fin 4 → ℝ) := {p |
  tl ≤ p 0 ∧ p 0 ≤ tr ∧ ul ≤ p 1 ∧ p 1 ≤ ur ∧
  a ≤ p 3 ∧ p 3 ≤ p 2 ∧ p 2 ≤ b}

def parentOpen : Set (Fin 4 → ℝ) := {p |
  tl < p 0 ∧ p 0 < tr ∧ ul < p 1 ∧ p 1 < ur ∧
  a < p 3 ∧ p 3 < p 2 ∧ p 2 < b}

theorem parentOpen_subset_closure : parentOpen ⊆ parentClosure := by
  intro p hp
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  exact ⟨h0.le, h1.le, h2.le, h3.le, h4.le, h5.le, h6.le⟩

theorem parent_coordinates_pos {p : Fin 4 → ℝ} (hp : p ∈ parentClosure) :
    0 < p 0 ∧ 0 < p 1 ∧ 0 < p 2 ∧ 0 < p 3 := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have ha : 0 < a := by norm_num [a]
  exact ⟨(show 0 < tl by norm_num [tl]).trans_le h0,
    (show 0 < ul by norm_num [ul]).trans_le h2,
    ha.trans_le (h4.trans h5), ha.trans_le h4⟩

def argument (p : Fin 4 → ℝ) : ℝ := (1 - p 0 - p 1 - p 2 - p 3) / p 2
def sMin : ℝ := 109522 / 20359
def sMax : ℝ := 110971 / 20016

/-- Includes every closed endpoint and the z=w ordering wall. -/
theorem parent_argument_range {p : Fin 4 → ℝ} (hp : p ∈ parentClosure) :
    argument p ∈ Set.Icc sMin sMax := by
  have hz := (parent_coordinates_pos hp).2.2.1
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  have hza : a ≤ p 2 := h4.trans h5
  have hwb : p 3 ≤ b := h5.trans h6
  constructor
  · unfold argument
    apply (le_div_iff₀ hz).2
    norm_num [sMin, tl, tr, ul, ur, a, b] at *
    linarith only [h1, h3, h6, hwb]
  · unfold argument
    apply (div_le_iff₀ hz).2
    norm_num [sMax, tl, tr, ul, ur, a, b] at *
    linarith only [h0, h2, hza, h4]

/-- Literal Chen-quarter saved density, with the ACTUAL reference mass. -/
def savedChenDensity (p : Fin 4 → ℝ) : ℝ :=
  savedDensity (p 2) * (1 / (4 * p 0 * p 1 * p 2 * p 3))

theorem actual_omega_enclosure :
    ∀ s ∈ Set.Icc sMin sMax, LiLiuPrereqBuchstab.buchstab s ≤ omegaB := by
  simpa [sMin, sMax, omegaB] using
    SavedParent394700ActualBuchstabSegmentedSourceOnly.actual_buchstab_original_parent_enclosure

/-- Closed real saved-parent density licence. No actual-omega, A/A' or
integral-bound target occurs among the hypotheses. -/
theorem original_savedDensity_ge_actual_on_parent
    {p : Fin 4 → ℝ} (hp : p ∈ parentClosure) :
    K * LiLiuPrereqBuchstab.buchstab (argument p) / p 2 ≤ savedDensity (p 2) := by
  have hz := (parent_coordinates_pos hp).2.2.1
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (actual_omega_enclosure _ (parent_argument_range hp)) currentK_bounds.1.le)
    hz.le).trans (savedDensity_ge_omegaB hz)

/-- Closed literal Chen-quarter kernel licence on this one parent,
also valid when restricted to its intersection with the actual crop. -/
theorem original_savedChenDensity_ge_actual_kernel
    {p : Fin 4 → ℝ} (hp : p ∈ parentClosure) :
    (K / 4) * LiLiuPrereqBuchstab.buchstab (argument p) *
      pairedFibreKernel (p 0) (p 1) (p 2) (p 3) ≤ savedChenDensity p := by
  rcases parent_coordinates_pos hp with ⟨ht, hu, hz, hw⟩
  have hf : 0 ≤ 1 / (4 * p 0 * p 1 * p 2 * p 3) := by positivity
  calc
    (K / 4) * LiLiuPrereqBuchstab.buchstab (argument p) *
        pairedFibreKernel (p 0) (p 1) (p 2) (p 3) =
        (K * LiLiuPrereqBuchstab.buchstab (argument p) / p 2) *
          (1 / (4 * p 0 * p 1 * p 2 * p 3)) := by
      rw [pairedFibreKernel_eq]
      field_simp [ht.ne', hu.ne', hz.ne', hw.ne']
    _ ≤ savedDensity (p 2) * (1 / (4 * p 0 * p 1 * p 2 * p 3)) :=
      mul_le_mul_of_nonneg_right (original_savedDensity_ge_actual_on_parent hp) hf
    _ = savedChenDensity p := rfl

end
end ImbalancedChen.Certificates.SavedParent394700SegmentedSourceOnly
