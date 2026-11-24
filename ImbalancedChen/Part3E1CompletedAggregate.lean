import ImbalancedChen.Part3DeterminantGCD
import ImbalancedChen.Part3SmoothReciprocalWeil
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Completion of the E1 Cauchy mass

The factorwise primitive gates stay in the actual sum, and are removed
from the upper bounds after eliminating the residue from the gcd.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators SchwartzMap FourierTransform

/-- The signed frequency box contains exactly `H` positive and `H` negative integers. -/
theorem card_e1NonzeroFrequencies (H : ℕ) : (e1NonzeroFrequencies H).card = 2 * H := by
  have hzero : (0 : ℤ) ∈ Icc (-(H : ℤ)) (H : ℤ) := mem_Icc.mpr ⟨by omega, by omega⟩
  rw [e1NonzeroFrequencies, card_erase_of_mem hzero, Int.card_Icc]
  omega

/-- The dyadic nonzero determinant gcd sum, with the physical modulus on the outside. -/
theorem e1DyadicNonzeroGcd_sum_le (Q R H T J : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (hT : ∀ d ∈ Ioc 0 (2 * R), d.divisors.card ≤ T)
    (hJ : ∀ j : ℤ, j ≠ 0 → j.natAbs ≤ 2 * H * (2 * R) → j.natAbs.divisors.card ≤ J) :
    (∑ q ∈ Icc Q (2 * Q), ∑ r ∈ Icc R (2 * R), ∑ r' ∈ Icc R (2 * R),
      ∑ h ∈ e1NonzeroFrequencies H, ∑ h' ∈ e1NonzeroFrequencies H,
        if e1Determinant h h' r r' = 0 then 0 else
          Int.gcd (e1Determinant h h' r r') ((q * r * r' : ℕ) : ℤ)) ≤
      64 * Q * J * (H * T) ^ 2 * R ^ 3 := by
  let D := Icc Q (2 * Q)
  let S := Icc R (2 * R)
  let F := e1NonzeroFrequencies H
  let j (r r' : ℕ) (h h' : ℤ) := e1Determinant h h' r r'
  let g (q r r' : ℕ) (h h' : ℤ) := Int.gcd (j r r' h h') ((q * r * r' : ℕ) : ℤ)
  have hD : D ⊆ Ioc 0 (2 * Q) := fun _ hq =>
    mem_Ioc.mpr ⟨hQ.trans_le (mem_Icc.mp hq).1, (mem_Icc.mp hq).2⟩
  have hS : S ⊆ Ioc 0 (2 * R) := fun _ hr =>
    mem_Ioc.mpr ⟨hR.trans_le (mem_Icc.mp hr).1, (mem_Icc.mp hr).2⟩
  have hqSum (r r' : ℕ) (h h' : ℤ) :
      (if j r r' h h' = 0 then 0 else ∑ q ∈ D, g q r r' h h') ≤
        (if j r r' h h' = 0 then 0 else ∑ q ∈ Ioc 0 (2 * Q), g q r r' h h') := by
    by_cases hj : j r r' h h' = 0
    · simp [hj]
    · rw [if_neg hj, if_neg hj]
      exact sum_le_sum_of_subset_of_nonneg hD (fun _ _ _ => Nat.zero_le _)
  change (∑ q ∈ D, ∑ r ∈ S, ∑ r' ∈ S, ∑ h ∈ F, ∑ h' ∈ F,
    if j r r' h h' = 0 then 0 else g q r r' h h') ≤ _
  calc
    _ = ∑ r ∈ S, ∑ r' ∈ S, ∑ h ∈ F, ∑ h' ∈ F,
          if j r r' h h' = 0 then 0 else ∑ q ∈ D, g q r r' h h' := by
      simp_rw [sum_comm (s := D) (t := S), sum_comm (s := D) (t := F)]
      refine sum_congr rfl (fun r _ => sum_congr rfl (fun r' _ =>
        sum_congr rfl (fun h _ => sum_congr rfl (fun h' _ => ?_))))
      by_cases hj : j r r' h h' = 0 <;> simp [hj]
    _ ≤ ∑ r ∈ S, ∑ r' ∈ S, ∑ h ∈ F, ∑ h' ∈ F,
          if j r r' h h' = 0 then 0 else ∑ q ∈ Ioc 0 (2 * Q), g q r r' h h' :=
      sum_le_sum fun r _ => sum_le_sum fun r' _ =>
        sum_le_sum fun h _ => sum_le_sum fun h' _ => hqSum r r' h h'
    _ ≤ ∑ r ∈ S, ∑ r' ∈ Ioc 0 (2 * R), ∑ h ∈ F, ∑ h' ∈ F,
          if j r r' h h' = 0 then 0 else ∑ q ∈ Ioc 0 (2 * Q), g q r r' h h' :=
      sum_le_sum fun _ _ => sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
    _ ≤ ∑ r ∈ Ioc 0 (2 * R), ∑ r' ∈ Ioc 0 (2 * R), ∑ h ∈ F, ∑ h' ∈ F,
          if j r r' h h' = 0 then 0 else ∑ q ∈ Ioc 0 (2 * Q), g q r r' h h' :=
      sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
    _ ≤ (2 * Q) * J * (2 * H * T) ^ 2 * (2 * R) ^ 3 :=
      sum_e1NonzeroDeterminant_gcd_le (2 * Q) (2 * R) H T J hT hJ
    _ = _ := by ring

/-- The completed reciprocal sum at the modulus of one Cauchy pair. -/
def e1CompletedSmoothTerm (q r r' : ℕ) (h h' a : ℤ) (N : ℝ)
    (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ) : ℂ :=
  if hm : 0 < q * r * r' then
    @smoothReciprocalSum (q * r * r') ⟨hm.ne'⟩ (a * e1Determinant h h' r r') N w S
  else 0

/-- The actual Cauchy mass, with the original factorwise primitive gates. -/
def e1CompletedCauchyMass (Q R H : ℕ) (a : ℤ) (N : ℝ) (w : 𝓢(ℝ, ℂ))
    (S : Finset ℕ) : ℝ :=
  ∑ q ∈ (Icc Q (2 * Q)).filter (fun n => n.Coprime a.natAbs),
    ∑ r ∈ (Icc R (2 * R)).filter (fun n => n.Coprime a.natAbs),
      ∑ r' ∈ (Icc R (2 * R)).filter (fun n => n.Coprime a.natAbs),
        ∑ h ∈ e1NonzeroFrequencies H, ∑ h' ∈ e1NonzeroFrequencies H,
          ‖e1CompletedSmoothTerm q r r' h h' a N w S‖

private theorem e1Term_norm_le_sampleMass (q r r' : ℕ) (h h' a : ℤ) (N : ℝ)
    (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ) :
    ‖e1CompletedSmoothTerm q r r' h h' a N w S‖ ≤ ∑ n ∈ S, ‖w ((n : ℝ) / N)‖ := by
  unfold e1CompletedSmoothTerm
  split
  · rename_i hm
    let _ : NeZero (q * r * r') := ⟨hm.ne'⟩
    unfold smoothReciprocalSum
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    unfold reciprocalPhase
    split
    · exact (stdAddChar_norm _).le
    · simp only [norm_zero, zero_le_one]
  · rw [norm_zero]
    exact sum_nonneg fun n _ => norm_nonneg _

private theorem e1Dyadic_mem_Ioc {L n : ℕ} (hL : 0 < L) (hn : n ∈ Icc L (2 * L)) :
    n ∈ Ioc 0 (2 * L) :=
  mem_Ioc.mpr ⟨hL.trans_le (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩

private theorem e1Dyadic_card (L : ℕ) : (Icc L (2 * L)).card = L + 1 := by
  rw [Nat.card_Icc]
  omega

private theorem e1Term_norm_le_completed (Q R q r r' : ℕ) (a h h' : ℤ)
    (hQ : 0 < Q) (hR : 0 < R)
    (hq : q ∈ Icc Q (2 * Q)) (hr : r ∈ Icc R (2 * R)) (hr' : r' ∈ Icc R (2 * R))
    (haq : a.natAbs.Coprime q) (har : a.natAbs.Coprime r) (har' : a.natAbs.Coprime r')
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S)
    {C : ℝ} (hC : 0 ≤ C) (hdecay : ∀ x : ℝ, ‖(𝓕 w) x‖ ≤ C / (1 + |x|) ^ 2)
    (P : ℕ) (hP : ∀ m ∈ Ioc 0 (8 * Q * R ^ 2), m.divisors.card ≤ P) :
    ‖e1CompletedSmoothTerm q r r' h h' a N w S‖ ≤
      6 * C * (P : ℝ)^2 * (Real.sqrt Q * R) + (C * N / ((Q : ℝ) * (R : ℝ)^2)) *
        (Int.gcd (e1Determinant h h' r r') ((q * r * r' : ℕ) : ℤ) : ℝ) := by
  let m := q * r * r'
  let j := e1Determinant h h' r r'
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos
    (mem_Ioc.mp (e1Dyadic_mem_Ioc hQ hq)).1 (mem_Ioc.mp (e1Dyadic_mem_Ioc hR hr)).1)
    (mem_Ioc.mp (e1Dyadic_mem_Ioc hR hr')).1
  let _ : NeZero m := ⟨hm.ne'⟩
  have hlow (L n : ℕ) (hn : n ∈ Icc L (2 * L)) : L ≤ n := (mem_Icc.mp hn).1
  have hupp (L n : ℕ) (hn : n ∈ Icc L (2 * L)) : n ≤ 2 * L := (mem_Icc.mp hn).2
  have hmLower : Q * R ^ 2 ≤ m := by
    calc
      _ = Q * R * R := by ring
      _ ≤ m := Nat.mul_le_mul (Nat.mul_le_mul (hlow Q q hq) (hlow R r hr)) (hlow R r' hr')
  have hmUpper : m ≤ 8 * Q * R ^ 2 := by
    calc
      m ≤ 2 * Q * (2 * R) * (2 * R) :=
        Nat.mul_le_mul (Nat.mul_le_mul (hupp Q q hq) (hupp R r hr)) (hupp R r' hr')
      _ = _ := by ring
  have hmodP := hP m (mem_Ioc.mpr ⟨hm, hmUpper⟩)
  have hmLowerR : (Q : ℝ) * (R : ℝ)^2 ≤ m := by exact_mod_cast hmLower
  have hmUpperR : (m : ℝ) ≤ 8 * (Q : ℝ) * (R : ℝ)^2 := by exact_mod_cast hmUpper
  have hroot : Real.sqrt m ≤ 3 * (Real.sqrt Q * R) := by
    have hsq : (3 * (Real.sqrt Q * (R : ℝ))) ^ 2 = 9 * (Q : ℝ) * (R : ℝ)^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg Q)]
      ring
    rw [Real.sqrt_le_left (by positivity), hsq]
    exact hmUpperR.trans (by gcongr; norm_num)
  have ha : a.natAbs.Coprime m := by
    simpa only [m, mul_assoc] using haq.mul_right (har.mul_right har')
  have hgcd : m.gcd (a * j).natAbs = Int.gcd j (m : ℤ) := by
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast, Int.natAbs_mul, Nat.gcd_comm m]
    exact ha.gcd_mul_left_cancel j.natAbs
  have hzero : ‖(𝓕 w) 0‖ ≤ C := by simpa using hdecay 0
  have hratio : N / (m : ℝ) ≤ N / ((Q : ℝ) * (R : ℝ)^2) :=
    div_le_div_of_nonneg_left hN.le (by positivity) hmLowerR
  rw [e1CompletedSmoothTerm, dif_pos hm]
  refine (smoothReciprocalSum_norm_le m (a * j) hN w S hneg hS C hC hdecay).trans ?_
  rw [hgcd]
  apply add_le_add
  · have hP' : (m.divisors.card : ℝ) ≤ (P : ℝ) := Nat.cast_le.mpr hmodP
    calc
      _ ≤ 2 * C * (P : ℝ)^2 * (3 * (Real.sqrt Q * R)) := by gcongr
      _ = _ := by ring
  · change _ ≤ C * N / ((Q : ℝ) * (R : ℝ)^2) * (Int.gcd j (m : ℤ) : ℝ)
    rw [mul_div_assoc, mul_comm C]
    gcongr

private theorem e1DyadicZero_sum_eq_card (Q R H : ℕ) :
    (∑ _q ∈ Icc Q (2 * Q), ∑ r ∈ Icc R (2 * R), ∑ r' ∈ Icc R (2 * R),
        ∑ h ∈ e1NonzeroFrequencies H, ∑ h' ∈ e1NonzeroFrequencies H,
          if e1Determinant h h' r r' = 0 then (1 : ℝ) else 0) =
      ((Q : ℝ) + 1) * ((e1ZeroDeterminantTuplesClosed H R).card : ℝ) := by
  let Rset := Icc R (2 * R)
  let F := e1NonzeroFrequencies H
  simp only [sum_const, e1Dyadic_card, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  congr 1
  rw [e1ZeroDeterminantTuplesClosed, card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, sum_filter, sum_product]
  let z (r r' : ℕ) (h h' : ℤ) : ℝ := if e1Determinant h h' r r' = 0 then 1 else 0
  change (∑ r ∈ Rset, ∑ r' ∈ Rset, ∑ h ∈ F, ∑ h' ∈ F, z r r' h h') =
    ∑ h ∈ F, ∑ r ∈ Rset, ∑ h' ∈ F, ∑ r' ∈ Rset, z r r' h h'
  simp_rw [sum_comm (s := Rset) (t := F)]

/-- The completed Cauchy mass splits into the zero determinant,
Weil and nonzero determinant Ramanujan contributions. -/
theorem e1CompletedCauchyMass_le (Q R H P T J : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (a : ℤ) {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S)
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hdecay : ∀ x : ℝ, ‖(𝓕 w) x‖ ≤ C / (1 + |x|) ^ 2)
    (hmass : (∑ n ∈ S, ‖w ((n : ℝ) / N)‖) ≤ B * N)
    (hP : ∀ m ∈ Ioc 0 (8 * Q * R ^ 2), m.divisors.card ≤ P)
    (hT : ∀ d ∈ Ioc 0 (2 * R), d.divisors.card ≤ T)
    (hJ : ∀ j : ℤ, j ≠ 0 → j.natAbs ≤ 2 * H * (2 * R) → j.natAbs.divisors.card ≤ J) :
    e1CompletedCauchyMass Q R H a N w S ≤
      (16 * B * (T : ℝ)) * (N * Q * R * H) +
      (192 * C * (P : ℝ)^2) * ((Q : ℝ) * Real.sqrt Q * (R : ℝ)^3 * (H : ℝ)^2) +
      (64 * C * (J : ℝ) * (T : ℝ)^2) * (N * R * (H : ℝ)^2) := by
  let D := Icc Q (2 * Q)
  let A := Icc R (2 * R)
  let F := e1NonzeroFrequencies H
  let K := 6 * C * (P : ℝ)^2 * (Real.sqrt Q * R)
  let L := C * N / ((Q : ℝ) * (R : ℝ)^2)
  let j (r r' : ℕ) (h h' : ℤ) := e1Determinant h h' r r'
  let z (r r' : ℕ) (h h' : ℤ) : ℝ := if j r r' h h' = 0 then 1 else 0
  let g (q r r' : ℕ) (h h' : ℤ) : ℕ :=
    if j r r' h h' = 0 then 0 else Int.gcd (j r r' h h') ((q * r * r' : ℕ) : ℤ)
  have hz0 (r r' : ℕ) (h h' : ℤ) : 0 ≤ z r r' h h' := by dsimp only [z]; split_ifs <;> norm_num
  have hpoint (q r r' : ℕ) (h h' : ℤ)
      (hq : q ∈ D.filter (fun n => n.Coprime a.natAbs)) (hr : r ∈ A.filter (fun n => n.Coprime a.natAbs))
      (hr' : r' ∈ A.filter (fun n => n.Coprime a.natAbs)) :
      ‖e1CompletedSmoothTerm q r r' h h' a N w S‖ ≤
        (B * N) * z r r' h h' + K + L * (g q r r' h h' : ℝ) := by
    by_cases hj : j r r' h h' = 0
    · simp only [z, g, if_pos hj, Nat.cast_zero, mul_zero, mul_one, add_zero]
      exact ((e1Term_norm_le_sampleMass q r r' h h' a N w S).trans hmass).trans
        (le_add_of_nonneg_right (by dsimp only [K]; positivity))
    · simp only [z, g, if_neg hj, mul_zero, zero_add]
      exact e1Term_norm_le_completed Q R q r r' a h h' hQ hR
        (mem_filter.mp hq).1 (mem_filter.mp hr).1 (mem_filter.mp hr').1
        (mem_filter.mp hq).2.symm (mem_filter.mp hr).2.symm (mem_filter.mp hr').2.symm
        hN w S hneg hS hC hdecay P hP
  let W (q r r' : ℕ) (h h' : ℤ) := (B * N) * z r r' h h' + K + L * (g q r r' h h' : ℝ)
  have hW (q r r' : ℕ) (h h' : ℤ) : 0 ≤ W q r r' h h' := by
    have := hz0 r r' h h'
    dsimp only [W, K, L]
    positivity
  have hQcard : (Q : ℝ) + 1 ≤ 2 * (Q : ℝ) := by
    have h : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hRcard : (R : ℝ) + 1 ≤ 2 * (R : ℝ) := by
    have h : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hDiag : (∑ _q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, z r r' h h') ≤
      (16 * (Q : ℝ) * H * R * T) := by
    rw [show (∑ _q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, z r r' h h') =
      ((Q : ℝ) + 1) * ((e1ZeroDeterminantTuplesClosed H R).card : ℝ) from e1DyadicZero_sum_eq_card Q R H]
    have hb : ((e1ZeroDeterminantTuplesClosed H R).card : ℝ) ≤ 8 * (H : ℝ) * R * T := by
      exact_mod_cast e1ZeroDeterminantTuplesClosed_card_le_eight_mul H R T hR
        (fun _ hd => hT _ (e1Dyadic_mem_Ioc hR hd))
    calc
      _ ≤ (2 * (Q : ℝ)) * (8 * (H : ℝ) * R * T) := by gcongr
      _ = _ := by ring
  have hGcd : (∑ q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, (g q r r' h h' : ℝ)) ≤
      (64 * (Q : ℝ) * J * ((H : ℝ) * T)^2 * (R : ℝ)^3) := by
    exact_mod_cast e1DyadicNonzeroGcd_sum_le Q R H T J hQ hR hT hJ
  calc
    _ ≤ ∑ q ∈ D.filter (fun n => n.Coprime a.natAbs),
      ∑ r ∈ A.filter (fun n => n.Coprime a.natAbs), ∑ r' ∈ A.filter (fun n => n.Coprime a.natAbs),
        ∑ h ∈ F, ∑ h' ∈ F, W q r r' h h' := by
      exact sum_le_sum fun q hq => sum_le_sum fun r hr => sum_le_sum fun r' hr' =>
        sum_le_sum fun h _ => sum_le_sum fun h' _ => hpoint q r r' h h' hq hr hr'
    _ ≤ ∑ q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, W q r r' h h' := by
      refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_).trans ?_
      · intro q _ _
        exact sum_nonneg fun r _ => sum_nonneg fun r' _ =>
          sum_nonneg fun h _ => sum_nonneg fun h' _ => hW q r r' h h'
      apply sum_le_sum
      intro q _
      refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) ?_).trans ?_
      · intro r _ _
        exact sum_nonneg fun r' _ => sum_nonneg fun h _ => sum_nonneg fun h' _ => hW q r r' h h'
      apply sum_le_sum
      intro r _
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun r' _ _ =>
        sum_nonneg fun h _ => sum_nonneg fun h' _ => hW q r r' h h')
    _ = (B * N) * (∑ _q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, z r r' h h') +
        K * (((Q : ℝ) + 1) * (((R : ℝ) + 1) * (2 * H))^2) +
        L * (∑ q ∈ D, ∑ r ∈ A, ∑ r' ∈ A, ∑ h ∈ F, ∑ h' ∈ F, (g q r r' h h' : ℝ)) := by
      simp only [W, sum_add_distrib, ← mul_sum, sum_const, D, A, F, e1Dyadic_card,
        card_e1NonzeroFrequencies, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
        Nat.cast_one]
      ring
    _ ≤ (B * N) * (16 * (Q : ℝ) * H * R * T) +
        K * ((2 * (Q : ℝ)) * ((2 * (R : ℝ)) * (2 * H))^2) +
        L * (64 * (Q : ℝ) * J * ((H : ℝ) * T)^2 * (R : ℝ)^3) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hDiag (by positivity))
        (by have hK : 0 ≤ K := by dsimp only [K]; positivity
            gcongr)) (mul_le_mul_of_nonneg_left hGcd (by dsimp only [L]; positivity))
    _ = _ := by
      dsimp only [K, L]
      have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
      field_simp
      ring

/-- All three divisor caps in the completed E1 mass are absorbed into an
arbitrary fixed power under one polynomial envelope. -/
theorem exists_e1CompletedCauchyMass_rpow {κ ε B C : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (Q R H : ℕ), 0 < Q → 0 < R →
      (8 * (Q : ℝ) * (R : ℝ)^2) ≤ X ^ κ →
      (2 * (R : ℝ)) ≤ X ^ κ → (4 * (H : ℝ) * (R : ℝ)) ≤ X ^ κ →
      ∀ (a : ℤ) (N : ℝ), 0 < N → ∀ (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ),
      (∀ x : ℝ, x < 0 → w x = 0) →
      (∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S) →
      (∀ x : ℝ, ‖(𝓕 w) x‖ ≤ C / (1 + |x|)^2) →
      (∑ n ∈ S, ‖w ((n : ℝ) / N)‖) ≤ B * N →
      e1CompletedCauchyMass Q R H a N w S ≤
        K * X ^ ε * (N * Q * R * H + (Q : ℝ) * Real.sqrt Q * (R : ℝ)^3 * (H : ℝ)^2 +
          N * R * (H : ℝ)^2) := by
  let δ := ε / (3 * κ)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨D, hD, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) hδ
  refine ⟨(1 + 16 * B + 192 * C) * (D + 2)^3, by positivity, ?_⟩
  intro X hX Q R H hQ hR hQR hRbox hHR a N hN w S hneg hS hdecay hmass
  let Dcap := 1 + ⌈D * X ^ (κ * δ)⌉₊
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hXpow : 1 ≤ X ^ (κ * δ) := Real.one_le_rpow hX (by positivity)
  have hcap1N : 1 ≤ Dcap := by dsimp only [Dcap]; omega
  have hcap1 : (1 : ℝ) ≤ (Dcap : ℝ) := by exact_mod_cast hcap1N
  have hcap (n : ℕ) (hn : 0 < n) (hnX : (n : ℝ) ≤ X ^ κ) : n.divisors.card ≤ Dcap := by
    have hb : (n.divisors.card : ℝ) ≤ (Dcap : ℝ) := by
      rw [← fouvryTau_two]
      calc
        _ ≤ D * (n : ℝ) ^ δ := htau n hn
        _ ≤ D * (X ^ κ) ^ δ := by gcongr
        _ ≤ _ := by
          rw [← Real.rpow_mul hX0.le]
          have hc := Nat.le_ceil (D * X ^ (κ * δ))
          push_cast [Dcap]
          linarith
    exact_mod_cast hb
  have hP : ∀ m ∈ Ioc 0 (8 * Q * R ^ 2), m.divisors.card ≤ Dcap := by
    intro m hm
    exact hcap m (mem_Ioc.mp hm).1 ((by exact_mod_cast (mem_Ioc.mp hm).2 :
      (m : ℝ) ≤ 8 * (Q : ℝ) * (R : ℝ)^2).trans hQR)
  have hT : ∀ d ∈ Ioc 0 (2 * R), d.divisors.card ≤ Dcap := by
    intro d hd
    exact hcap d (mem_Ioc.mp hd).1 ((by exact_mod_cast (mem_Ioc.mp hd).2 :
      (d : ℝ) ≤ 2 * (R : ℝ)).trans hRbox)
  have hJ : ∀ j : ℤ, j ≠ 0 → j.natAbs ≤ 2 * H * (2 * R) → j.natAbs.divisors.card ≤ Dcap := by
    intro j hj hbox
    have hb : (j.natAbs : ℝ) ≤ 2 * (H : ℝ) * (2 * (R : ℝ)) := by exact_mod_cast hbox
    apply hcap _ (Int.natAbs_pos.mpr hj)
    exact hb.trans (le_of_eq (by ring)) |>.trans hHR
  have hDcap : (Dcap : ℝ) ≤ (D + 2) * X ^ (κ * δ) := by
    have h := (Nat.ceil_lt_add_one (show 0 ≤ D * X ^ (κ * δ) by positivity)).le
    dsimp only [Dcap]
    push_cast
    nlinarith only [h, hXpow]
  have hcapCube : (Dcap : ℝ)^3 ≤ (D + 2)^3 * X ^ ε := by
    calc
      _ ≤ ((D + 2) * X ^ (κ * δ)) ^ 3 := by gcongr
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat]
        congr 1
        dsimp only [δ]
        field_simp
  let Ω := (1 + 16 * B + 192 * C) * (Dcap : ℝ)^3
  have hΩ : Ω ≤ (1 + 16 * B + 192 * C) * (D + 2)^3 * X ^ ε := by
    dsimp only [Ω]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hcapCube (by positivity)
  have h1 : (Dcap : ℝ) ≤ (Dcap : ℝ)^3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcap1) (show 0 ≤ (Dcap : ℝ)^2 + Dcap by positivity)]
  have h2 : (Dcap : ℝ)^2 ≤ (Dcap : ℝ)^3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcap1) (show 0 ≤ (Dcap : ℝ)^2 by positivity)]
  have hc1 : 16 * B * (Dcap : ℝ) ≤ Ω := by
    dsimp only [Ω]
    exact mul_le_mul (by linarith) h1 (by positivity) (by positivity)
  have hc2 : 192 * C * (Dcap : ℝ)^2 ≤ Ω := by
    dsimp only [Ω]
    exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
  have hc3 : 64 * C * (Dcap : ℝ)^2 * (Dcap : ℝ) ≤ Ω := by
    dsimp only [Ω]
    nlinarith only [mul_nonneg (show 0 ≤ 1 + 16 * B + 128 * C by positivity)
      (show 0 ≤ (Dcap : ℝ)^3 by positivity)]
  have hc3' : 64 * C * (Dcap : ℝ) * (Dcap : ℝ)^2 ≤ Ω := by
    calc
      _ = 64 * C * (Dcap : ℝ)^2 * (Dcap : ℝ) := by ring
      _ ≤ Ω := hc3
  refine (e1CompletedCauchyMass_le Q R H Dcap Dcap Dcap hQ hR a hN w S hneg hS hC hB
    hdecay hmass hP hT hJ).trans ?_
  rw [mul_add, mul_add]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right (hc1.trans hΩ) (by positivity))
    (mul_le_mul_of_nonneg_right (hc2.trans hΩ) (by positivity)))
    (mul_le_mul_of_nonneg_right (hc3'.trans hΩ) (by positivity))

/-- The primitive mean's totient denominator costs a uniform chosen subpower. -/
theorem exists_e1ReciprocalTotient_rpow {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (X : ℝ), 1 ≤ X → ∀ (Q R : ℕ), 0 < Q → 0 < R →
      4 * (Q : ℝ) * R ≤ X ^ κ →
      ∀ q ∈ Icc Q (2 * Q), ∀ s ∈ Icc R (2 * R),
        (1 : ℝ) / (q * s).totient ≤ (D * X ^ ε) / ((Q : ℝ) * R) := by
  let δ := ε / κ
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨D, hD, htau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) hδ
  refine ⟨D, hD, ?_⟩
  intro X hX Q R hQ hR hcap q hq s hs
  let m := q * s
  have hlow : Q * R ≤ m := Nat.mul_le_mul (mem_Icc.mp hq).1 (mem_Icc.mp hs).1
  have hm : 0 < m := (Nat.mul_pos hQ hR).trans_le hlow
  have hup : (m : ℝ) ≤ 4 * (Q : ℝ) * R := by
    have h : (m : ℝ) ≤ (2 * (Q : ℝ)) * (2 * (R : ℝ)) := by
      exact_mod_cast Nat.mul_le_mul (mem_Icc.mp hq).2 (mem_Icc.mp hs).2
    exact h.trans_eq (by ring)
  have hφ : (0 : ℝ) < m.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm)
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmτ : (m : ℝ) ≤ (m.totient : ℝ) * (fouvryTau 2 m : ℝ) := by
    exact_mod_cast le_totient_mul_fouvryTau_two m
  have hτ : (fouvryTau 2 m : ℝ) ≤ D * X ^ ε := by
    refine (htau m hm).trans ?_
    calc
      _ ≤ D * (X ^ κ) ^ δ := by gcongr; exact hup.trans hcap
      _ = _ := by
        rw [← Real.rpow_mul (zero_le_one.trans hX)]
        congr 1
        dsimp only [δ]
        field_simp
  change (1 : ℝ) / m.totient ≤ _
  calc
    _ ≤ (fouvryTau 2 m : ℝ) / m := by
      rw [div_le_div_iff₀ hφ hm', one_mul, mul_comm]
      exact hmτ
    _ ≤ (D * X ^ ε) / m := div_le_div_of_nonneg_right hτ hm'.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast hlow)

/-- Fixed logarithmic cutoff slack, squared, costs a selectable subpower. -/
theorem e1Cutoff_log_budget {ε X L C : ℝ} (hε : 0 < ε) (hX : 1 ≤ X)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hcut : L ≤ C * (Real.log X)^5) :
    max L (L^2) ≤ (1 + C * (10 / ε)^5)^2 * X ^ ε := by
  have hX0 := zero_lt_one.trans_le hX
  have hlog := Real.log_le_rpow_div hX0.le (show 0 < ε / 10 by positivity)
  have hlog' : Real.log X ≤ (10 / ε) * X ^ (ε / 10) := by
    convert hlog using 1
    field_simp
  have hpower : (X ^ (ε / 10)) ^ 5 = X ^ (ε / 2) := by
    rw [← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat]
    congr 1
    ring
  have hL' : L ≤ C * (10 / ε)^5 * X ^ (ε / 2) := by
    refine hcut.trans ?_
    calc
      _ ≤ C * ((10 / ε) * X ^ (ε / 10)) ^ 5 := by gcongr; exact Real.log_nonneg hX
      _ = _ := by rw [mul_pow, hpower, mul_assoc]
  let U := (1 + C * (10 / ε)^5) * X ^ (ε / 2)
  have hU1 : 1 ≤ U := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right (by positivity)) (Real.one_le_rpow hX (by positivity))
  have hLU : L ≤ U := hL'.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hU : U^2 = (1 + C * (10 / ε)^5)^2 * X ^ ε := by
    dsimp only [U]
    rw [mul_pow, ← Real.rpow_mul_natCast hX0.le, Nat.cast_ofNat,
      show ε / 2 * 2 = ε by ring]
  rw [← hU]
  apply max_le
  · exact hLU.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hU1) (show 0 ≤ U by positivity)])
  · exact pow_le_pow_left₀ hL hLU 2

/-- Multiply the completed Cauchy estimate by the original scale factor
and the fixed logarithmic slack. -/
theorem e1_scale_budget_le {N Q R M H L X ε D P K Ccut : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hM : 0 < M) (hH : 0 ≤ H)
    (hL : 0 ≤ L) (hX : 1 ≤ X) (hε : 0 < ε)
    (hK : 0 ≤ K) (hCcut : 0 ≤ Ccut)
    (hx : X = M * N) (hcut : H ≤ L * (Q * R / M))
    (hLcut : L ≤ Ccut * (Real.log X)^5) :
    (D * X ^ (ε/4))^2 * P^2 * (K * X ^ (ε/4)) *
        (N^3 / (Q^3 * R^2) *
          (N * Q * R * H + Q * Real.sqrt Q * R^3 * H^2 + N * R * H^2)) ≤
      (D^2 * P^2 * K * (1 + Ccut * (40 / ε)^5)^2) * X ^ ε * (N^4 / Q^2) *
        (N * Q / X + N * Q ^ (5/2 : ℝ) * R^3 / X^2 + N^2 * Q * R / X^2) := by
  let A1 := N * Q / X
  let A2 := N * Q ^ (5/2 : ℝ) * R^3 / X^2
  let A3 := N^2 * Q * R / X^2
  let V := (D * X ^ (ε / 4))^2 * P^2 * (K * X ^ (ε / 4))
  have hX0 := zero_lt_one.trans_le hX
  have hU : max L (L^2) ≤ (1 + Ccut * (40 / ε)^5)^2 * X ^ (ε/4) := by
    have h := e1Cutoff_log_budget (ε := ε / 4) (by positivity) hX hL hCcut hLcut
    have h40 : 10 / (ε / 4) = 40 / ε := by field_simp; norm_num
    rwa [h40] at h
  have hscales := e1_cauchyMonomials_le N Q R M H L X hN hQ hR hM hH hx hcut
  calc
    _ ≤ V * (N^4 / Q^2 * (L * A1 + L^2 * A2 + L^2 * A3)) :=
      mul_le_mul_of_nonneg_left hscales (by dsimp only [V]; positivity)
    _ ≤ V * (N^4 / Q^2 * (((1 + Ccut * (40 / ε)^5)^2 * X ^ (ε/4)) * (A1 + A2 + A3))) := by
      have hL1 := (le_max_left L (L^2)).trans hU
      have hL2 := (le_max_right L (L^2)).trans hU
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (by dsimp only [V]; positivity)
      rw [mul_add, mul_add]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hL1 (by dsimp only [A1]; positivity))
        (mul_le_mul_of_nonneg_right hL2 (by dsimp only [A2]; positivity)))
        (mul_le_mul_of_nonneg_right hL2 (by dsimp only [A3]; positivity))
    _ = _ := by
      have hcombine : (X ^ (ε/4))^2 * X ^ (ε/4) * X ^ (ε/4) = X ^ ε := by
        rw [pow_two, ← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_add hX0]
        congr 1
        ring
      dsimp only [V]
      rw [← hcombine]
      change _ = _ * _ * (N^4 / Q^2) * (A1 + A2 + A3)
      ring

/-- The fixed dyadic majorant covers each original natural sample and
has total sampled mass at most (4N). -/
theorem e1_fixedMajorant (N : ℕ) (hN : 0 < N) :
    let w := CommonSmoothCutoff.dyadicCutoffSchwartz
    let S := Icc 0 (3 * N)
    Icc N (2 * N) ⊆ S ∧
      (∀ n ∈ S, 0 ≤ (w ((n : ℝ) / (N : ℝ))).re) ∧
      (∀ n ∈ Icc N (2 * N), 1 ≤ (w ((n : ℝ) / (N : ℝ))).re) ∧
      (∀ x : ℝ, x < 0 → w x = 0) ∧
      (∀ n : ℕ, w ((n : ℝ) / (N : ℝ)) ≠ 0 → n ∈ S) ∧
      (∑ n ∈ S, ‖w ((n : ℝ) / (N : ℝ))‖) ≤ 4 * (N : ℝ) := by
  dsimp only
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hne (x : ℝ) (hx : CommonSmoothCutoff.dyadicCutoffSchwartz x ≠ 0) :
      x ∈ Set.Icc (1 / 2 : ℝ) 3 := by
    rw [CommonSmoothCutoff.dyadicCutoffSchwartz_apply, Ne, Complex.ofReal_eq_zero] at hx
    exact CommonSmoothCutoff.dyadicCutoff_tsupport_subset (subset_closure hx)
  refine ⟨fun n hn => mem_Icc.mpr ⟨Nat.zero_le _, by have := (mem_Icc.mp hn).2; omega⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro n _
    simpa only [CommonSmoothCutoff.dyadicCutoffSchwartz_apply, Complex.ofReal_re] using
      CommonSmoothCutoff.dyadicCutoff_nonneg ((n : ℝ) / N)
  · intro n hn
    rw [CommonSmoothCutoff.dyadicCutoffSchwartz_apply, Complex.ofReal_re,
      CommonSmoothCutoff.dyadicCutoff_eq_one]
    refine ⟨(le_div_iff₀ hN').mpr ?_, (div_le_iff₀ hN').mpr ?_⟩
    · simpa using (Nat.cast_le.mpr (mem_Icc.mp hn).1 : (N : ℝ) ≤ n)
    · exact_mod_cast (mem_Icc.mp hn).2
  · intro x hx
    by_contra h
    have := (hne x h).1
    linarith
  · intro n hn
    have hnp := (div_le_iff₀ hN').mp (hne ((n : ℝ) / N) hn).2
    exact mem_Icc.mpr ⟨Nat.zero_le _, by exact_mod_cast hnp⟩
  · calc
      _ ≤ ∑ _n ∈ Icc 0 (3 * N), (1 : ℝ) := by
        apply sum_le_sum
        intro n _
        rw [CommonSmoothCutoff.dyadicCutoffSchwartz_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (CommonSmoothCutoff.dyadicCutoff_nonneg _)]
        exact CommonSmoothCutoff.dyadicCutoff_le_one _
      _ ≤ _ := by
        simp only [sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith

end

end ImbalancedChen.Part3
