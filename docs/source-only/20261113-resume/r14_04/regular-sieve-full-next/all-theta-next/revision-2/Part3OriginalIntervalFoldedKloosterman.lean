import ImbalancedChen.Part3OriginalKloostermanOperatorL2
import ImbalancedChen.Part3ActualCommonIntervalCompletionParseval
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

/-! Physical rectangular restrictions of the complete Kloosterman
operator, for the second estimate in Drappeau Lemma 4.6. The contiguous
intervals may cross the residue boundary any number of times. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalIntervalFoldedKloosterman20261113
open Finset Complex
open OriginalSmoothPoissonTail (kloosterman)
open OriginalSmoothPoissonTail.FiniteOperator20261026b (energy originalOperator originalOperator_energy_le)
open ActualCommonIntervalCompletionParsevalSourceOnly (wrappedOccupancy wrappedOccupancy_eq_quot_or_succ)

def foldRow (c A B : ℕ) [NeZero c] (a : ℕ → ℂ) (r : ZMod c) : ℂ :=
  ∑ n∈(Ico A B).filter (fun n => (n:ZMod c)=r),a n

def intervalEnergy (A B : ℕ) (a : ℕ → ℂ) := ∑ n∈Ico A B,‖a n‖^2

theorem fold_energy {c A B H : ℕ} [NeZero c] (hAB : A≤B) (hH : B-A≤H)
    (a : ℕ → ℂ) : energy c (foldRow c A B a)≤
        (((H/c+1:ℕ):ℝ))*intervalEnergy A B a := by
  let W := Ico A B
  let I := fun r : ZMod c => W.filter (fun n => (n:ZMod c)=r)
  have one (r : ZMod c) : ‖foldRow c A B a r‖^2 ≤
      ((H/c+1:ℕ):ℝ)*∑ n∈I r,‖a n‖^2 := by
    have cardI : (I r).card≤H/c+1 := by
      have d := Nat.div_le_div_right (c:=c) hH
      change wrappedOccupancy A B c r≤_
      rcases wrappedOccupancy_eq_quot_or_succ A B c hAB r with h|h <;>omega
    change ‖∑ n∈I r,a n‖^2≤_
    apply (show ‖∑ n∈I r,a n‖^2≤((I r).card:ℝ)*∑ n∈I r,‖a n‖^2 by
      simpa using OAI.CubicFirstMoment.complex_bilinear_rows_sq (I r) (fun _ => (1:ℂ)) a).trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast cardI) (sum_nonneg (fun _ _ => sq_nonneg _))
  have L := sum_le_sum (s:=(univ : Finset (ZMod c))) (fun r _ => one r)
  rw [←mul_sum] at L
  exact L.trans_eq (congrArg (fun y : ℝ => ((H/c+1:ℕ):ℝ)*y)
    (sum_fiberwise_of_maps_to (s:=W) (t:=(univ : Finset (ZMod c)))
      (g:=fun n : ℕ => (n:ZMod c)) (fun _ _ => mem_univ _) (fun n => ‖a n‖^2)))

private theorem representative (c : ℕ) [NeZero c] (m n : ℕ) :
    kloosterman c (m:ℤ) (n:ℤ)=kloosterman c ((m:ZMod c).val:ℤ) ((n:ZMod c).val:ℤ) := by
  simp only [OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod,Int.cast_natCast,ZMod.natCast_zmod_val]

theorem rectangular_identity (c A B D E : ℕ) [NeZero c] (a b : ℕ → ℂ) :
    (∑ m∈Ico A B,∑ n∈Ico D E,a m*b n*kloosterman c (m:ℤ) (n:ℤ))=
      ∑ r : ZMod c,foldRow c A B a r*originalOperator c (foldRow c D E b) r := by
  let M := Ico A B
  let N := Ico D E
  let f := fun m : ℕ => ∑ n∈N,a m*b n*kloosterman c (m:ℤ) (n:ℤ)
  have G := sum_fiberwise_of_maps_to (s:=M) (t:=(univ : Finset (ZMod c)))
    (g:=fun m : ℕ => (m:ZMod c)) (fun _ _ => mem_univ _) f
  change (∑ m∈M,f m)=_
  rw [←G]
  apply sum_congr rfl
  intro r hr
  simp only [foldRow,sum_mul]
  apply sum_congr rfl
  intro m hm
  have mr := (mem_filter.mp hm).2
  have T := sum_fiberwise_of_maps_to (s:=N) (t:=(univ : Finset (ZMod c)))
    (g:=fun n : ℕ => (n:ZMod c)) (fun _ _ => mem_univ _)
    (fun n => a m*b n*kloosterman c (m:ℤ) (n:ℤ))
  dsimp only [f]
  rw [←T]
  simp only [originalOperator,foldRow,mul_sum]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro n hn
  rw [representative,mr,(mem_filter.mp hn).2]
  ring

/-- Each interval has length at most H. The charge (c+H) is obtained
from the existing sharp complete operator and the true occupancy. -/
theorem rectangular_bound {c A B D E H : ℕ} [NeZero c] (hAB : A≤B)
    (hDE : D≤E) (hM : B-A≤H) (hN : E-D≤H) (a b : ℕ → ℂ) :
    ‖∑ m∈Ico A B,∑ n∈Ico D E,a m*b n*kloosterman c (m:ℤ) (n:ℤ)‖≤
      ((c:ℝ)+H)*Real.sqrt (intervalEnergy A B a)*Real.sqrt (intervalEnergy D E b) := by
  let V : ℝ := (H/c+1:ℕ)
  let F := foldRow c A B a
  let G := foldRow c D E b
  have hV : 0≤V := Nat.cast_nonneg _
  have b0 : 0≤intervalEnergy D E b := sum_nonneg (fun _ _ => sq_nonneg _)
  have a0 : 0≤intervalEnergy A B a := sum_nonneg (fun _ _ => sq_nonneg _)
  have cost : (c:ℝ)*V≤c+H := by
    have h := Nat.div_mul_le_self H c
    have hc : c*(H/c+1)≤c+H := by rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm c (H/c)];omega
    exact_mod_cast hc
  have LF := fold_energy hAB hM a
  have RG := (originalOperator_energy_le c G).trans
    (mul_le_mul_of_nonneg_left (fold_energy hDE hN b) (sq_nonneg _))
  have C := OAI.CubicFirstMoment.complex_bilinear_rows_sq (univ : Finset (ZMod c)) F (originalOperator c G)
  have Q := C.trans (mul_le_mul LF RG
    (sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg hV a0))
  have S := Real.sqrt_le_sqrt Q
  rw [Real.sqrt_sq (norm_nonneg _)] at S
  change ‖∑ r:ZMod c,F r*originalOperator c G r‖≤
    Real.sqrt ((V*intervalEnergy A B a)*((c:ℝ)^2*(V*intervalEnergy D E b))) at S
  rw [Real.sqrt_mul (mul_nonneg hV a0),Real.sqrt_mul hV,Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg c),Real.sqrt_mul hV] at S
  rw [rectangular_identity]
  calc
    _≤_ := S
    _=(c:ℝ)*(Real.sqrt V)^2*Real.sqrt (intervalEnergy A B a)*Real.sqrt (intervalEnergy D E b) := by ring
    _≤_ := by
      rw [Real.sq_sqrt hV]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right cost (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end ImbalancedChen.Part3.OriginalIntervalFoldedKloosterman20261113
end
