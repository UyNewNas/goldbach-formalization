import ImbalancedChen.Part5OriginalH430ClassicalSmoothMarkedFamily
import ImbalancedChen.P5RoughLogGridSmoothTensorPartition

/-! The native positive telescoping tensor on the actual base-two prime
scales. The sum of all overlapping rectangles is one before evaluating
either the additive test or the signed congruence-minus-coprime kernel. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothDyadicFamily
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open P5Z.RoughLogGridSmoothPartition
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankSupport (W)
open Part5OriginalH430ClassicalSmoothRankAccounting (tails smoothRank)
open Part5OriginalH430ClassicalSmoothMarkedFamily (smoothCount)
open scoped Classical Topology BigOperators

def lastScale (N : ℕ) := Nat.ceil (log (2*(N:ℝ))/log 2)
abbrev Rect (k N : ℕ) := Labels k (lastScale N)
def logTwo {k N : ℕ} (t : Fin k → Fin (2*N+1)) (i : Fin k) := log ((t i).val:ℝ)/log 2
def partition {k N : ℕ} (j : Rect k N) (t : Fin k → Fin (2*N+1)) : ℝ :=
  tensor 0 ((lastScale N:ℝ)+1) (lastScale N) 1 j (logTwo t)

theorem endpoints (n : ℕ) (j : Fin (n+1)) :
    left 0 ((n:ℝ)+1) n j=(j.val:ℝ) ∧ right 0 ((n:ℝ)+1) n j=(j.val:ℝ)+1 := by
  simp [left,right,logPrimeMeshPoint,logPrimeMeshStep,show (n:ℝ)+1≠0 by positivity]

theorem actual_partition {N k : ℕ} (hN : 0<N) (t : Fin k → Fin (2*N+1))
    (ht : t∈Part3.labelledPrimeTuples k (2*N)) : (∑ j : Rect k N,partition j t)=1 := by
  apply sum_tensors_eq_one (by norm_num)
  intro i
  have hp := (mem_filter.mp ht).2 i
  have hpos : (0:ℝ)<(t i).val := Nat.cast_pos.mpr hp.pos
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have hcap : ((t i).val:ℝ)≤2*(N:ℝ) := by exact_mod_cast (Nat.lt_succ_iff.mp (t i).isLt)
  have H := div_le_div_of_nonneg_right (log_le_log hpos hcap) h2.le
  have hceil : log (2*(N:ℝ))/log 2≤(lastScale N:ℝ) := Nat.le_ceil _
  exact ⟨div_nonneg (log_nonneg (by exact_mod_cast hp.one_lt.le)) h2.le,by
    dsimp only [logTwo]
    linarith only [H,hceil]⟩

theorem rectangle_nonneg {k N : ℕ} (j : Rect k N) (t : Fin k → Fin (2*N+1)) :
    0≤partition j t := tensor_nonneg (by positivity) (by norm_num) _ _ _

theorem rectangle_support {k N : ℕ} (j : Rect k N) (t : Fin k → Fin (2*N+1))
    (ht : partition j t≠0) :
    ∀ i, ((j i).val : ℝ) - 1 < logTwo t i ∧ logTwo t i < ((j i).val : ℝ) + 1 := by
  intro i
  have h := tensor_nonzero_support (a:=(0:ℝ)) (b:=(lastScale N:ℝ)+1) (δ:=1)
    (by positivity) (by norm_num) _ _ _ ht i
  rwa [(endpoints _ _).1,(endpoints _ _).2] at h

theorem rectangle_count (k N : ℕ) (hN : 1≤N) :
    (Fintype.card (Rect k N):ℝ)≤(3+log (N:ℝ)/log 2)^k := by
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have h2N : (1:ℝ)≤2*(N:ℝ) := by have hh : (1:ℝ)≤N := by exact_mod_cast hN; linarith
  have hh := Nat.ceil_lt_add_one (div_nonneg (log_nonneg h2N) h2.le)
  rw [log_mul (by norm_num : (2:ℝ)≠0) h0.ne',add_div,div_self h2.ne'] at hh
  simp only [Rect,Labels,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  apply pow_le_pow_left₀ (by positivity)
  change (Nat.ceil (log (2*(N:ℝ))/log 2):ℝ)+1≤_
  rw [log_mul (by norm_num : (2:ℝ)≠0) h0.ne',add_div,div_self h2.ne']
  linarith only [hh]

def rectangleWeight {r N : ℕ} (cs : List ℕ) (j : Rect (rank cs.length r) N)
    (ν δ h c : ℝ) (t : Fin (rank cs.length r) → Fin (2*N+1)) :=
  partition j t*W cs t ν δ h c

theorem restore_tuple {r N : ℕ} (hN : 0<N) (cs : List ℕ) (t : Fin (rank cs.length r) → Fin (2*N+1))
    (ht : t∈Part3.labelledPrimeTuples (rank cs.length r) (2*N)) (ν δ h c : ℝ) :
    (∑ j : Rect (rank cs.length r) N,rectangleWeight cs j ν δ h c t)=W cs t ν δ h c := by
  simp only [rectangleWeight,←sum_mul,actual_partition hN t ht,one_mul]

theorem restore_sum (tested : Bool) {N : ℕ} (hN : 0<N) (ν δ h c : ℝ) :
    smoothCount tested N ν δ h c=wordsSum (fun cs => ∑ r∈tails cs.length,
      ∑ j : Rect (rank cs.length r) N,∑ t∈Part3.labelledPrimeTuples (rank cs.length r) (2*N),
        rectangleWeight cs j ν δ h c t*testWeight tested N 1 (Part3.labelledProduct t)) := by
  apply congrArg wordsSum
  funext cs
  apply sum_congr rfl
  intro r _
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  rw [←sum_mul,restore_tuple hN cs t ht]

/-- The finite physical signed PP itself recombines at the same rho before
taking its absolute value, with the exact genuine coprime centre intact. -/
theorem restore_signed {r N : ℕ} (hN : 0<N) (cs : List ℕ) (D : Finset ℕ) (ρ : ℕ → ℝ) (ν δ h c : ℝ) :
    Part3.primeProductSignedError (rank cs.length r) (2*N) N D ρ (fun t => W cs t ν δ h c)=
      ∑ j : Rect (rank cs.length r) N,Part3.primeProductSignedError (rank cs.length r) (2*N) N
        D ρ (rectangleWeight cs j ν δ h c) := by
  unfold Part3.primeProductSignedError
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←mul_sum,sum_comm]
  apply congrArg (fun x : ℝ => ρ d*x)
  apply sum_congr rfl
  intro t ht
  rw [←sum_mul,restore_tuple hN cs t ht]

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothDyadicFamily

