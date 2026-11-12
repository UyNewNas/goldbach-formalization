import ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeFamily
import ImbalancedChen.Part5OriginalH430ClassicalSmoothFineSelected

/-! The remaining actual signed PP of the Fine-selected upper bound is the
sum over the native ranks of this one geometric family, on the same moduli
and coefficient. All interchanges precede absolute values. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeSignedSum
noncomputable section
open Finset Real Wu2008DoubleSieve
open Part3 (primeProductSignedError labelledPrimeTuples labelledProduct)
open P5Z.AdmissibleAllRankIntegerGeometricFamily (originalWeight)
open Part5OriginalH430ClassicalSmoothPositiveSieve (signedPart whole)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankSupport (W)
open Part5OriginalH430ClassicalSmoothSharpGates (code)
open Part5OriginalH430ClassicalSmoothRealProfile (raw prime_agrees)
open Part5OriginalH430ClassicalSmoothAllOccurrences
open Part5OriginalH430ClassicalSmoothNativeFamily (family)
open scoped Classical Topology BigOperators

private theorem signed_sum {α : Type*} [Fintype α] (k P N : ℕ) (Q : Finset ℕ) (ρ : ℕ → ℝ)
    (F : α → (Fin k → Fin (P+1)) → ℝ) :
    primeProductSignedError k P N Q ρ (fun t => ∑ o : α,F o t)=
      ∑ o : α,primeProductSignedError k P N Q ρ (F o) := by
  let K := fun (q : ℕ) (t : Fin k → Fin (P+1)) =>
    (if Nat.ModEq q (labelledProduct t) N then (1:ℝ) else 0)-
      (if Nat.Coprime (labelledProduct t) q then (1:ℝ) else 0)/(q.totient:ℝ)
  calc
    _ = ∑ d∈Q,∑ o : α,ρ d*(∑ t∈labelledPrimeTuples k P,F o t*K d t) := by
      unfold primeProductSignedError
      apply sum_congr rfl
      intro d _
      rw [←mul_sum]
      congr 1
      simp only [sum_mul]
      exact sum_comm
    _ = _ := sum_comm

def nativeResidual (N : ℕ) (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
    (hc : 0<c) (hc' : c≤1/8) (Q : Finset ℕ) (ρ : ℕ → ℝ) : ℝ :=
  ∑ k : Fin 201,primeProductSignedError k.val (2*N) N Q ρ (fun t =>
    originalWeight (family ν hd hh hh' hc hc') N k (fun i => (t i).val))

theorem all_rank_signed_eq {N : ℕ} (hN : 2≤N) (ν : ℝ) {δ h c : ℝ}
    (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8) (Q : Finset ℕ) (ρ : ℕ → ℝ) :
    nativeResidual N ν hd hh hh' hc hc' Q ρ=whole (signedPart N ν δ h c Q ρ) := by
  let F := fun (o : Occurrence) (k : Fin 201) (t : Fin k.val → Fin (2*N+1)) =>
    lane N ν δ h c o k (fun i => ((t i).val:ℝ))
  let E := fun (k : Fin 201) (o : Occurrence) =>
    primeProductSignedError k.val (2*N) N Q ρ (F o k)
  have hK (k : Fin 201) : primeProductSignedError k.val (2*N) N Q ρ (fun t =>
      originalWeight (family ν hd hh hh' hc hc') N k (fun i => (t i).val))=∑ o : Occurrence,E k o := by
    have he : (fun t : Fin k.val → Fin (2*N+1) =>
          originalWeight (family ν hd hh hh' hc hc') N k (fun i => (t i).val))=
        (fun t => ∑ o : Occurrence,F o k t) := by
      funext t; change ambient ν δ h c N k (fun i => ((t i).val:ℝ))=_
      rw [ambient,if_pos hN]
    rw [he]
    exact signed_sum _ _ _ Q ρ (fun o => F o k)
  have hLane (o : Occurrence) : (∑ k : Fin 201,E k o)=signedPart N ν δ h c Q ρ (word o) (length o) := by
    rw [sum_eq_single (order o) (fun k _ hne => by
      dsimp only [E,F]
      simp only [off_rank hne,primeProductSignedError,zero_mul,sum_const_zero,mul_zero])
      (fun hno => (hno (mem_univ _)).elim)]
    have he : F o (order o)=(fun t => W (word o) t ν δ h c) := by
      funext t
      dsimp only [F]
      rw [on_rank]
      exact prime_agrees (word o) ν δ h c t
    dsimp only [E]
    rw [he] <;> rfl
  unfold nativeResidual
  simp_rw [hK]
  rw [sum_comm]
  simp_rw [hLane]
  exact occurrences_eq (signedPart N ν δ h c Q ρ)

theorem selected_fine_residual {N : ℕ} (hN : 2≤N) (n₀ : ℕ) (t₀ : ℝ) {δ h c : ℝ}
    (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
    (m round n : ℕ) (e : ℚ) (q : ℕ) (a ν β : ℝ) (k : ℕ) :
    let μ := Part5OriginalH430RootIntervalTheta.clampLevel n₀ t₀
    let D := P4AOriginalFiniteAll22FineDensity.modulusFamily ν β 0 N
    let R := P4AOriginalFiniteAll22FineDensity.coefficientFamily m round n e q a ν β k 0 N
    whole (signedPart N μ δ h c D R)=nativeResidual N μ hd hh hh' hc hc' D R :=
  (all_rank_signed_eq hN _ hd hh hh' hc hc' _ _).symm

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeSignedSum

