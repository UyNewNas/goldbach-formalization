import ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerProfile

/-! The all-orders bounds apply to the literal positive physical box
coefficient, evaluated at p_i=2^{j_i} exp(u_i). This identity holds on
the entire positive chart before restricting it to integer prime tuples. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalCharts
noncomputable section
open Finset Set Filter Real Wu2008DoubleSieve
open P4B P5Z.RoughLogGridSmoothPartition
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothWordPhysical (logPoint)
open Part5OriginalH430ClassicalSmoothSharpGates (code physicalProduct)
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothRankSupport (W)
open Part5OriginalH430ClassicalSmoothDyadicFamily
open Part5OriginalH430ClassicalSmoothEulerBounds (E)
open Part5OriginalH430ClassicalSmoothEulerProfile
open scoped Classical Topology BigOperators ContDiff

def centre {k N : ℕ} (j : Rect k N) (i : Fin k) : ℝ := ((j i).val:ℝ)*log 2
def primeChart {k N : ℕ} (j : Rect k N) (u : E k) (i : Fin k) := exp (centre j i+u i)

/-- The real chart weight uses literal prime magnitude, split prime logs,
and the radial coordinate given by the entire product divided by N. -/
def realRectangle {s r N : ℕ} (C : Fin s → ℕ) (j : Rect (rank s r) N) (ν δ h c : ℝ)
    (v : E (rank s r)) : ℝ :=
  tensor 0 ((lastScale N:ℝ)+1) (lastScale N) 1 j (fun i => log (v i)/log 2) *
    outerWeight C ν δ h c (split (fun i => log (v i)/log (N:ℝ)))
      (split (fun i => v i/(N:ℝ)^(1/90:ℝ))) ((∏ i,v i)/(N:ℝ))

theorem chart_identity {s r N : ℕ} (hN : 2≤N) (C : Fin s → ℕ) (j : Rect (rank s r) N)
    (ν δ h c : ℝ) (u : E (rank s r)) :
    realRectangle C j ν δ h c (primeChart j u)=
      chart C ν δ h c (⟨N,hN⟩,centre j) u := by
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have hB (i : Fin (rank s r)) :
      label 0 ((lastScale N:ℝ)+1) (lastScale N) 1 (j i) (log (primeChart j u i)/log 2)=bump (u i) := by
    rw [label,(endpoints _ _).1,(endpoints _ _).2,primeChart,log_exp]
    have he : (centre j i+u i)/log 2=(j i).val+u i/log 2 := by
      dsimp only [centre]
      field_simp [h2.ne'] <;> ring
    rw [he]
    unfold bump
    congr 1 <;> congr 1 <;> ring
  have hR (i : Fin (rank s r)) : primeChart j u i/(N:ℝ)^(1/90:ℝ)=
      exp (centre j i+u i-(1/90)*log (N:ℝ)) := by
    rw [exp_sub,rpow_def_of_pos h0,mul_comm (1/90:ℝ) (log (N:ℝ))] <;> rfl
  have hM : (∏ i,primeChart j u i)/(N:ℝ)=radial (⟨N,hN⟩,centre j) u := by
    rw [radial,exp_sub,exp_log h0,Real.exp_sum] <;> rfl
  unfold realRectangle chart
  simp only [tensor,hB,hR,hM,logCoords,ratios,primeChart,log_exp]

theorem at_prime_tuple {r N : ℕ} (cs : List ℕ) (j : Rect (rank cs.length r) N)
    (t : Fin (rank cs.length r) → Fin (2*N+1)) (ν δ h c : ℝ) :
    realRectangle (code cs) j ν δ h c (fun i => ((t i).val:ℝ))=rectangleWeight cs j ν δ h c t := by
  have h := entire_product t
  have hM : (∏ i,((t i).val:ℝ))=
      (physicalProduct (first (fun i => (t i).val)) (qVec (fun i => (t i).val)) (rVec (fun i => (t i).val)):ℝ) := by
    exact_mod_cast h
  change _=partition j t*W cs t ν δ h c
  unfold realRectangle
  rw [hM]
  rfl

theorem chart_at_prime {r N : ℕ} (hN : 2≤N) (cs : List ℕ) (j : Rect (rank cs.length r) N)
    (t : Fin (rank cs.length r) → Fin (2*N+1)) (ht : t∈Part3.labelledPrimeTuples (rank cs.length r) (2*N))
    (ν δ h c : ℝ) :
    rectangleWeight cs j ν δ h c t=
      chart (code cs) ν δ h c (⟨N,hN⟩,centre j) (fun i => log ((t i).val:ℝ)-centre j i) := by
  rw [←chart_identity hN,←at_prime_tuple cs j t]
  congr 1
  funext i
  change ((t i).val:ℝ)=exp (centre j i+(log ((t i).val:ℝ)-centre j i))
  rw [show centre j i+(log ((t i).val:ℝ)-centre j i)=log ((t i).val:ℝ) by ring,
    exp_log (Nat.cast_pos.mpr ((mem_filter.mp ht).2 i).pos)]

theorem bump_support {x : ℝ} (hx : bump x≠0) : -log 2<x ∧ x<log 2 := by
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have hw : (0:ℝ)<1 := by norm_num
  constructor
  · by_contra! h
    have h' : x/log 2≤ -1 := (div_le_iff₀ h2).mpr (by linarith only [h])
    have ha := smoothGateUpperStep_eq_zero hw h'
    have hb := smoothGateUpperStep_eq_zero hw (show x/log 2-1≤ -1 by linarith only [h'])
    exact hx (by simp only [bump,ha,hb,sub_zero])
  · by_contra! h
    have h' := (one_le_div h2).mpr h
    have ha := smoothGateUpperStep_eq_one hw (zero_le_one.trans h')
    have hb := smoothGateUpperStep_eq_one hw (sub_nonneg.mpr h')
    exact hx (by simp only [bump,ha,hb,sub_self])

theorem compact_chart {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) (a : Param (rank s r)) :
    HasCompactSupport (chart C ν δ h c a) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi (fun _ : Fin (rank s r) =>
    (isCompact_Icc : IsCompact (Icc (-log 2) (log 2)))))
  intro u hu i _
  have hb := (prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hu).1) i (mem_univ i)
  obtain ⟨hl,hr⟩ := bump_support hb
  exact ⟨hl.le,hr.le⟩

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalCharts

