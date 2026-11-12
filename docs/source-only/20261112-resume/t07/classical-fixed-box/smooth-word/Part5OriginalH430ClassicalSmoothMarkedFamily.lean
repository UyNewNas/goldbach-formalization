import ImbalancedChen.Part5OriginalH430ClassicalSmoothRankAccounting

/-! One smooth positive marked family for all twenty original occurrences.
The same W appears in the ordinary mass and in the additive prime test.
The ordinary surplus is charged before any analytic distribution estimate. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothMarkedFamily
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open Part5OriginalH430RootIntervalTheta (clampLevel clampMass)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_add words_const)
open Part5OriginalH430ClassicalFixedClampMarks (count frozen_bounds)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount (boundaryCount)
open Part5OriginalH430ClassicalRadialMarkedRanks (native_rank_count transition_floor)
open Part5OriginalH430ClassicalProperWallSeedCredit (properCount)
open Part5OriginalH430ClassicalAllBoundaryCredit (totalAmbient same_clamp_boundary_payment)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankAccounting
open scoped Classical Topology BigOperators

def smoothCount (tested : Bool) (N : ℕ) (ν δ h c : ℝ) : ℝ :=
  wordsSum (fun cs => ∑ r∈tails cs.length,smoothRank tested N ν δ h c cs r)

theorem sharp_count_exact (tested : Bool) {N : ℕ} {ν κ : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hν' : ν≤1/2) (hk : κ≤1/112) :
    count tested 1 N ν κ=wordsSum (fun cs => ∑ r∈tails cs.length,
      sharpRank tested N ν κ cs (rank cs.length r)) := by
  rw [native_rank_count hN hν hν' hk tested]
  apply congrArg wordsSum
  funext cs
  exact (restore_ranks tested hN hν cs).symm

theorem dominates (tested : Bool) {N : ℕ} {ν κ δ h c : ℝ} (hN : 1<N)
    (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) (hd : 0<δ) (hh : 0<h) :
    count tested 1 N ν κ≤smoothCount tested N ν δ h c := by
  rw [sharp_count_exact tested hN hν hν' hk]
  exact words_mono (fun j cs hc => sum_le_sum (fun r _ => sharp_le_smooth tested j hc hN hν hν' hk hd hh r))

theorem ordinary_excess {N : ℕ} {ν κ δ h c : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2)
    (hk : κ≤1/112) (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
    (hlower : (N:ℝ)^(1-κ)≤(c/2)*(N:ℝ)) (hz : cut N≤(N:ℝ)^(1/90:ℝ)/2) :
    smoothCount false N ν δ h c≤count false 1 N ν κ+totalAmbient N ν h δ c := by
  let B := ∑ k : Fin 201,collar N k.val ν δ h c
  let F := fun cs : List ℕ => ∑ r∈tails cs.length,sharpRank false N ν κ cs (rank cs.length r)
  have H := words_mono (F:=fun cs => ∑ r∈tails cs.length,smoothRank false N ν δ h c cs r)
    (G:=fun cs => F cs+B) (by
      intro j cs hcs
      have hr := sum_le_sum (s:=tails cs.length)
        (fun r _ => smooth_ordinary_le j hcs hN hν hν' hk hd hh hh' hc hc' hlower hz r)
      rw [sum_add_distrib] at hr
      exact hr.trans (add_le_add_left (collar_sum N cs.length ν δ h c) _))
  rw [words_add F (fun _ => B),words_const] at H
  have hB : 20*B=totalAmbient N ν h δ c := by
    unfold B collar totalAmbient boundaryCount properCount
    rw [sum_add_distrib,sum_add_distrib]
    ring
  rw [hB] at H
  rw [sharp_count_exact false hN hν hν' hk]
  exact H

/-- A single choice of widths dominates the actual tested and untested
carriers while paying the ordinary smooth excess to the same original Theta.
There is no signed-error cancellation between the two counts. -/
theorem original_common_outer {n : ℕ} {τ κ ε : ℝ} (ht : 0≤τ) (ht' : τ≤1/12)
    (hn : 1/((n:ℝ)+1)≤11/384) (hk : 0<κ) (hk' : κ≤1/112) (he : 0<ε) :
    ∃ h δ c : ℝ,0<h ∧ h≤1/8 ∧ 0<δ ∧ 0<c ∧ c≤1/8 ∧
      ∀ᶠ N : ℕ in atTop,let ν := clampLevel n τ;
        (∀ tested : Bool,count tested 1 N ν κ≤smoothCount tested N ν δ h c) ∧
        (8452171/1250000)*(singularSeries N/log (N:ℝ))*
          (smoothCount false N ν δ h c-count false 1 N ν κ)≤ε*clampMass N n τ := by
  obtain ⟨h,hh,hh',δ,hδ,c,hc,hc',H⟩ :
      ∃ h,0<h ∧ h≤1/8 ∧ ∃ δ,0<δ ∧ ∃ c,0<c ∧ c≤1/8 ∧
        ∀ᶠ N : ℕ in atTop,(N:ℝ)^(1-κ)≤(c/2)*(N:ℝ) ∧
          (8452171/1250000)*(singularSeries N/log (N:ℝ))*totalAmbient N (clampLevel n τ) h δ c≤
            ε*clampMass N n τ := by
    obtain ⟨h,δ,c,hh,hh',hd,hc,hc',H⟩ := same_clamp_boundary_payment ht ht' hn hk hk' he
    exact ⟨h,hh,hh',δ,hd,c,hc,hc',H.mono (fun _ hn => ⟨hn.1,hn.2.1⟩)⟩
  refine ⟨h,δ,c,hh,hh',hδ,hc,hc',?_⟩
  obtain ⟨hν,hν'⟩ := frozen_bounds ht ht' hn
  filter_upwards [H,transition_floor,eventually_ge_atTop (2:ℕ)] with N hN hz h2
  have hlarge : 1<N := by omega
  have hhA := ordinary_excess hlarge hν hν' hk' hδ hh hh' hc hc' hN.1 hz
  refine ⟨fun b => dominates b hlarge hν hν' hk' hδ hh,?_⟩
  have hsurplus : smoothCount false N (clampLevel n τ) δ h c-count false 1 N (clampLevel n τ) κ≤
      totalAmbient N (clampLevel n τ) h δ c := by linarith only [hhA]
  exact (mul_le_mul_of_nonneg_left hsurplus
    (mul_nonneg (by norm_num) (densityScale_pos h2).le)).trans hN.2

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothMarkedFamily

