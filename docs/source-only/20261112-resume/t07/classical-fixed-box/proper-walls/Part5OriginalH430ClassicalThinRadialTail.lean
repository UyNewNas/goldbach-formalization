import ImbalancedChen.Part5OriginalH430ClassicalProperWallSeedCredit

/-! The small radial endpoint of the actual large-product cut. A fixed
positive c absorbs N^(1-kappa)/N eventually at each positive kappa.
The entire marked ambient interval 0<M≤cN has ordinary density O(c). -/
namespace ImbalancedChen.Part5OriginalH430ClassicalThinRadialTail
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_const)
open Part5OriginalH430ClassicalFixedClampGeometry (prefix_data)
open Part5OriginalH430ClassicalRadialRoughMass (cut shell endpoint)
open Part5OriginalH430ClassicalRadialTupleCount (bandTuples boundaryCount all_ranks_bound multiplicity)
open Part5OriginalH430ClassicalRadialMarkedRanks (vectors vector_spec)
open scoped Classical Topology BigOperators

def markedThin (N : ℕ) (ν κ c : ℝ) : ℝ :=
  wordsSum (fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter (fun t =>
    (Part3.labelledProduct t:ℝ)≤c*(N:ℝ))).card:ℝ))

theorem original_thin_le {N : ℕ} {ν κ c : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hν' : ν≤1/2) (hk : κ≤1/112) : markedThin N ν κ c≤boundaryCount N 0 c := by
  let R := fun k : Fin 201 => ((bandTuples N k.val 0 c).card:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hd := words_mono (F:=fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter
    (fun t => (Part3.labelledProduct t:ℝ)≤c*(N:ℝ))).card:ℝ)) (G:=fun _ => ∑ k,R k) (by
    intro j cs hc
    apply sum_le_sum
    intro k _
    apply Nat.cast_le.mpr
    apply card_le_card
    intro t ht
    obtain ⟨hv,hcap⟩ := mem_filter.mp ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    obtain ⟨_,hpr,hprod,hfloor⟩ := vector_spec j hc hN hν hν' hk hu
    have hpos := (prefix_data hN hν (mem_filter.mp hu).1).2.2.2.2.1
    apply mem_filter.mpr
    refine ⟨hpr,fun i => ?_,?_,hcap⟩
    · exact (rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (1/96:ℝ)≤1/90)).trans (hfloor i)
    · rw [zero_mul,hprod]
      exact Nat.cast_pos.mpr hpos)
  rw [words_const] at hd
  exact hd

theorem lower_wall_in_tail {κ c : ℝ} (hk : 0<κ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)^(1-κ)≤c*(N:ℝ) := by
  have hh := (tendsto_rpow_neg_atTop hk).comp tendsto_natCast_atTop_atTop
  filter_upwards [hh.eventually (gt_mem_nhds hc),eventually_gt_atTop (0:ℕ)] with N hN hpos
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  rw [show 1-κ= -κ+1 by ring,rpow_add h0,rpow_one]
  exact mul_le_mul_of_nonneg_right hN.le h0.le

theorem absolute_thin_payment {ε : ℝ} (he : 0<ε) :
    ∃ c : ℝ,0<c ∧ c≤1/8 ∧ ∀ᶠ N : ℕ in atTop,
      (log (N:ℝ)/(N:ℝ))*boundaryCount N 0 c≤ε := by
  have hm : 0≤multiplicity := by unfold multiplicity; positivity
  let A := 96*multiplicity
  have hA : 0≤A := by dsimp only [A]; positivity
  let c := min (1/8:ℝ) (ε/(2*(A+1)))
  have hd : 0<2*(A+1) := by linarith only [hA]
  have hc : 0<c := lt_min (by norm_num) (div_pos he hd)
  have hc' : c≤1/8 := min_le_left _ _
  have hec := (le_div_iff₀ hd).mp (show c≤ε/(2*(A+1)) from min_le_right _ _)
  have homega := mul_le_mul_of_nonneg_left (buchstab_le_one (by norm_num : (1:ℝ)≤96))
    (show 0≤multiplicity*(96*c) from mul_nonneg hm (by positivity))
  have hsmall : multiplicity*(96*c*buchstab 96)<ε := by
    dsimp only [A] at hec
    nlinarith only [hec,hc,homega,mul_nonneg hm hc.le]
  have hlim := (endpoint hc).const_mul multiplicity
  refine ⟨c,hc,hc',?_⟩
  filter_upwards [hlim.eventually (gt_mem_nhds hsmall),eventually_gt_atTop (1:ℕ)] with N hs hN
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hn := div_nonneg (log_pos hNr).le (Nat.cast_nonneg N)
  have hsub : shell N 0 c⊆roughNumbers (c*(N:ℝ)) (cut N) := fun _ hs => (mem_sdiff.mp hs).1
  have hcard : ((shell N 0 c).card:ℝ)≤(roughCount (c*(N:ℝ)) (cut N):ℝ) :=
    Nat.cast_le.mpr (card_le_card hsub)
  have hb := (all_ranks_bound N 0 c).trans (mul_le_mul_of_nonneg_left hcard hm)
  calc
    _ ≤ (log (N:ℝ)/(N:ℝ))*(multiplicity*(roughCount (c*(N:ℝ)) (cut N):ℝ)) :=
      mul_le_mul_of_nonneg_left hb hn
    _ = multiplicity*((log (N:ℝ)/(N:ℝ))*(roughCount (c*(N:ℝ)) (cut N):ℝ)) := by ring
    _ ≤ ε := hs.le

end
end ImbalancedChen.Part5OriginalH430ClassicalThinRadialTail

