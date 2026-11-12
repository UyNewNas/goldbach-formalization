import ImbalancedChen.Part5OriginalH430ClassicalProperWallMarkedOutputs
import ImbalancedChen.PowerErrorBudget

/-! Absolute original outer, colour, order and least-tail wall allowance.
The preassigned input level fixes the intercepts before the target tends
to infinity. A prime dividing the target is handled on the full rough output. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalProperWallSeedCredit
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_const)
open Part5OriginalH430ClassicalFixedClampGeometry (expanded_geometry prefix_data)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount (multiplicity)
open Part5OriginalH430ClassicalRadialMarkedRanks (vectors vector_spec)
open Part5OriginalH430ClassicalProperWallPairs (outputs output_wall_budget)
open Part5OriginalH430ClassicalProperWallMarkedOutputs (properTuples bad onWall rank_bound)
open scoped Classical Topology BigOperators

def properCount (N : ℕ) (ν δ : ℝ) : ℝ :=
  20*∑ k : Fin 201,((properTuples N k.val ν δ).card:ℝ)

def markedProper (N : ℕ) (ν κ δ : ℝ) : ℝ :=
  wordsSum (fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter (onWall ν δ)).card:ℝ))

theorem all_proper_ranks {N : ℕ} (hN : 2<N) (ν δ : ℝ) :
    properCount N ν δ≤multiplicity*(((outputs N ν δ).card:ℝ)+((bad N).card:ℝ)) := by
  have hh := sum_le_sum (s:=(univ:Finset (Fin 201))) (fun k _ => rank_bound hN k.val ν δ)
  rw [←sum_mul] at hh
  unfold properCount multiplicity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤20)

theorem original_proper_le {N : ℕ} {ν κ δ : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hν' : ν≤1/2) (hk : κ≤1/112) : markedProper N ν κ δ≤properCount N ν δ := by
  let R := fun k : Fin 201 => ((properTuples N k.val ν δ).card:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hd := words_mono (F:=fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter
    (onWall ν δ)).card:ℝ)) (G:=fun _ => ∑ k,R k) (by
    intro j cs hc
    apply sum_le_sum
    intro k _
    apply Nat.cast_le.mpr
    apply card_le_card
    intro t ht
    obtain ⟨hv,hw⟩ := mem_filter.mp ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    obtain ⟨hm,hl⟩ := mem_filter.mp hu
    obtain ⟨_,hpr,hprod,hfloor⟩ := vector_spec j hc hN hν hν' hk hu
    have hlen := (expanded_geometry j hc hN hν hν' hk hm).2.2.2.2.1
    have hcap := (prefix_data hN hν hm).2.2.2.2.2.1
    apply mem_filter.mpr
    refine ⟨hpr,by omega,fun i => ?_,?_,hw⟩
    · exact (rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (1/96:ℝ)≤1/90)).trans (hfloor i)
    · rw [hprod]
      exact (Nat.cast_le.mpr hcap).trans (by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)]))
  rw [words_const] at hd
  exact hd

theorem target_bad_small {ε : ℝ} (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,(log (N:ℝ)/(N:ℝ))*((bad N).card:ℝ)≤ε := by
  have hh := (tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0:ℝ)<1/96)).const_mul ((2:ℝ)/log 2)
  rw [mul_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds he),eventually_gt_atTop (1:ℕ)] with N hsmall hN
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hcut : 0<cut N := rpow_pos_of_pos h0 _
  have hbad := p5U7ActualBadRough_card_le_log (N:=N) (x:=2*(N:ℝ)) (z:=cut N) (by omega)
    (by positivity) hcut
  apply (mul_le_mul_of_nonneg_left hbad (div_nonneg (log_pos hNr).le h0.le)).trans
  calc
    _ = (2/log 2)*((log (N:ℝ))^2/(N:ℝ)^(1/96:ℝ)) := by
      dsimp only [cut] at hcut ⊢
      field_simp [h0.ne',hcut.ne',(log_pos (by norm_num : (1:ℝ)<2)).ne'] <;> ring
    _ ≤ _ := hsmall.le

/-- All eight walls in a single finite strip, every ordered pair of slots
and every original word. The width is a function of the fixed level and
the budget and is independent of N and of its prime divisors. -/
theorem absolute_proper_payment (ν : ℝ) {ε : ℝ} (he : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ N : ℕ in atTop,(log (N:ℝ)/(N:ℝ))*properCount N ν δ≤ε := by
  have hm : 0≤multiplicity := by unfold multiplicity; positivity
  let e := ε/(2*(multiplicity+1))
  have hden : 0<2*(multiplicity+1) := by linarith only [hm]
  have hep : 0<e := div_pos he hden
  have hprice : e*(2*(multiplicity+1))=ε := div_mul_cancel₀ _ hden.ne'
  obtain ⟨δ,hd,hout⟩ := output_wall_budget ν hep
  refine ⟨δ,hd,?_⟩
  filter_upwards [hout,target_bad_small hep,eventually_gt_atTop (2:ℕ)] with N ho hb hN
  have hn : 0≤log (N:ℝ)/(N:ℝ) := div_nonneg (log_nonneg (by exact_mod_cast (show 1≤N by omega)))
    (Nat.cast_nonneg _)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add ho hb) hm
  calc
    _ ≤ (log (N:ℝ)/(N:ℝ))*(multiplicity*(((outputs N ν δ).card:ℝ)+((bad N).card:ℝ))) :=
      mul_le_mul_of_nonneg_left (all_proper_ranks hN ν δ) hn
    _ = multiplicity*((log (N:ℝ)/(N:ℝ))*((outputs N ν δ).card:ℝ)+
      (log (N:ℝ)/(N:ℝ))*((bad N).card:ℝ)) := by ring
    _ ≤ multiplicity*(e+e) := hsum
    _ ≤ ε := by linarith only [hprice,hep]

end
end ImbalancedChen.Part5OriginalH430ClassicalProperWallSeedCredit

