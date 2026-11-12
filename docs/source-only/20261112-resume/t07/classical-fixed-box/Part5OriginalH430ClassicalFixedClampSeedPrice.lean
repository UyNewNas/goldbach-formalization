import ImbalancedChen.Part5OriginalH430ClassicalFixedClampDeletion
import ImbalancedChen.Part5OriginalH430ClassicalFixedClampPrimeGeometry

/-! The fixed geometric family's ordinary upper J is bounded at the
original positive-width clamp. The K/4 seed price has exactly the
corresponding normalized limit. Neither result assumes positive switching. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampSeedPrice
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2SeedOmegaLiteralFibre (K)
open P2SeedOmegaLiteralFunctional (switchCost)
open P2EnhancedNonunitWordMass (rawScale)
open P2EnhancedNonunitLabelGeometry (ordinaryNonunitWord)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedSwitchedTrueNormalization
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSeedIntegralCap
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampGeometry (prefix_unit_below)
open Part5OriginalH430ClassicalFixedClampDeletion
open scoped Classical Topology BigOperators

def J (ν : ℝ) := cost*intervalMass clampStart (1/3) ν/4

private theorem masked_large_to_raw {N p : ℕ} {ν κ : ℝ} (hN : 1<N)
    (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) (hp : p∈outer N N) :
    allLarge false N ((N:ℝ)^ν) p (smallProduct N κ)≤
      wordsSum (ordinaryNonunitWord N ((N:ℝ)^ν) p) := by
  apply words_mono
  intro j cs hc
  apply sum_le_sum
  intro qs hqs
  have hsub : largeIntegers N (p*qs.prod) (qs.getD (qs.length-2) 0) (smallProduct N κ)⊆
      (roughNumbers ((N:ℝ)/(p*qs.prod:ℕ)) (qs.getD (qs.length-2) 0)).erase 1 := by
    intro m hm
    apply mem_erase.mpr
    refine ⟨?_,(mem_filter.mp hm).1⟩
    rintro rfl
    let u : Mark := ⟨p,qs,1⟩
    have hu : u∈marks N N ν κ cs := flags.mpr ⟨hp,hqs,hm⟩
    have hcap := prefix_unit_below j hc hN hν hν' hk (exact_target_mask.mp hu).1
    have hh := (mem_filter.mp hm).2
    rw [Nat.mul_one] at hh
    exact (not_lt_of_ge hcap) hh
  simpa only [testWeight,Bool.false_eq_true,if_false,sum_const,nsmul_eq_mul,mul_one] using
    (Nat.cast_le (α:=ℝ)).mpr (card_le_card hsub)

private theorem masked_normalized {ε : ℝ} (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ ν κ : ℝ,1/3+7/128≤ν → ν≤1/2 → κ≤1/112 →
      log (N:ℝ)/(N:ℝ)*count false N N ν κ≤
        ((cost+ε)/4)*reciprocalMass N clampStart (1/3) ν := by
  obtain ⟨T,h4,hraw⟩ := all_raw_words_upper (by norm_num : (0:ℝ)<7/128) he
  filter_upwards [eventually_ge_atTop T] with N hN
  intro ν κ hν hν' hk
  have hNr : 1<N := by omega
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hlog := log_pos (by exact_mod_cast hNr : (1:ℝ)<N)
  have hrepr : count false N N ν κ=∑ p∈outer N N,
      allLarge false N ((N:ℝ)^ν) p (smallProduct N κ) := by
    unfold count marks
    simp only [sum_sigma]
    rw [words_sum] <;> rfl
  rw [hrepr,reciprocalMass,←outer_eq_primeBand hNr,mul_sum,mul_sum]
  apply sum_le_sum
  intro p hp
  have hv := mem_primeWindow.mp hp
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hv.1.pos
  have hp1 : (1:ℝ)<p := by exact_mod_cast hv.1.one_lt
  have hp' : p∈outer 1 N := mem_primeWindow.mpr ⟨hv.1,Nat.coprime_one_right _,hv.2.2⟩
  obtain ⟨hscale,hR,_,_⟩ := platform hNr hν hp'
  have hrlog := residual_log hNr hv.1.pos ν
  have hL : 0<residualExponent N p ν := by
    have hh := log_pos hR
    rw [hrlog] at hh
    exact pos_of_mul_pos_right hh hlog.le
  have ht : 0≤prefixExponent N p := div_nonneg (log_pos hp1).le hlog.le
  have ha := (trueAlpha_ge_two_iff hNr hv.1.pos hL).mpr (by linarith)
  have hs := (masked_large_to_raw hNr hν hν' hk hp).trans
    (hraw N hN ((N:ℝ)^ν) p hv.1.pos hscale ha)
  have hraw0 : 0≤allLarge false N ((N:ℝ)^ν) p (smallProduct N κ) := by
    apply sum_nonneg
    intro j _
    exact List.sum_nonneg (fun x hx => by
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
      exact sum_nonneg (fun q _ => sum_nonneg (fun m _ => by simp [testWeight])))
  have hrawPos : 0<rawScale N ((N:ℝ)^ν) p :=
    div_pos h0 (mul_pos hp0 (log_pos hR))
  have hcost := nonneg_of_mul_nonneg_right (hraw0.trans hs) hrawPos
  have hL' : 0<ν-physicalPrime N p := hL
  have hden : 1/(p:ℝ)≤1/((p:ℝ)-1) :=
    one_div_le_one_div_of_le (sub_pos.mpr hp1) (by linarith)
  calc
    _ ≤ (log (N:ℝ)/(N:ℝ))*(rawScale N ((N:ℝ)^ν) p*(cost+ε)) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hlog.le h0.le)
    _ = ((cost+ε)/(ν-physicalPrime N p))*(1/(p:ℝ)) := by
      unfold rawScale
      rw [hrlog]
      change _*( _ / (_*(log (N:ℝ)*(ν-physicalPrime N p))) * _) = _
      field_simp [h0.ne',hp0.ne',hlog.ne',hL'.ne'] <;> ring
    _ ≤ ((cost+ε)/(ν-physicalPrime N p))*(1/((p:ℝ)-1)) :=
      mul_le_mul_of_nonneg_left hden (div_nonneg hcost hL'.le)
    _ = _ := by unfold intervalProfile; ring

/-- The absolute upper-mass hypothesis of the original fixed-family U*
for this full geometric multiset. All thresholds follow the fixed ν.
No target mask, exceptional-word indicator or p-dependent error remains. -/
theorem geometric_raw_J {ν κ ε : ℝ} (hν : 1/3+7/128≤ν) (hν' : ν≤1/2)
    (hk : κ≤1/112) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      log (N:ℝ)/(N:ℝ)*count false 1 N ν κ≤J ν+ε := by
  let I := intervalMass clampStart (1/3) ν
  have hb : 0<clampStart := by norm_num [clampStart]
  have hbc : clampStart<(1/3:ℝ) := by norm_num [clampStart]
  have hL : (1/3:ℝ)<ν := by linarith
  have hI : 0<I := intervalMass_positive hb hbc hL
  let δ := ε/(I+1)
  have hδ : 0<δ := div_pos he (by linarith)
  have hpay : δ*(I+1)=ε := div_mul_cancel₀ ε (by linarith only [hI] : I+1≠0)
  have hlim := (reciprocal_mass_limit hb hbc (by norm_num : (1/3:ℝ)<1) hL).const_mul ((cost+δ)/4)
  have hbnd : ((cost+δ)/4)*I<J ν+ε/2 := by
    change ((cost+δ)/4)*I<cost*I/4+ε/2
    linarith only [hpay,hδ,he]
  filter_upwards [masked_normalized hδ,hlim.eventually (gt_mem_nhds hbnd),
    deletion_vanishes.eventually (gt_mem_nhds (half_pos he)),eventually_gt_atTop (1:ℕ)]
    with N hmask hprice hdel hN
  have hlog : 0≤log (N:ℝ)/(N:ℝ) := div_nonneg
    (log_nonneg (by exact_mod_cast hN.le)) (Nat.cast_nonneg _)
  have hplus := mul_le_mul_of_nonneg_left (complete_deletion_le hN hν hν' hk) hlog
  rw [mul_add] at hplus
  linarith only [hplus,(hmask ν κ hν hν' hk),hprice,hdel]

/-- For the same fixed pre-target (n,τ), the seed's literal K/4
thirteen-word price tends to K times the J just proved for U*. -/
theorem original_price_common_limit {n : ℕ} {τ κ ε : ℝ} (ht : 0≤τ)
    (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hk : κ≤1/112) (he : 0<ε) :
    (∀ᶠ N : ℕ in atTop, log (N:ℝ)/(N:ℝ)*count false 1 N (clampLevel n τ) κ≤J (clampLevel n τ)+ε) ∧
    Tendsto (fun N => switchCost*clampMass N n τ/singularNormalization N) atTop
      (𝓝 (K*J (clampLevel n τ))) := by
  obtain ⟨hν,hν'⟩ := frozen_bounds ht ht' hn
  refine ⟨geometric_raw_J hν hν' hk he,?_⟩
  have h := (actual_clamp_theta_limit ht ht' hn).const_mul switchCost
  have hprice : switchCost*intervalMass clampStart (1/3) (clampLevel n τ)=K*J (clampLevel n τ) := by
    unfold switchCost J cost; ring
  rw [←hprice]
  simpa only [mul_div_assoc] using h

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampSeedPrice
