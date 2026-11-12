import ImbalancedChen.Part5OriginalH430ClassicalRadialMarkedRanks
import ImbalancedChen.ActualUpperDensityAssembly

/-! The original closed radial wall and its ambient all-rank allowance.
The second terminal returns the ordinary source collar at the manuscript's
density scale to the physical clamp Theta. It does not estimate a prime
restriction or the signed discrepancy. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRadialSeedCredit
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430RootIntervalTheta (clampMass intervalMass)
open Part5OriginalH430ClassicalRootThetaPayment (uniform_clamp_witness)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_const)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalRadialTupleCount
open Part5OriginalH430ClassicalRadialMarkedRanks
open scoped Classical Topology BigOperators

def markedBoundary (N : ℕ) (ν κ h : ℝ) : ℝ :=
  wordsSum (fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter (fun t =>
    (1-h)*(N:ℝ)≤(Part3.labelledProduct t:ℝ) ∧
      (Part3.labelledProduct t:ℝ)≤(1+h)*(N:ℝ))).card:ℝ))

theorem original_boundary_le {N : ℕ} {ν κ h : ℝ} (hN : 1<N) (hν : 1/3+7/128≤ν)
    (hν' : ν≤1/2) (hk : κ≤1/112) (hh : 0<h) :
    markedBoundary N ν κ h≤boundaryCount N (1-2*h) (1+2*h) := by
  let R := fun k : Fin 201 => ((bandTuples N k.val (1-2*h) (1+2*h)).card:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hp := mul_pos hh h0
  have hd := words_mono (F:=fun cs => ∑ k : Fin 201,(((vectors N ν κ cs k.val).filter (fun t =>
    (1-h)*(N:ℝ)≤(Part3.labelledProduct t:ℝ) ∧
      (Part3.labelledProduct t:ℝ)≤(1+h)*(N:ℝ))).card:ℝ)) (G:=fun _ => ∑ k,R k) (by
    intro j cs hc
    apply sum_le_sum
    intro k _
    apply Nat.cast_le.mpr
    apply card_le_card
    intro t ht
    obtain ⟨hv,hlo,hhi⟩ := mem_filter.mp ht
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    obtain ⟨_,hpr,_,hfloor⟩ := vector_spec j hc hN hν hν' hk hu
    apply mem_filter.mpr
    refine ⟨hpr,fun i => ?_,?_,?_⟩
    · exact (rpow_le_rpow_of_exponent_le hNr.le (by norm_num : (1/96:ℝ)≤1/90)).trans (hfloor i)
    · linarith only [hlo,hp]
    · linarith only [hhi,hp])
  rw [words_const] at hd
  exact hd

/-- The entire ambient shell at the K0 density scale, for all original
admissible resolutions simultaneously. The width precedes the target, and
the only positive mass witness is the already proved full original clamp. -/
theorem ambient_boundary_price {ε : ℝ} (he : 0<ε) :
    ∃ h : ℝ,0<h ∧ h≤1/8 ∧ ∀ᶠ N : ℕ in atTop,∀ (n : ℕ) (τ : ℝ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 →
      (8452171/1250000)*(singularSeries N/log (N:ℝ))*boundaryCount N (1-2*h) (1+2*h)≤
        ε*clampMass N n τ := by
  let I := intervalMass clampStart (1/3) (1/2)
  let K0 : ℝ := 8452171/1250000
  obtain ⟨hI,hw⟩ := uniform_clamp_witness
  have hi : 0<I := hI
  have hk : 0<K0 := by norm_num [K0]
  let δ := ε*(I/2)/K0
  have hd : 0<δ := div_pos (mul_pos he (half_pos hi)) hk
  obtain ⟨h,hp,hsmall,hbound⟩ := absolute_radial_payment hd
  refine ⟨h,hp,hsmall,?_⟩
  filter_upwards [hbound,hw,eventually_ge_atTop (2:ℕ)] with N hraw hmass hN
  intro n τ ht ht' hn
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have h0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  let B := boundaryCount N (1-2*h) (1+2*h)
  have hB : B≤δ*((N:ℝ)/log (N:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hraw (div_nonneg h0.le hlog.le)
    change ((log (N:ℝ)/(N:ℝ))*B)*((N:ℝ)/log (N:ℝ))≤_ at hh
    convert hh using 1 <;> field_simp [hlog.ne',h0.ne'] <;> ring
  have hc := mul_le_mul_of_nonneg_left hB
    (mul_nonneg hk.le (densityScale_pos hN).le)
  have hprice : K0*(singularSeries N/log (N:ℝ))*(δ*((N:ℝ)/log (N:ℝ)))=
      ε*((I/2)*singularNormalization N) := by
    rw [←sourceMassScale_mul_densityScale]
    dsimp only [δ]
    field_simp [hk.ne',hlog.ne'] <;> ring
  rw [hprice] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (hmass n τ ht ht' hn) he.le)

end
end ImbalancedChen.Part5OriginalH430ClassicalRadialSeedCredit
