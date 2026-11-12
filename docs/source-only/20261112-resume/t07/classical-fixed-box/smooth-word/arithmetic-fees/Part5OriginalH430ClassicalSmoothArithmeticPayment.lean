import ImbalancedChen.Part5OriginalH430ClassicalSmoothRankArithmetic

/-! One threshold for all original word occurrences, ranks, physical
policies and genuine clamp resolutions. Only the signed PP and the physical
density remain on the tested upper side of this positive transformed family. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothArithmeticPayment
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430RootIntervalTheta (intervalMass clampLevel clampMass)
open Part5OriginalH430ClassicalRootThetaPayment (uniform_clamp_witness)
open Part5OriginalH430ClassicalSeedIntegralCap (wordsSum words_mono words_const)
open Part5OriginalH430ClassicalFixedClampMarks (count frozen_bounds)
open Part5OriginalH430ClassicalRadialMarkedRanks (transition_floor)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankAccounting (tails)
open Part5OriginalH430ClassicalSmoothMarkedFamily (smoothCount dominates)
open Part5OriginalH430ClassicalSmoothPositiveSieve
open Part5OriginalH430ClassicalSmoothRankArithmetic
open scoped Classical Topology BigOperators

private theorem whole_le {F : List ℕ → ℕ → ℝ} {b : ℝ} (hb : 0≤b)
    (hF : ∀ cs r,rank cs.length r≤200 → F cs r≤b) : whole F≤20*(201*b) := by
  have H := words_mono (F:=fun cs => ∑ r∈tails cs.length,F cs r) (G:=fun _ => 201*b) (by
    intro _ cs _
    have h := sum_le_sum (s:=tails cs.length) (fun r hr => hF cs r (mem_filter.mp hr).2)
    have hc : (tails cs.length).card≤201 := (card_le_card (filter_subset _ _)).trans_eq (card_range 201)
    simp only [sum_const,nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hb))
  simpa only [whole,words_const] using H

theorem absolute_fees {ε : ℝ} (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ)
      (a ω τ L ν δ h c : ℝ), (N:ℝ)^ω≤cutoff N → 0<h → h≤1/8 → 0<c → c≤1/8 →
      let D := moduli N ((N:ℝ)^ω)
      let R := rho B round n e q a ω N τ L
      whole (fun cs r => |coprimePart N ν δ h c D R cs r|)+
        whole (smallPart N ν δ h c (Nat.ceil (cutoff N)))≤ε*singularNormalization N := by
  obtain ⟨A,hA,rows⟩ := correction_rank
  have hcorr := eventually_powerLog_le_singularNormalization (20*201*A) (1-1/96) 1
    (by norm_num) (ε/2) (half_pos he)
  have hsmall := eventually_powerLog_le_singularNormalization (20*201*(2*fibreBound)) (19/96) 0
    (by norm_num) (ε/2) (half_pos he)
  filter_upwards [hcorr,hsmall,transition_floor,eventually_ge_atTop (2:ℕ)] with N hcorr hsmall hz hN
  intro heven B round n e q a ω τ L ν δ h c hw hh hh' hc hc'
  let D := moduli N ((N:ℝ)^ω)
  let R := rho B round n e q a ω N τ L
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hCp : 0≤A*(N:ℝ)^(1-1/96:ℝ)*log (N:ℝ) :=
    mul_nonneg (mul_nonneg hA.le (rpow_nonneg (Nat.cast_nonneg N) _)) (log_pos hNr).le
  have hSp : 0≤(2*fibreBound)*(N:ℝ)^(19/96:ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) fibre_nonneg) (rpow_nonneg (Nat.cast_nonneg N) _)
  have H1 := whole_le (F:=fun cs r => |coprimePart N ν δ h c D R cs r|) hCp
    (fun cs r hk => rows B round n e q a ω N τ L ν δ h c cs r hN heven hw hz hh hh' hc hc' hk)
  have H2 := whole_le (F:=smallPart N ν δ h c (Nat.ceil (cutoff N))) hSp
    (fun cs r hk => small_rank cs ν δ h c (by omega) hk)
  simp only [pow_one] at hcorr
  simp only [pow_zero,mul_one] at hsmall
  change whole (fun cs r => |coprimePart N ν δ h c D R cs r|)+_≤_
  linarith only [H1,H2,hcorr,hsmall]

/-- The full absolute arithmetic bill is paid against the same original
clamp Theta. The only positivity witness is its fixed structural interval. -/
theorem absolute_fees_clamp {ε : ℝ} (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (n₀ : ℕ) (t₀ : ℝ),0≤t₀ → t₀≤1/12 → 1/((n₀:ℝ)+1)≤11/384 →
      ∀ (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ) (a ω τ L ν δ h c : ℝ),
      (N:ℝ)^ω≤cutoff N → 0<h → h≤1/8 → 0<c → c≤1/8 →
      let D := moduli N ((N:ℝ)^ω)
      let R := rho B round n e q a ω N τ L
      whole (fun cs r => |coprimePart N ν δ h c D R cs r|)+
        whole (smallPart N ν δ h c (Nat.ceil (cutoff N)))≤ε*clampMass N n₀ t₀ := by
  let I := intervalMass clampStart (1/3) (1/2)
  obtain ⟨hi,hwitness⟩ := uniform_clamp_witness
  have hI : 0<I := hi
  filter_upwards [absolute_fees (mul_pos he (half_pos hI)),hwitness] with N hp hmass
  intro even n₀ t₀ ht ht' hn B round n e q a ω τ L ν δ h c hw hh hh' hc hc'
  have h := hp even B round n e q a ω τ L ν δ h c hw hh hh' hc hc'
  dsimp only at h ⊢
  apply h.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hmass n₀ t₀ ht ht' hn) he.le

/-- In addition to the original geometry only the finite sieve policy
conditions are needed here. The two outstanding analytic expressions use
the same exact displayed moduli, same coefficient and same complete tuple. -/
theorem tested_le_density_signed {n₀ : ℕ} {t₀ κ ν δ h c ε : ℝ}
    (ht : 0≤t₀) (ht' : t₀≤1/12) (hn : 1/((n₀:ℝ)+1)≤11/384)
    (hν : ν=clampLevel n₀ t₀) (hk' : κ≤1/112) (hd : 0<δ)
    (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop,Even N → ∀ (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ) (a ω τ L : ℝ),
      1<L → (N:ℝ)^ω≤L → (N:ℝ)^ω≤cutoff N → cutoff N≤(N:ℝ) →
      let D := moduli N ((N:ℝ)^ω)
      let R := rho B round n e q a ω N τ L
      count true 1 N ν κ≤smoothCount false N ν δ h c*physicalDensitySum D R+
        whole (signedPart N ν δ h c D R)+ε*clampMass N n₀ t₀ := by
  subst ν
  let ν := clampLevel n₀ t₀
  obtain ⟨hmin,hmax⟩ := frozen_bounds ht ht' hn
  filter_upwards [absolute_fees_clamp he,eventually_gt_atTop (1:ℕ)] with N hfees hN
  intro even B round n e q a ω τ L hL hwL hwz hz
  let D := moduli N ((N:ℝ)^ω)
  let R := rho B round n e q a ω N τ L
  let C := coprimePart N ν δ h c D R
  have hminor : whole C≤whole (fun cs r => |C cs r|) := words_mono
    (fun _ cs _ => sum_le_sum (s:=tails cs.length) (fun r _ => le_abs_self (C cs r)))
  have hp := hfees even n₀ t₀ ht ht' hn B round n e q a ω τ L ν δ h c hwz hh hh' hc hc'
  have hs := physical_positive_upper B round n e q a ω N τ L ν δ h c hL hwL hwz hz
  have hsharp := dominates (c:=c) true hN hmin hmax hk' hd hh
  change count true 1 N ν κ≤smoothCount false N ν δ h c*physicalDensitySum D R+
    whole (signedPart N ν δ h c D R)+ε*clampMass N n₀ t₀
  change smoothCount true N ν δ h c≤smoothCount false N ν δ h c*physicalDensitySum D R+
    whole C+whole (signedPart N ν δ h c D R)+whole (smallPart N ν δ h c _) at hs
  change whole (fun cs r => |C cs r|)+whole (smallPart N ν δ h c _)≤_ at hp
  linarith only [hsharp,hs,hminor,hp]

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothArithmeticPayment

