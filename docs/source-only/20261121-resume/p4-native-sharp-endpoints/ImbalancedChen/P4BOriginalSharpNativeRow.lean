import ImbalancedChen.P4BOriginalSharpPairComparison

/-! SOURCE ONLY / UNCOMPILED. Exact native half-open long blocks.
Only the two selected long positions are rewritten; all short positions,
including units and repeated values, remain in the original signed fibre. -/
namespace ImbalancedChen.P4BOriginalSharpNativeRow
noncomputable section
open Classical Set
open scoped BigOperators
open PrimeProducts
open P4BOriginalSharpLongProfiles
open P4BOriginalRoughPairFinite (roughDelta roughDelta_original)
open P4BOriginalRoughE3Assembly (roughSum)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalTwoLongActualDictionary (same_rho_mode_eq_fibres)
open Part3.TwoLongActualHBShortMass
open Part3.TwoLongRetainedRowReindex (roughFibreCore longWeight)
open Part3.TwoLongHBMellinBrunProfiles (owned_long_role_profile)
open Part3.TwoLongTransitionMellinN2 (logFactor)
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.PrimeMellinProfileVariation20261026b (phase)
open Part3.TwoLongQuantitativeTransitionProfiles (sharp)
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.ActualHBDyadicProductWindow (lower owns_bounds)
open P5Z.ActualRoughHeathBrownWords (Role actual)
open P5Z.ActualLowerNormalizedBlockGeometry (blockIntegers rectangle scales mem_blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)

theorem owned_mem_wide (b : Block) {n : ℕ} (hn : Owns b n) : n∈wideWindow (lower b) := by
  have hb := owns_bounds hn
  have hl : (0:ℝ)≤lower b := Nat.cast_nonneg _
  have hnR : (n:ℝ)≤2*(lower b:ℝ) := by exact_mod_cast hb.2
  refine Finset.mem_Icc.mpr ⟨Nat.zero_le _,?_⟩
  have H : (n:ℝ)≤Nat.ceil ((5/2:ℝ)*(lower b:ℝ)) :=
    (show (n:ℝ)≤(5/2:ℝ)*(lower b:ℝ) by linarith).trans (Nat.le_ceil _)
  exact_mod_cast H

theorem sharp_slot_eq_owned (b : Block) (hU : (1:ℝ)<lower b) (Z y t : ℝ)
    (role : Role) (hrole : role=.one ∨ role=.logarithm) (n : ℕ) :
    sharpProfile (decide (role=.logarithm)) (lower b) t ((n:ℝ)/(lower b:ℝ))*Part3.roughOneSlot Z n=
      if Owns b n then actual Z y role n*phase t ((n:ℝ)/(lower b:ℝ)) else 0 := by
  by_cases hn : Owns b n
  · have hmem := (owns_iff_Ioc hU n).mp hn
    have H := owned_long_role_profile (d:=1) (u:=n) (by norm_num) (by simpa using hn) Z y t role hrole
    simp only [one_mul,div_one] at H
    rw [if_pos hn,sharpProfile,sharp,if_pos hmem,one_mul]
    exact H.symm
  · have hmem : ¬(n:ℝ)/(lower b:ℝ)∈Ioc (1:ℝ) 2 := fun h => hn ((owns_iff_Ioc hU n).mpr h)
    simp [sharpProfile,sharp,hmem,hn]

theorem sharp_fibre_identity {r : ℕ} (bs : Fin r→Block) (Z : ℝ) (ys xi : Fin r→ℝ)
    (rs : Fin r→Role) (i t : Fin r)
    (hU : (1:ℝ)<lower (bs i)) (hV : (1:ℝ)<lower (bs t)) (hZ : 0≤Z)
    (hri : rs i=.one ∨ rs i=.logarithm) (hrt : rs t=.one ∨ rs t=.logarithm)
    (short N q : ℕ) (alpha : ℂ) :
    roughDelta (sharpProfile (decide (rs i=.logarithm)) (lower (bs i)) (xi i))
      (sharpProfile (decide (rs t=.logarithm)) (lower (bs t)) (xi t))
      (lower (bs i)) (lower (bs t)) Z short N q alpha=
      alpha*roughFibreCore bs Z ys xi rs i t short N q := by
  rw [roughDelta_original _ _ _ _ hZ]
  have hfi : (wideWindow (lower (bs i))).filter (Owns (bs i))=blockIntegers (bs i) := by
    ext n
    simp only [Finset.mem_filter,mem_blockIntegers]
    exact ⟨And.right,fun hn => ⟨owned_mem_wide _ hn,hn⟩⟩
  have hft : (wideWindow (lower (bs t))).filter (Owns (bs t))=blockIntegers (bs t) := by
    ext n
    simp only [Finset.mem_filter,mem_blockIntegers]
    exact ⟨And.right,fun hn => ⟨owned_mem_wide _ hn,hn⟩⟩
  have hid (u v : ℕ) :
      alpha*sharpProfile (decide (rs i=.logarithm)) (lower (bs i)) (xi i) ((u:ℝ)/(lower (bs i):ℝ))*
        sharpProfile (decide (rs t=.logarithm)) (lower (bs t)) (xi t) ((v:ℝ)/(lower (bs t):ℝ))*
        Part3.roughOneSlot Z u*Part3.roughOneSlot Z v=
      alpha*(if Owns (bs i) u then longWeight (bs i) Z (ys i) (xi i) (rs i) u else 0)*
        (if Owns (bs t) v then longWeight (bs t) Z (ys t) (xi t) (rs t) v else 0) := by
    dsimp only [longWeight]
    rw [←sharp_slot_eq_owned (bs i) hU Z (ys i) (xi i) (rs i) hri u,
      ←sharp_slot_eq_owned (bs t) hV Z (ys t) (xi t) (rs t) hrt v]
    ring
  simp_rw [hid]
  unfold roughFibreCore
  rw [←hfi,←hft]
  simp only [Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hui : Owns (bs i) u
  · simp only [if_pos hui]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hvt : Owns (bs t) v <;> simp [hui,hvt] <;> ring
  · simp [hui]

def nativeMode {r : ℕ} (bs : Fin r→Block) (Z : ℝ) (ys xi : Fin r→ℝ) (rs : Fin r→Role)
    (N : ℕ) (S : Finset ℕ) (c : ℕ→ℂ) : ℂ :=
  MellinInsertion20261028.exactDiscrepancy (rectangle bs) S c completeProduct N
    (fun y => hbSlots Z ys rs y*occurrenceMode (scales bs) y xi)

theorem nativeMode_eq_sharpSum {r : ℕ} (bs : Fin r→Block) (Z : ℝ) (ys xi : Fin r→ℝ)
    (rs : Fin r→Role) (i t : Fin r) (hit : i≠t)
    (hU : (1:ℝ)<lower (bs i)) (hV : (1:ℝ)<lower (bs t)) (hZ : 0≤Z)
    (hri : rs i=.one ∨ rs i=.logarithm) (hrt : rs t=.one ∨ rs t=.logarithm)
    (m r0 n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k N : ℕ) (level : ℝ) (S : Finset ℕ) :
    nativeMode bs Z ys xi rs N S (rho m r0 n e q a omega k N level)=
      roughSum (sharpProfile (decide (rs i=.logarithm)) (lower (bs i)) (xi i))
        (sharpProfile (decide (rs t=.logarithm)) (lower (bs t)) (xi t))
        (lower (bs i)) (lower (bs t)) Z
        (shortSupport (fun v : ShortPositions i t => bs v.val))
        (shortSequence (fun v : ShortPositions i t => bs v.val) Z
          (fun v => ys v.val) (fun v => xi v.val) (fun v => rs v.val))
        m r0 n e q a omega k N level S := by
  unfold nativeMode roughSum
  rw [same_rho_mode_eq_fibres bs Z ys xi rs i t hit N S]
  simp_rw [sharp_fibre_identity bs Z ys xi rs i t hU hV hZ hri hrt]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro short hshort
  ring

end
end ImbalancedChen.P4BOriginalSharpNativeRow
