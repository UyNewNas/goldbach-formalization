import ImbalancedChen.Part5OriginalH430PairExactUpperPolynomial
import ImbalancedChen.Part5OriginalH430SeedOrdinaryWindows

/-! Physical cubic cutoff for all four good pair occurrences in every W2
action. The parameter identities use the ordered pair and the parent Q. -/
namespace ImbalancedChen.Part5OriginalH430PairPhysicalCubeGeometry
noncomputable section
open Set Real Finset Wu2008DoubleSieve
open P5OriginalActionMassBound P5OriginalFeedbackDomains P2OriginalBankChildPrimeMass
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalHalfOpenProfileCarrier P2OriginalW2CountTupleReindex
open P2OriginalLiteralW1OldProfile (cutoff_eq_physical_power)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430OrdinaryPairWalls (actual_half_iff_open)
open Part5OriginalH430PairExactUpperPolynomial (original_model_and_AP)
open Part5OriginalH430SameQCanonicalMains (model)
open P2ActualMarkedCountState (rootLevel)
open scoped Classical BigOperators

theorem pair_scale {N n p d : ℕ} {r : Root} {t L η : ℝ}
    (hN : 1<N) (hd : 0<d) (hη : 0<η) (hL : η≤L)
    (hQ : rootQ N n r t p=(d:ℝ)*(N:ℝ)^L) (hQN : rootQ N n r t p≤(N:ℝ))
    (a : Fin 36) (k : Fin 4) (x : Fin 2 → ℕ)
    (hx : x∈actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5))
    (hm : normalizedLog N L x∈pairHalf (originalW2At a) k) :
    let Q := rootQ N n r t p; let b := d*x 0*x 1; let z := occurrenceCutoff Q d (originalW2At a) k (x 0) (x 1)
    0<b ∧ b≤N ∧ 1<Q/(b:ℝ) ∧ (N:ℝ)^(η/15)≤cutoff Q b 3 ∧ cutoff Q b 3≤z ∧
      model true N Q b z=model true N Q b (cutoff Q b 3) ∧
        ordinaryRosserRemainder true N b (rootLevel Q b) z=ordinaryRosserRemainder true N b (rootLevel Q b) (cutoff Q b 3) := by
  let Q := rootQ N n r t p
  let b := d*x 0*x 1
  let u := normalizedLog N L x 0
  let v := normalizedLog N L x 1
  let y := 1-u-v
  let s0 := (originalW2At a).s0
  let z := occurrenceCutoff Q d (originalW2At a) k (x 0) (x 1)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hNp := zero_lt_one.trans hNr
  have hLp := hη.trans_le hL
  have hp (i : Fin 2) := mem_actualPrimeBoxTuples_iff.mp hx i
  have hpos (i : Fin 2) := (hp i).1.pos
  have hb : 0<b := Nat.mul_pos (Nat.mul_pos hd (hpos 0)) (hpos 1)
  have hbr : (0:ℝ)<b := Nat.cast_pos.mpr hb
  have hpow0 := normalizedLog_rpow hN hLp x hpos 0
  have hpow1 := normalizedLog_rpow hN hLp x hpos 1
  change (N:ℝ)^(L*u)=(x 0:ℝ) at hpow0
  change (N:ℝ)^(L*v)=(x 1:ℝ) at hpow1
  have hsum : (N:ℝ)^(L*y)*(N:ℝ)^(L*u)*(N:ℝ)^(L*v)=(N:ℝ)^L := by
    rw [←rpow_add hNp,←rpow_add hNp]
    congr 1
    dsimp only [y]
    ring
  have hR : Q/(b:ℝ)=(N:ℝ)^(L*y) := by
    apply (div_eq_iff hbr.ne').mpr
    rw [show Q=(d:ℝ)*(N:ℝ)^L from hQ,←hsum,hpow0,hpow1]
    dsimp only [b]; push_cast; ring
  have hag := originalRepairedW2Bank_geometry _ (originalW2At_mem a)
  have hopen := (actual_half_iff_open hN hLp hQ a k x
    (fun i => ⟨(hp i).1,(hp i).2.1⟩)).mp hm
  have hy : (1/5:ℝ)≤y := (W2PairDomain_geometry hag k hopen).2
  have hR1 : 1<Q/(b:ℝ) := by rw [hR]; exact one_lt_rpow hNr (mul_pos hLp (by linarith))
  have hbN : b≤N := by
    have hh : (b:ℝ)<Q := by simpa only [one_mul] using (lt_div_iff₀ hbr).mp hR1
    exact_mod_cast (hh.trans_le hQN).le
  have hcube : cutoff Q b 3=(N:ℝ)^(L*(y/3)) := by
    unfold cutoff
    rw [hR,←rpow_mul hNp.le]
    congr 1
    ring
  have hcmin : (N:ℝ)^(η/15)≤cutoff Q b 3 := by
    rw [hcube]
    apply rpow_le_rpow_of_exponent_le hNr.le
    nlinarith only [mul_le_mul_of_nonneg_left hy hLp.le,hL]
  have hs := W2PairDomain_profile_bounds hag k hopen
  have hs3 := hs.2.1.le.trans hs.2.2
  have hs0 : 0<s0 := W2_anchor_positive hag
  have hu0 : 0<u := (show 0<(1/5:ℝ) by norm_num).trans_le
    (hag.1.trans (W2PairDomain_gates hag k hopen).1.le)
  have hbound : cutoff Q b 3≤z := by
    rw [hcube]
    by_cases hk : k.val<2
    · change pairProfile (originalW2At a) k (normalizedLog N L x)≤3 at hs3
      simp only [pairProfile,hk,if_true,fixedPairProfile] at hs3
      change s0*y≤3 at hs3
      have hr : y/3≤1/s0 := (le_div_iff₀ hs0).mpr (by linarith only [hs3])
      change _≤occurrenceCutoff Q d (originalW2At a) k (x 0) (x 1)
      rw [occurrenceCutoff,if_pos hk,cutoff_eq_physical_power hd hQ]
      apply rpow_le_rpow_of_exponent_le hNr.le
      linarith only [mul_le_mul_of_nonneg_left hr hLp.le]
    · change pairProfile (originalW2At a) k (normalizedLog N L x)≤3 at hs3
      simp only [pairProfile,hk,if_false,movingPairProfile] at hs3
      change y/u≤3 at hs3
      have hr : y/3≤u := by linarith only [(div_le_iff₀ hu0).mp hs3]
      change _≤occurrenceCutoff Q d (originalW2At a) k (x 0) (x 1)
      rw [occurrenceCutoff,if_neg hk,←hpow0]
      exact rpow_le_rpow_of_exponent_le hNr.le (mul_le_mul_of_nonneg_left hr hLp.le)
  have hQpos : 0≤Q := by rw [show Q=(d:ℝ)*(N:ℝ)^L from hQ]; positivity
  exact ⟨hb,hbN,hR1,hcmin,hbound,
    original_model_and_AP r t (Nat.mul_pos hd (hpos 0)) (hp 1).1
      ((hp 1).1.coprime_iff_not_dvd.mpr (hp 1).2.1) hQpos hbound⟩

end
end ImbalancedChen.Part5OriginalH430PairPhysicalCubeGeometry
