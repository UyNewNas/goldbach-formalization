import ImbalancedChen.P2TwentyOneSmallPartnerThetaPayment
import ImbalancedChen.CurrentChenP5CausalPrimeCorrectionPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A concrete original-root attachment: the literal U5 pair selector and its
enhanced max-level V, with Q=N^V and d=p*q.  The numerical cap V<=153/256,
the residual floor 34/125 and the prime floor 417/5000 are taken from the
actual production dictionaries.  They discharge all arithmetic hypotheses
of the same-Q small-partner payment and masked-tail decomposition here.

This does not place a W2 action in the table induction, identify a J/cost
integral, allocate whole groups, or supply the other ten roots/history paths.
The whole original Gamma source at this root is the object being bounded.
-/
namespace ImbalancedChen.P2OriginalU5SmallPartnerRootPayment
noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted (Theta)
open P2ActualSameQTwentyOnePositiveSourceBinding (actualGoodMass actualSmallPartnerMass)
open P2TwentyOneSmallPartnerThetaPayment
open P5OriginalU5CausalFinite (pairSupport coordinates originalResidual)

def rootQ (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  (N : ℝ)^Part5OriginalUpsilon5CausalDictionary.level (coordinates N t 0) (coordinates N t 1)

/-- An auxiliary small-partner split only; the original five switching
cutoffs and the actual parent Q are untouched. -/
def smallCap (N : ℕ) : ℕ := Nat.floor ((N : ℝ)^(1/100 : ℝ))

theorem pair_primes {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    t.1.Prime ∧ t.2.Prime := by
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
  exact ⟨(mem_chenAdditivePrimeCarrier.mp hp).2.1,
    (mem_chenAdditivePrimeCarrier.mp hq).2.1⟩

theorem pair_product_pos {N : ℕ} {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    0<t.1*t.2 := mul_pos (pair_primes ht).1.pos (pair_primes ht).2.pos

/-- Physical residual identity at the real original root; alpha is not
replaced or reset, and no different child level is chosen. -/
theorem root_residual_identity {N : ℕ} (hN : 1<N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    rootQ N t/((t.1*t.2 : ℕ) : ℝ)=(N : ℝ)^(originalResidual N t) := by
  have hpos : ∀ j : Fin 2,0<(![t.1,t.2] : Fin 2 → ℕ) j := by
    intro j
    fin_cases j
    · exact (pair_primes ht).1.pos
    · exact (pair_primes ht).2.pos
  have hp := actualPrimeTupleLog_rpow hN ![t.1,t.2] hpos
  have hp0 : (N : ℝ)^coordinates N t 0=(t.1 : ℝ) := hp 0
  have hp1 : (N : ℝ)^coordinates N t 1=(t.2 : ℝ) := hp 1
  have hNpos : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hprod : ((t.1*t.2 : ℕ) : ℝ)=(N : ℝ)^(coordinates N t 0+coordinates N t 1) := by
    rw [Real.rpow_add hNpos,hp0,hp1,Nat.cast_mul]
  rw [hprod,rootQ,← Real.rpow_sub hNpos]
  congr 1
  unfold P5OriginalU5CausalFinite.originalResidual Part5OriginalUpsilon5CausalDictionary.residual
  ring

theorem root_level_cap {N : ℕ} (hN : 1≤N) (t : ℕ × ℕ) :
    rootQ N t≤(N : ℝ)^(153/256 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
    (P5CausalPrimeCorrectionPayment.original_U5_level_le_cap (coordinates N t))

theorem root_residual_gt_one {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) : 1<rootQ N t/((t.1*t.2 : ℕ) : ℝ) := by
  rw [root_residual_identity (by omega) ht]
  exact Real.one_lt_rpow (by exact_mod_cast (show 1<N by omega))
    (P5OriginalU5CausalFinite.original_geometry hN ht).2.1

/-- The actual lowest W2 cutoff is above N^(1/100), uniformly on U5. -/
theorem root_lowest_cutoff_floor {N : ℕ} (hN : 2≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    (N : ℝ)^(1/100 : ℝ)≤
      P2EnhancedTwentyOneSameQWeighted.cutoff (rootQ N t) (t.1*t.2) (227/50) := by
  have hres := (P5OriginalU5CausalFinite.original_geometry hN ht).1
  change (34/125 : ℝ)≤originalResidual N t at hres
  unfold P2EnhancedTwentyOneSameQWeighted.cutoff
  rw [root_residual_identity (by omega) ht,← Real.rpow_mul (Nat.cast_nonneg N)]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
  norm_num
  linarith

theorem smallCap_le_power (N : ℕ) : (smallCap N : ℝ)≤(N : ℝ)^(1/100 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The old d floor is proved from the original pair's lower endpoint,
including every prime divisor of the full old product. -/
theorem root_old_prime_floor {N : ℕ} (hN : 1≤N) {t : ℕ × ℕ}
    (ht : t ∈ pairSupport N) :
    ∀ p : ℕ,p.Prime → p ∣ t.1*t.2 → smallCap N≤p := by
  have hsmall : (smallCap N : ℝ)≤(t.1 : ℝ) := by
    have hlo := (Finset.mem_filter.mp ht).2.1
    exact (smallCap_le_power N).trans
      ((Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN)
        (by norm_num : (1/100 : ℝ)≤417/5000)).trans hlo)
  have horder : t.1<t.2 := (Finset.mem_filter.mp ht).2.2.1
  intro p hp hpd
  rcases hp.dvd_mul.mp hpd with hp1 | hp2
  · have heq := (Nat.prime_dvd_prime_iff_eq hp (pair_primes ht).1).mp hp1
    rw [heq]
    exact_mod_cast hsmall
  · have heq := (Nat.prime_dvd_prime_iff_eq hp (pair_primes ht).2).mp hp2
    rw [heq]
    exact (by exact_mod_cast hsmall : smallCap N≤t.1).trans horder.le

/-- The small-partner payment itself does not need evenness or G's
masked-tail decomposition.  All its root arithmetic gates are discharged. -/
theorem original_U5_smallPartner_theta_payment {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ t ∈ pairSupport N,∀ s : ℝ,0≤s →
      actualSmallPartnerMass N (rootQ N t) {t.1*t.2} (fun _ => s) (smallCap N)≤
        epsilon*Theta N (rootQ N t) {t.1*t.2} (fun _ => s) := by
  obtain ⟨T,hT,hpay⟩ := actual_smallPartner_theta_payment
    (eta:=1/100) (kappa:=153/256) (rho:=1/100)
    (by norm_num) (by norm_num) (by norm_num) hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT t ht s hs
  have hN4 := hT.trans hNT
  apply hpay N hNT (rootQ N t) {t.1*t.2} (fun _ => s) (smallCap N)
    (root_level_cap (by omega) t) (smallCap_le_power N)
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact pair_product_pos ht
  · intro d hd
    exact hs
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact root_residual_gt_one (by omega) ht
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact root_lowest_cutoff_floor (by omega) ht

/-- One threshold before every genuine U5 pair and every nonnegative mark.
This bounds the actual same-Q all-word switchedCount by the independent
good source with its small-partner loss paid in the exact root Theta_Q. -/
theorem original_U5_switched_good_source_paid {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ t ∈ pairSupport N,∀ s : ℝ,0≤s →
      P2EnhancedTwentyOneChildCorrection.switchedCount N (rootQ N t) {t.1*t.2} (fun _ => s)≤
        actualGoodMass N (rootQ N t) {t.1*t.2} (fun _ => s) (smallCap N)+
          epsilon*Theta N (rootQ N t) {t.1*t.2} (fun _ => s) := by
  obtain ⟨T,hT,hpay⟩ := actual_switched_good_source_paid
    (eta:=1/100) (kappa:=153/256) (rho:=1/100)
    (by norm_num) (by norm_num) (by norm_num) hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he t ht s hs
  have hN4 := hT.trans hNT
  apply hpay N hNT he (rootQ N t) {t.1*t.2} (fun _ => s) (smallCap N)
    (root_level_cap (by omega) t) (smallCap_le_power N) (smallCap_le_power N)
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact pair_product_pos ht
  · intro d hd
    exact hs
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact root_residual_gt_one (by omega) ht
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact root_lowest_cutoff_floor (by omega) ht
  · intro d hd
    rw [Finset.mem_singleton.mp hd]
    exact root_old_prime_floor (by omega) ht

end
end ImbalancedChen.P2OriginalU5SmallPartnerRootPayment
