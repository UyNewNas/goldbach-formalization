import ImbalancedChen.P2EnhancedCollisionFloorBound
import ImbalancedChen.P2EnhancedOrderedReciprocalBudget
import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual selected-square collision counts are paid through all original
ordered words and the original sigma(d) weights. The explicit estimate is

  22 (1+log N)^6 N/(eta N^eta) * sum_d sigma(d)/d.

The prefix reciprocal mass is retained. Roughness of the complete
labelled divisor is derived from roughness of the old specified divisor
and the actual positive cutoff for every new prime. It is not supplied as
an assumed enhanced count estimate. All strict source windows remain.

The subsequent lower bound for the SAME Theta_Q, and the enhanced ordinary
signed and K switched-product licences, remain separate obligations.
-/

namespace ImbalancedChen.P2EnhancedCollisionWeightedBudget

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedPrefixMaskDefect P2EnhancedCollisionFloorBound
open P2EnhancedTwentyOneQuotientFinite P2EnhancedOrderedReciprocalBudget
open P2EnhancedTwentyOneSameQWeighted
open scoped Classical

def collisionScale (N d : ℕ) (eta : ℝ) : ℝ :=
  (1 / eta) * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ eta)

theorem collisionScale_nonneg (N d : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 ≤ collisionScale N d eta := by
  unfold collisionScale
  exact div_nonneg (mul_nonneg (one_div_nonneg.mpr heta.le) (Nat.cast_nonneg N))
    (mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (Nat.cast_nonneg N) eta))

/-- A prime divisor of an actual prime list inherits its lower cutoff. -/
theorem list_prime_divisor_lower (l : List ℕ) {r : ℕ} {Y : ℝ}
    (hr : r.Prime) (hdiv : r ∣ l.prod)
    (hlist : ∀ p ∈ l, p.Prime ∧ Y ≤ (p : ℝ)) : Y ≤ (r : ℝ) := by
  revert hdiv hlist
  induction l with
  | nil =>
    intro hdiv _
    exact (hr.not_dvd_one hdiv).elim
  | cons p l ih =>
    intro hdiv hlist
    have hp := hlist p (by simp)
    rcases hr.dvd_mul.mp hdiv with hdp | hdl
    · have heq := (Nat.prime_dvd_prime_iff_eq hr hp.1).mp hdp
      simpa only [heq] using hp.2
    · exact ih hdl (fun q hq => hlist q (by simp [hq]))

/-- Old prefix roughness and actual new-slot lower bounds imply full
labelled-divisor roughness; no distribution or cap assertion is used. -/
theorem complete_product_rough {N d M r : ℕ} {eta a f : ℝ} {l : List ℕ}
    (hd : 0 < d)
    (hold : ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ))
    (hcut : (N : ℝ) ^ eta ≤ a)
    (hl : l ∈ secondFunctionalMotherTuples (primeWindow M a f) r) :
    ∀ q ∈ (d * l.prod).primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ) := by
  have hmem := ((secondFunctionalMother_tuple_mem _ _ _).mp hl).2.2
  intro q hq
  obtain ⟨hprime, hdiv, _⟩ := Nat.mem_primeFactors.mp hq
  rcases hprime.dvd_mul.mp hdiv with hqd | hql
  · exact hold q (Nat.mem_primeFactors.mpr ⟨hprime, hqd, hd.ne'⟩)
  · apply list_prime_divisor_lower l hprime hql
    intro p hp
    have hw := mem_primeWindow.mp (hmem p hp)
    exact ⟨hw.1, hcut.trans hw.2.2.1⟩

/-- The actual prime carrier has a uniform elementary reciprocal budget. -/
theorem window_reciprocal_budget (N M : ℕ) (a f : ℝ) (hupper : f ≤ (N : ℝ)) :
    (∑ p ∈ primeWindow M a f, 1 / (p : ℝ)) ≤ 1 + Real.log N := by
  apply reciprocal_le_one_add_log
  intro p hp
  have hw := mem_primeWindow.mp hp
  exact mem_Icc.mpr ⟨hw.1.one_lt.le, by exact_mod_cast hw.2.2.2.le.trans hupper⟩

/-- Every selected label contributes its complete reciprocal product. -/
theorem collisionPrefixTerm_le {N d M : ℕ} {eta a b c e f : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hold : ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ))
    (hcut : (N : ℝ) ^ eta ≤ a) (hupper : f ≤ (N : ℝ)) (cs : List ℕ) :
    collisionPrefixTerm N d M a b c e f cs ≤
      collisionScale N d eta * (1 + Real.log N) ^ cs.length := by
  let P := primeWindow M a f
  have hscale := collisionScale_nonneg N d heta
  have hrec := tuple_reciprocal_le_power P cs.length
    (window_reciprocal_budget N M a f hupper)
  calc
    collisionPrefixTerm N d M a b c e f cs ≤
        ∑ l ∈ secondFunctionalMotherTuples P cs.length,
          collisionScale N d eta * (1 / (l.prod : ℝ)) := by
      apply sum_le_sum
      intro l hl
      by_cases hc : l.map (secondFunctionalMotherColour b c e) = cs
      · simp only [if_pos hc]
        have hmem := ((secondFunctionalMother_tuple_mem _ _ _).mp hl).2.2
        have hprod : 0 < l.prod := List.prod_pos (fun p hp =>
          (mem_primeWindow.mp (hmem p hp)).1.pos)
        have hb := collision_card_le_power hN he (mul_pos hd hprod) heta
          (complete_product_rough hd hold hcut hl)
        convert hb using 1
        simp only [collisionScale, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [if_neg hc]
        exact mul_nonneg hscale (by positivity)
    _ = collisionScale N d eta *
        ∑ l ∈ secondFunctionalMotherTuples P cs.length, 1 / (l.prod : ℝ) :=
      (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hrec hscale

/-- The entire original switched dictionary, including every occurrence. -/
theorem collisionSwitched_le {N d M : ℕ} {eta a b c e f : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hd : 0 < d) (heta : 0 < eta)
    (hold : ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ))
    (hcut : (N : ℝ) ^ eta ≤ a) (hupper : f ≤ (N : ℝ)) :
    collisionSwitched N d M a b c e f ≤
      collisionScale N d eta * (22 * (1 + Real.log N) ^ 6) := by
  have hword (i : ℕ) :
      ((secondFunctionalMotherGammaWords i).map
        (collisionPrefixTerm N d M a b c e f)).sum ≤
      collisionScale N d eta * ((secondFunctionalMotherGammaWords i).map
        (fun cs => (1 + Real.log N) ^ cs.length)).sum := by
    have h := secondFunctionalMother_list_sum_mono (secondFunctionalMotherGammaWords i)
      (collisionPrefixTerm N d M a b c e f)
      (fun cs => collisionScale N d eta * (1 + Real.log N) ^ cs.length)
      (fun cs _ => collisionPrefixTerm_le hN he hd heta hold hcut hupper cs)
    simpa only [List.sum_map_mul_left] using h
  have h := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (collisionPrefixTerm N d M a b c e f)).sum)
    (fun i => collisionScale N d eta * ((secondFunctionalMotherGammaWords i).map
      (fun cs => (1 + Real.log N) ^ cs.length)).sum) (fun i _ => hword i)
  have hbound : collisionSwitched N d M a b c e f ≤
      collisionScale N d eta * wordBudget (1 + Real.log N) := by
    simpa only [collisionSwitched, wordBudget, List.sum_map_mul_left] using h
  exact hbound.trans (mul_le_mul_of_nonneg_left
    (wordBudget_le_sixth (by linarith [Real.log_natCast_nonneg N]))
    (collisionScale_nonneg N d heta))

/-- The original common-Q physical last cutoff is below N. -/
theorem seed_cutoff_le_N {N d : ℕ} {Q : ℝ} (hd : 0 < d)
    (hQ : Q ≤ (N : ℝ)) (hR : 1 ≤ Q / (d : ℝ)) : cutoff Q d (11/5) ≤ N := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNd : (N : ℝ) ≤ (N : ℝ) * d := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg N)
  have hRupper : Q / (d : ℝ) ≤ N :=
    (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (hQ.trans hNd)
  calc
    cutoff Q d (11/5) ≤ Q / (d : ℝ) := by
      unfold cutoff
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
        (by norm_num : 1 / (11/5 : ℝ) ≤ 1)
    _ ≤ _ := hRupper

/-- Full original sigma-weighted error, with the prefix harmonic mass retained. -/
theorem weightedCollisions_le {N : ℕ} {Q eta : ℝ} (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hN : 4 ≤ N) (he : Even N) (hQ : Q ≤ (N : ℝ)) (heta : 0 < eta)
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hR : ∀ d ∈ D, 1 ≤ Q / (d : ℝ))
    (hold : ∀ d ∈ D, ∀ q ∈ d.primeFactors, (N : ℝ) ^ eta ≤ (q : ℝ))
    (hcut : ∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227/50)) :
    weightedCollisions N Q D sigma ≤
      (22 * (1 + Real.log N) ^ 6 * (1 / eta) * (N : ℝ) / (N : ℝ) ^ eta) *
        ∑ d ∈ D, sigma d / (d : ℝ) := by
  calc
    weightedCollisions N Q D sigma ≤
        ∑ d ∈ D, sigma d *
          (collisionScale N d eta * (22 * (1 + Real.log N) ^ 6)) := by
      apply sum_le_sum
      intro d hmem
      apply mul_le_mul_of_nonneg_left _ (hsigma d hmem)
      exact collisionSwitched_le hN he (hd d hmem) heta (hold d hmem) (hcut d hmem)
        (seed_cutoff_le_N (hd d hmem) hQ (hR d hmem))
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      simp only [collisionScale, div_eq_mul_inv, mul_inv_rev]
      ring

end
end ImbalancedChen.P2EnhancedCollisionWeightedBudget
