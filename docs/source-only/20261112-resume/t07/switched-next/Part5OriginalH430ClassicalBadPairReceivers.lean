import ImbalancedChen.Part5OriginalH430ClassicalBadPairPrice
import ImbalancedChen.ChenInitialCorrectionBudget

/-! Finite original Γ5 receivers. Both the unsimplified positive mother
and the purified tested integer fibre are bounded by the same upper
polynomial and its ordinary complete-modulus errors. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairReceivers
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open MathlibNt.SieveTheory.BombieriVinogradov MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2ActualMarkedCountState (rootLevel root_coefficient_full_Q root_level_geometry)
open P2FrozenReceiverCountActions (frozenCarrier frozenCount)
open P2SameQSeedCoprimeMean (finiteAPDiscrepancy finiteMeanShift)
open P5OriginalU5FrozenSource (receiver finiteAPDiscrepancy_eq_actualSource finiteMeanShift_eq_actualSource)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedReceiverRoughPurification (roughReceiver)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430RootRosserSurplus (signedAP frozen_count_plus_surplus surplus_nonneg)
open Part5OriginalH430ClassicalTailBV (receiver_atom_eq_trueLi)
open Part5OriginalH430SeedPurifiedPrimeFibres (fibre rough_receiver_eq_prime_fibre)
open Part5OriginalH430ClassicalBadPairGeometry
open Part5OriginalH430ClassicalBadPairPrice (actual_bad_model_paid)
open scoped Classical BigOperators

def pool (N : ℕ) (τ : ℝ) := (Icc 1 ⌊(N:ℝ)^(1/2-τ)⌋₊).filter (fun k => k.Coprime N)

def trueError (N k : ℕ) : ℝ := |chenQuotientPrimeAPError N (trueLogarithmicIntegral N) k|

def sourceAt (N p : ℕ) (Q : ℝ) (l : List ℕ) : ℝ :=
  ((sourceSieveCarrier N (p*l.prod) (p*N) (cutoff Q p (227/50))).card:ℝ)

private theorem finite_sources {N p : ℕ} {Q : ℝ} {l : List ℕ}
    (hN : 4≤N) (he : Even N) (h : Geometry N p Q l) :
    let D := p*l.prod
    let y := cutoff Q p (227/50)
    let w := cutoff Q D 2
    max (sourceAt N p Q l) (fibre true N D y) ≤
      (frozenCount N D (receiver N) w:ℝ) + (N.primeFactors.card:ℝ) := by
  let D := p*l.prod
  let y := cutoff Q p (227/50)
  let w := cutoff Q D 2
  let F := frozenCarrier N D (receiver N) w
  have hcover : sourceSieveCarrier N D (p*N) y ⊆ F ∪ N.primeFactors := by
    intro e he'
    obtain ⟨her,hpr,hdiv,hs⟩ := mem_filter.mp he'
    by_cases hc : e.Coprime N
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨her,hpr,hdiv,?_⟩,hc⟩
      intro q hq hcop hqw hqd
      have hdv : p*N∣D*N := Nat.mul_dvd_mul_right N (dvd_mul_right p l.prod)
      exact hs q hq (hcop.of_dvd_right hdv) (hqw.trans_le h.cutoff_order.2) hqd
    · exact mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpr,not_not.mp (fun hnot => hc (hpr.coprime_iff_not_dvd.mpr hnot)),by omega⟩)
  have hrcover : roughReceiver N p D y ⊆ F ∪ N.primeFactors := by
    intro e he'
    obtain ⟨he',hrough⟩ := mem_filter.mp he'
    obtain ⟨her,hpr,hdiv,_⟩ := mem_filter.mp he'
    by_cases hc : e.Coprime N
    · apply mem_union_left
      apply mem_filter.mpr
      rw [(source_double_sieve_carriers N D w).1]
      exact ⟨mem_filter.mpr ⟨her,hpr,hdiv,fun q hq _ hqw hqd =>
        (not_lt_of_ge (hrough q hq hqd)) (hqw.trans_le h.cutoff_order.2)⟩,hc⟩
    · exact mem_union_right _ (Nat.mem_primeFactors.mpr
        ⟨hpr,not_not.mp (fun hnot => hc (hpr.coprime_iff_not_dvd.mpr hnot)),by omega⟩)
  change max _ (fibre true N D y) ≤ _
  rw [←rough_receiver_eq_prime_fibre (d:=p) hN he h.big.1]
  refine max_le ?_ ?_
  · exact_mod_cast (card_le_card hcover).trans card_union_le
  · exact_mod_cast (card_le_card hrcover).trans card_union_le

theorem atom_bound {N k : ℕ} (hN : 0<N) (hk : 0<k) (hcop : k.Coprime N) (hlog : 1≤log (N:ℝ)) :
    |finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N k +
      (((chenAdditivePrimeCarrier N).card:ℝ)-logarithmicIntegral N-chenPrimeDivisorCount N k)/(Nat.totient k:ℝ)| ≤
      trueError N k + (3/log 2)*log (N:ℝ) := by
  rw [←finiteAPDiscrepancy_eq_actualSource,←finiteMeanShift_eq_actualSource hcop,receiver_atom_eq_trueLi]
  have hl : 0<log (2:ℝ) := log_pos (by norm_num)
  have hc := (chenCentrePrimeAPCount_le_divisorCount N N k).trans (chenPrimeDivisorCount_le_log N hN)
  have hconst : 0≤(2:ℝ)/log 2 := by positivity
  have hφ : (1:ℝ)≤Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
  have hpos := chenCentrePrimeAPCount_nonneg N N k
  calc
    _ ≤ (trueError N k + |(2/log 2)/(Nat.totient k:ℝ)|) + |chenCentrePrimeAPCount N N k| :=
      (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ _ := by
      rw [abs_of_nonneg (div_nonneg hconst (Nat.cast_nonneg _)),abs_of_nonneg hpos]
      have ha := div_le_self hconst hφ
      have hb := le_mul_of_one_le_right hconst hlog
      have he : (2/log 2)*log (N:ℝ)+log (N:ℝ)/log 2 = (3/log 2)*log (N:ℝ) := by ring
      linarith only [ha,hb,hc,he]

/-- The positive Γ5 mother and its true tested fibre at the original
classical root. The same inclusive unsifted fibre covers their ordinary
model. A complete-modulus signed AP row and the deleted centres remain. -/
theorem actual_classical_bad_row :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (n p : ℕ) (τ : ℝ), 0≤τ → τ≤1/12 →
      1/((n:ℝ)+1)≤11/384 → p∈Part5OriginalH430FrozenClassicalRootModuli.classicalBand N →
      let Q := Part5OriginalH430FrozenIntegerSupport.rootQ N n .U3 τ p
      ∀ l ∈ P2EnhancedBadGamma5ArithmeticGeometry.badLabels N Q p,
        let D := p*l.prod
        let y := cutoff Q p (227/50)
        max (sourceAt N p Q l) (fibre true N D y) -
          (K/4)*thetaConversion N p*fibre false N D y ≤
          signedAP N D Q (cutoff Q D 2)+(N.primeFactors.card:ℝ) := by
  filter_upwards [actual_bad_model_paid,eventually_ge_atTop (4:ℕ)] with N hm hN
  intro he n p τ ht ht' hn hp l hl
  let Q := Part5OriginalH430FrozenIntegerSupport.rootQ N n .U3 τ p
  let D := p*l.prod
  let w := cutoff Q D 2
  have h := actual_pair (by omega) ht ht' hn hp hl
  have hbar := hm he p Q l h
  have hc := finite_sources hN he h
  have hs := root_level_geometry h.child (by norm_num : (1:ℝ)≤2)
  have heq := frozen_count_plus_surplus (N:=N) (p:=D) Q w h.big.2.2
  have hnneg := surplus_nonneg (N:=N) hs.1 hs.2
  dsimp only at hc ⊢
  linarith only [hbar,hc,heq,hnneg]

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairReceivers
