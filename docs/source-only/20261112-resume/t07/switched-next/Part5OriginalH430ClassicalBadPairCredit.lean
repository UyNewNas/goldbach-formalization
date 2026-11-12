import ImbalancedChen.Part5OriginalH430ClassicalBadPairPayment
import ImbalancedChen.Part5OriginalH430ClassicalRootH430Boundary

/-! First directed use on the physical cube surplus and the first-prime
shell of the original U3 clamp. The other seed terms are literal counts. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairCredit
noncomputable section
open Finset Filter Real Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff localQuotient localCollisions localBadPrimes local_sameQ_finite)
open P2EnhancedTwentyOneQuotientFinite (quotientLocal)
open P2EnhancedTwentyOneChildCorrection (localPositivePairs localSwitched)
open P2ActualSameQTwentyOnePositiveSourceBinding (actual_local_source_identity)
open P2OriginalW2ComplementAction P2OriginalW2CountTupleReindex P2OriginalW2MotherOccurrenceReindex
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2EnhancedSwitchedUnsiftedSource (originalBadPairCount)
open P2FrozenReceiverCountActions (frozenCount frozenCarrier)
open P5OriginalU5FrozenSource (receiver frozenCount_eq_original_count)
open P5OriginalActionMassBound (originalW2At)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430TaggedArithmeticReceivers (originalReceiver original_band_prime)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment (clamp_subset_classical)
open Part5OriginalH430SeedThirteenPrimeWords (longPrime restrictedPrime mother_positive_split)
open Part5OriginalH430SelectedOrdinaryPairCounts (actualState)
open Part5OriginalH430SeedPurifiedPrimeFibres (badFibre)
open Part5OriginalH430ClassicalBadPairPayment
open Part5OriginalH430ClassicalRootCredits (cubeCredit)
open Part5OriginalH430ClassicalRootH430Boundary (rootDifference actual_classical_and_clamp_distance)
open scoped Classical Topology BigOperators

/-- The two anchors; the three original negative singles; all four good
pair lanes; the thirteen positive long lanes and the original errors.
The independent Γ5 price is inserted in the final theorem. -/
def otherSeedTerms (N p : ℕ) (Q : ℝ) : ℝ :=
  let y := cutoff Q p (227/50)
  let z₁ := cutoff Q p (353/100)
  let z₂ := cutoff Q p (29/10)
  let z₃ := cutoff Q p (61/25)
  let z := cutoff Q p (11/5)
  4*(sourceSieveCount N p (p*N) y:ℝ)+(sourceSieveCount N p (p*N) z₁:ℝ)-
    fourthRowMotherSingle N p N y z-fourthRowMotherSingle N p N y z₂-fourthRowMotherSingle N p N y z₃+
    (∑ k : Fin 4,sourceGoodOccurrence N Q (actualState N) p (originalW2At 0) k)+longPrime N Q p+
    W2Charge N Q p 0+localCollisions N Q p+localBadPrimes N Q p

def badPrice (N p : ℕ) (Q : ℝ) : ℝ :=
  (K/4)*thetaConversion N p*badFibre false N Q p

private theorem original_count_le_seed {N n p : ℕ} {τ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈clampPrimes N) :
    ((originalReceiver N p).card:ℝ)≤
      (sourceSieveCount N p (p*N) (cutoff (rootQ N n .U3 τ p) p (11/5)):ℝ) := by
  let Q := rootQ N n .U3 τ p
  let z := cutoff Q p (11/5)
  have hb := clamp_subset_classical hN hp
  have hpp := original_band_prime (mem_filter.mp hb).1
  have hcl := classical_geometry (m:=0) hN ht ht' hn hb
  have hNr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hR : Q/(p:ℝ)≤(N:ℝ)^(1/2-clampStart) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hpp.1.pos)).mpr
    calc
      _ ≤ (N:ℝ)^(1/2:ℝ) := hcl.2.2.trans (rpow_le_rpow_of_exponent_le hNr (by linarith))
      _ = (N:ℝ)^(1/2-clampStart)*(N:ℝ)^clampStart := by rw [←rpow_add hN0]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (mem_filter.mp hp).2 (rpow_nonneg hN0.le _)
  have hz : z≤(N:ℝ)^a := by
    calc
      _ ≤ ((N:ℝ)^(1/2-clampStart))^(1/(11/5):ℝ) :=
        rpow_le_rpow (zero_lt_one.trans hcl.1).le hR (by norm_num)
      _ ≤ _ := by
        rw [←rpow_mul hN0.le]
        exact rpow_le_rpow_of_exponent_le hNr (by norm_num [clampStart,a])
  have hrough : ChenPrimeRough ((N:ℝ)^a) p := by
    intro q hq hqp
    rw [(Nat.prime_dvd_prime_iff_eq hq hpp.1).mp hqp]
    exact (mem_filter.mp (mem_filter.mp hb).1).2.1
  have hsub : frozenCarrier N p (receiver N) ((N:ℝ)^a) ⊆ sourceSieveCarrier N p (p*N) z := by
    intro e he
    obtain ⟨hr,hpr,hdiv,hs⟩ := mem_filter.mp (mem_filter.mp he).1
    exact mem_filter.mpr ⟨hr,hpr,hdiv,fun q hq hcop hlow => hs q hq hcop (hlow.trans_le hz)⟩
  change ((chenSiftedQuotientPrimeSource N p ((N:ℝ)^a)).card:ℝ)≤_
  rw [←frozenCount_eq_original_count N p ((N:ℝ)^a) hrough]
  exact_mod_cast card_le_card hsub

private theorem real_one_step {N n p : ℕ} {τ : ℝ} (hN : 4≤N) (he : Even N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈clampPrimes N) :
    let Q := rootQ N n .U3 τ p
    5*((originalReceiver N p).card:ℝ) ≤ otherSeedTerms N p Q+originalBadPairCount N Q p := by
  let Q := rootQ N n .U3 τ p
  have hb := clamp_subset_classical (by omega) hp
  have hpp := original_band_prime (mem_filter.mp hb).1
  have hR := (classical_geometry (m:=0) (by omega) ht ht' hn hb).1
  have hroot := original_count_le_seed (by omega) ht ht' hn hp
  have hseed := local_sameQ_finite N Q p hR.le
  have hpos := mother_positive_split hN he hpp.1.pos hR
  rw [←actual_local_source_identity Q hN he hpp.1.pos] at hpos
  dsimp only [localQuotient,quotientLocal] at hseed
  dsimp only [localPositivePairs,localSwitched,restrictedPrime] at hpos
  dsimp only [otherSeedTerms]
  linarith only [hroot,hseed,hpos]

/-- Directed lower estimate for the actual sum of E_p+S_p. The bad
positive Γ5 prime count has been paid at its original converted integer
price. The signed budget still displays every other term of this seed. -/
theorem original_clamp_credit_after_Gamma5 {τ ε : ℝ} (ht : 0<τ) (ht' : τ≤1/12) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1)≤11/384 →
      5*(clampMass N n τ-∑ p∈clampPrimes N,cubeCredit N n p τ) ≤
        (∑ p∈clampPrimes N, let Q := rootQ N n .U3 τ p
          otherSeedTerms N p Q+badPrice N p Q)+ε*clampMass N n τ := by
  filter_upwards [actual_Gamma5_at_common_mass ht ht' (half_pos he),
    actual_classical_and_clamp_distance ht ht' (show 0<ε/10 by positivity),
    eventually_ge_atTop (4:ℕ)] with N hg hd hN
  intro heven n hn
  let B := clampPrimes N
  let Q := fun p => rootQ N n .U3 τ p
  let C := fun p : ℕ => ((originalReceiver N p).card:ℝ)
  have hseed := sum_le_sum (s:=B) (fun p hp => real_one_step hN heven ht.le ht' hn hp)
  change (∑ p∈B,5*C p)≤∑ p∈B,(otherSeedTerms N p (Q p)+originalBadPairCount N (Q p) p) at hseed
  rw [←mul_sum,sum_add_distrib] at hseed
  have hpool := hg heven n hn B (clamp_subset_classical (by omega))
  have hpay := (sum_le_sum (s:=B) (fun p _ => show
    originalBadPairCount N (Q p) p-badPrice N p (Q p)≤originalDebt N p (Q p) from
    sub_le_sub_right (le_max_left _ _) _)).trans hpool
  rw [sum_sub_distrib] at hpay
  have hdiff (p : ℕ) : thetaAtom N (Q p) p-cubeCredit N n p τ ≤ C p+|rootDifference N n p τ| := by
    have h := neg_le_abs (rootDifference N n p τ)
    change -(C p+cubeCredit N n p τ-thetaAtom N (Q p) p) ≤ _ at h
    linarith only [h]
  have hab := sum_le_sum (s:=B) (fun p _ => hdiff p)
  rw [sum_sub_distrib,sum_add_distrib] at hab
  change clampMass N n τ-(∑ p∈B,cubeCredit N n p τ)≤(∑ p∈B,C p)+
    ∑ p∈B,|rootDifference N n p τ| at hab
  have herr := (hd heven n hn).2
  change 5*(clampMass N n τ-(∑ p∈B,cubeCredit N n p τ))≤
    (∑ p∈B,(otherSeedTerms N p (Q p)+badPrice N p (Q p)))+ε*clampMass N n τ
  rw [sum_add_distrib]
  linarith only [hab,hseed,hpay,herr]

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairCredit
