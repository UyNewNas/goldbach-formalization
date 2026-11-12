import ImbalancedChen.Part5OriginalH430ClassicalLargePrimeTuples
import ImbalancedChen.Part5OriginalH430ClassicalBadPairCredit

/-! Apply the long-word purification and small-product payment to the
same E_p+S_p on which the original Γ5 price was already paid. All
complete colour labels and all original non-switched terms remain. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalClampLongCredit
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open P2EnhancedReceiverRoughPurification (repeatWordMass centerWordMass)
open P2EnhancedExactExceptionFinite (badPairRepeat badPairCenter)
open P2EnhancedExactExceptionTheta (localErrors weightedErrors exact_errors_theta_payment)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430TaggedArithmeticReceivers (original_band_prime)
open Part5OriginalH430OriginalRootQBound (original_root_Q_le_target)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment (clamp_subset_classical)
open Part5OriginalH430SeedThirteenPrimeWords (longPrime primeWord)
open Part5OriginalH430SeedPurifiedPrimeFibres (wordFibre prime_word_purified)
open Part5OriginalH430ClassicalCausalSeedScale
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSwitchedSmallPayment
open Part5OriginalH430ClassicalInclusiveLongMass (longFibre)
open Part5OriginalH430ClassicalRootCredits (cubeCredit)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430ClassicalBadPairCredit (otherSeedTerms badPrice original_clamp_credit_after_Gamma5)
open scoped Classical Topology BigOperators

private theorem root_position (N n p : ℕ) (τ : ℝ) :
    ∃ l : LevelIndex N n .U3 τ p 430,
      levelOccurrence l=origin 430 (rootRequest N n .U3 τ p) ∧ wordProduct l=p := by
  let o : Occurrence N := origin 430 (rootRequest N n .U3 τ p)
  have ho : o∈rootHistory N n .U3 τ p := List.mem_cons_self
  have hm : o∈levelRequests N n .U3 τ p 430 := List.mem_filter.mpr ⟨ho,rfl⟩
  obtain ⟨l,hl⟩ := List.mem_iff_get.mp hm
  have hl' : levelOccurrence l=o := hl
  exact ⟨l,hl',by simp only [wordProduct,hl',o,origin,rootRequest,parentProduct,List.prod_cons,List.prod_nil,mul_one]⟩

private theorem long_prime_purification {N d : ℕ} (Q : ℝ) (hN : 4≤N) (he : Even N) (hd : 0<d) :
    longPrime N Q d≤longFibre true N Q d+localErrors N Q d := by
  have h := sum_le_sum (s:=univ) (fun (j : Fin 13) _ => secondFunctionalMother_list_sum_mono
    (secondFunctionalMotherGammaWords (9+j.val)) (primeWord N Q d)
    (fun cs => wordFibre true N Q d cs+(repeatWordMass N Q d cs+centerWordMass N Q d cs))
    (fun cs _ => by linarith only [prime_word_purified Q hN he hd cs]))
  have hp : 0≤badPairRepeat N Q d := by unfold badPairRepeat; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hc : 0≤badPairCenter N Q d := by unfold badPairCenter; exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  unfold longPrime longFibre localErrors
  simp only [List.sum_map_add,sum_add_distrib] at h ⊢
  linarith only [hp,hc,h]

/-- Pointwise in the external classical p, since only a fixed-power
error and the already paid prime-centre/repeat errors are absorbed.
The assertion leaves the entire nontrivial large prime test on the right. -/
theorem classical_long_prime_to_large {κ ε : ℝ} (hk : 0<κ) (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (τ : ℝ) (p : ℕ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈classicalBand N →
      let Q := rootQ N n .U3 τ p
      longPrime N Q p≤allLarge true N Q p (smallProduct N κ)+ε*thetaAtom N Q p := by
  obtain ⟨Ta,h4,ha⟩ := small_both_atoms hk (half_pos he)
  obtain ⟨Tb,_,hb⟩ := exact_errors_theta_payment frozenLeafCutoffFloor_pos (half_pos he)
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN heven n τ p ht ht' hn hp
  let Q := rootQ N n .U3 τ p
  let X := smallProduct N κ
  have hN4 := h4.trans ((le_max_left Ta Tb).trans hN)
  have h2 : 2≤N := by omega
  have hband := (mem_filter.mp hp).1
  have hpp := (original_band_prime hband).1.pos
  have hQ := original_root_Q_le_target N n .U3 τ p h2 ht ht' hband
  obtain ⟨l,hl,hd⟩ := root_position N n p τ
  have hgeo := actual_cubic_residual h2 ht ht' hn hp l
  dsimp only at hgeo
  rw [hd] at hgeo
  have hrough := history_integer_roughness h2 ht ht' hn hband (levelOccurrence_source l).1
  have hfp : (∀ q∈p.primeFactors,(N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
      (N:ℝ)^frozenLeafCutoffFloor≤cutoff Q p (227/50) := by
    have hh : (∀ q∈(wordProduct l).primeFactors,(N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
        (N:ℝ)^frozenLeafCutoffFloor≤cutoff Q (wordProduct l) (227/50) := hrough.2.2
    simpa only [hd] using hh
  have hlocal := hb N ((le_max_right Ta Tb).trans hN) heven Q ({p}:Finset ℕ) (fun _ => (1:ℝ))
    hQ (fun x hx => (mem_singleton.mp hx).symm ▸ hpp) (fun _ _ => zero_le_one)
    (fun x hx => (mem_singleton.mp hx).symm ▸ hgeo.2.1)
    (fun x hx => (mem_singleton.mp hx).symm ▸ hfp.1)
    (fun x hx => (mem_singleton.mp hx).symm ▸ hfp.2)
  simp only [weightedErrors,Theta_eq_sum_atoms,sum_singleton,one_mul] at hlocal
  have hsmall := (ha N ((le_max_left Ta Tb).trans hN) Q p hpp hQ hgeo.2.2.1).1
  have hpur := long_prime_purification (d:=p) Q hN4 heven hpp
  have hsp := all_parts true N Q p X
  change longFibre true N Q p=allSmall true N Q p X+allLarge true N Q p X at hsp
  dsimp only
  linarith only [hlocal,hsmall,hpur,hsp]

/-- At the original positive-width clamp, Γ5 has its proved untested
price. The old longPrime term is replaced by the genuine large-product
test. The ε is charged once to the original clamp mass. -/
theorem original_E_and_S_after_small_switches {τ κ ε : ℝ}
    (ht : 0<τ) (ht' : τ≤1/12) (hk : 0<κ) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ,1/((n:ℝ)+1)≤11/384 →
      5*(clampMass N n τ-∑ p∈clampPrimes N,cubeCredit N n p τ)≤
        (∑ p∈clampPrimes N,let Q:=rootQ N n .U3 τ p
          (otherSeedTerms N p Q-longPrime N Q p)+badPrice N p Q+
            allLarge true N Q p (smallProduct N κ))+ε*clampMass N n τ := by
  obtain ⟨T,h4,ha⟩ := classical_long_prime_to_large hk (half_pos he)
  filter_upwards [eventually_ge_atTop T,original_clamp_credit_after_Gamma5 ht ht' (half_pos he)]
    with N hN hb
  intro heven n hn
  let Q := fun p => rootQ N n .U3 τ p
  let X := smallProduct N κ
  have hh := hb heven n hn
  have hrow (p : ℕ) (hp : p∈clampPrimes N) :
      otherSeedTerms N p (Q p)+badPrice N p (Q p)≤
        (otherSeedTerms N p (Q p)-longPrime N (Q p) p)+badPrice N p (Q p)+allLarge true N (Q p) p X+
          (ε/2)*thetaAtom N (Q p) p := by
    have h := ha N hN heven n τ p ht.le ht' hn (clamp_subset_classical (by omega : 2≤N) hp)
    dsimp only at h
    linarith only [h]
  have hs := sum_le_sum (s:=clampPrimes N) hrow
  have hsum : (∑ p∈clampPrimes N,
      (otherSeedTerms N p (Q p)-longPrime N (Q p) p)+badPrice N p (Q p)+allLarge true N (Q p) p X+
        (ε/2)*thetaAtom N (Q p) p) =
      (∑ p∈clampPrimes N,(otherSeedTerms N p (Q p)-longPrime N (Q p) p)+badPrice N p (Q p)+
        allLarge true N (Q p) p X)+(ε/2)*clampMass N n τ := by
    rw [sum_add_distrib,←mul_sum] <;> rfl
  rw [hsum] at hs
  dsimp only at hh ⊢
  linarith only [hh,hs]

end
end ImbalancedChen.Part5OriginalH430ClassicalClampLongCredit
