import ImbalancedChen.Part5OriginalH430StrictCutoffTransfer
import ImbalancedChen.P1ActualMovingPrimeIntervalEnvelope
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization
import U8TwoLogDenominator
import U8OptimalPrefix

/-! An ordinary and rejected sieve-window majorant for the original additive
prime. The two-linear leading coefficient is the actual Bq. Its small primes
are excluded by physical roughness. No prime distribution estimate for an
individual Bq, or relative lower bound on a parent vertex, is assumed. -/
namespace ImbalancedChen.Part5OriginalH430RoughCutoffSelberg

noncomputable section
open Finset Filter Set MathlibNt.SieveTheory
open scoped Classical BigOperators Topology
open U8Literal.SmallProduct U8Literal.SmallProduct.TwoDimensional
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open Wu2008DoubleSieve
open P2FrozenReceiverCountActions (frozenCount frozenCarrier)
open P5OriginalU5FrozenSource (receiver frozenCarrier_eq_original_labels)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P1ActualMovingPrimeIntervalEnvelope

private theorem roots_of_rough {d m N : ℕ} {Z : ℝ}
    (hd : ChenPrimeRough Z d) (hm : m ∣ (sievePrimes Z).prod id) :
    residueRootCount m N d = nuN N m := by
  rw [residueRootCount_squarefree ((sievePrimes_prod_squarefree Z).squarefree_of_dvd hm),nuN]
  apply prod_congr rfl
  intro p hp
  have hP := Nat.prime_of_mem_primeFactors hp
  have hD := Nat.dvd_trans (Nat.dvd_of_mem_primeFactors hp) hm
  obtain ⟨q,hq,hpq⟩ := (hP.prime.dvd_finsetProd_iff id).mp hD
  have he := ((mem_sievePrimes.mp hq).1.eq_one_or_self_of_dvd p hpq).resolve_left hP.ne_one
  have hZ : (p:ℝ) < Z := by simpa [he] using (mem_sievePrimes.mp hq).2
  have hn : ¬p ∣ d := fun h => (not_lt_of_ge (hd p hP h)) hZ
  have : Fact p.Prime := ⟨hP⟩
  rw [residueRootCount_prime]
  by_cases hc : p ∣ N
  · rw [if_pos hc,localRoots_card_one_of_dvd_N hn hc]
  · rw [if_neg hc,localRoots_card_two hn hc]

private theorem rough_quadratic {N d : ℕ} {Z R : ℝ} (hN : Even N)
    (hd : ChenPrimeRough Z d) (hR : 1≤R) :
    quadratic N 1 (d,1) (carrier Z R) (optimalWeight N hN Z R) =
      ((interval N 1 (d,1)).card:ℝ)/denominator N Z R +
      quadraticRemainder N 1 (d,1) (carrier Z R) (optimalWeight N hN Z R) := by
  rw [quadratic_eq_main_add_remainder]
  have HM :
      (∑ a ∈ carrier Z R, ∑ b ∈ carrier Z R,
        optimalWeight N hN Z R a * optimalWeight N hN Z R b *
        (residueRootCount (Nat.lcm a b) N (d*1):ℝ)/Nat.lcm a b) =
        mainMatrix N Z R (optimalWeight N hN Z R) := by
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    rw [Nat.mul_one,roots_of_rough hd (Nat.lcm_dvd (carrier_dvd ha) (carrier_dvd hb)),
      nuN_cast_eq_rootCount]
  rw [HM,mainMatrix_optimal N hN Z hR]
  ring

private def large (N d : ℕ) (Z : ℝ) := (frozenCarrier N d (receiver N) Z).filter
  (fun ell => Z ≤ (ell:ℝ))

private def crossed (N d : ℕ) (Z : ℝ) := (interval N 1 (d,1)).filter
  (fun m => (twoLinear N (d,1) m).Coprime ((sievePrimes Z).prod id))

private theorem large_card {N d : ℕ} {Z : ℝ} (hd : ChenPrimeRough Z d) :
    (large N d Z).card ≤ (crossed N d Z).card := by
  let f := fun ell : ℕ => (N-ell)/d
  have data {ell : ℕ} (he : ell ∈ large N d Z) :
      ell ∈ chenQuotientPrimeCarrier N d ∧ ChenPrimeRough Z (f ell) ∧ Z ≤ ell := by
    obtain ⟨he,hZ⟩ := mem_filter.mp he
    rw [frozenCarrier_eq_original_labels N d Z hd] at he
    obtain ⟨hp,hdv,hr⟩ := mem_filter.mp he
    exact ⟨mem_chenQuotientPrimeCarrier.mpr ⟨hp,hdv⟩,hr,hZ⟩
  have hsub : (large N d Z).image f ⊆ crossed N d Z := by
    intro m hm
    obtain ⟨ell,he,rfl⟩ := mem_image.mp hm
    obtain ⟨hsrc,hr,hZ⟩ := data he
    obtain ⟨hadd,hdv⟩ := mem_chenQuotientPrimeCarrier.mp hsrc
    obtain ⟨hl,hp,_⟩ := mem_chenAdditivePrimeCarrier.mp hadd
    have hmul : d*(f ell) = N-ell := Nat.mul_div_cancel' hdv
    have hquo : f ell ∈ chenQuotientPrimeSource N d := mem_image.mpr ⟨ell,hsrc,rfl⟩
    have hinfo := chenQuotientPrimeSource_data hquo
    have ht : d*1*f ell < N := by rw [Nat.mul_one,hmul]; omega
    have hout : N-d*1*f ell = ell := by rw [Nat.mul_one,hmul]; omega
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hinfo.1,ht,?_⟩,?_⟩
    · simpa using (show ((d*1*f ell:ℕ):ℝ)≤N by exact_mod_cast ht.le)
    · apply Nat.coprime_prod_right_iff.mpr
      intro p hpr
      obtain ⟨hpr,hpZ⟩ := mem_sievePrimes.mp hpr
      have hm : ¬p ∣ f ell := fun h => (not_lt_of_ge (hr p hpr h)) hpZ
      have hne : p < ell := by exact_mod_cast hpZ.trans_le hZ
      change (f ell * (N-d*1*f ell)).Coprime p
      rw [hout]
      exact (hpr.coprime_iff_not_dvd.mpr hm).symm.mul_left
        (Nat.coprime_of_lt_prime hpr.ne_zero hne hp)
  have hinj : Set.InjOn f (large N d Z : Set ℕ) :=
    fun _ hx _ hy h => chenQuotientPrimeSource_injective (data hx).1 (data hy).1 h
  rw [← card_image_of_injOn hinj]
  exact card_le_card hsub

private theorem interval_size {N d : ℕ} (hd : 0<d) :
    ((interval N 1 (d,1)).card:ℝ) ≤ (N:ℝ)/d := by
  have hsub : interval N 1 (d,1) ⊆ Icc 1 (N/d) := by
    intro m hm
    obtain ⟨_,hm,hl,_⟩ := mem_filter.mp hm
    have hdm : m*d ≤ N := by simpa [Nat.mul_comm] using hl.le
    exact mem_Icc.mpr ⟨hm,(Nat.le_div_iff_mul_le hd).mpr hdm⟩
  have hcard : (interval N 1 (d,1)).card ≤ N/d := by simpa using card_le_card hsub
  apply (le_div_iff₀ (Nat.cast_pos.mpr hd : 0<(d:ℝ))).mpr
  exact_mod_cast (Nat.mul_le_mul_right d hcard).trans (Nat.div_mul_le_self N d)

/-- Explicit dimension-two upper bound for every actual receiver submask and
all rough old products, with its small-output and CRT errors visible. -/
theorem actual_frozen_selberg {N d : ℕ} {Z R z : ℝ} (hN : Even N) (hd : 0<d)
    (hr : ChenPrimeRough Z d) (hR : 1≤R) (hz : Z≤z) {E : ℕ → Prop}
    (hE : ∀ ell, E ell → receiver N ell) :
    (frozenCount N d E z:ℝ) ≤ (N:ℝ)/d / denominator N Z R +
      ((⌈Z⌉₊:ℕ):ℝ) + 2*(R+1)^2*R^4 := by
  have hsub : frozenCarrier N d E z ⊆ frozenCarrier N d (receiver N) Z := by
    unfold frozenCarrier
    rw [(source_double_sieve_carriers N d z).1,(source_double_sieve_carriers N d Z).1]
    intro ell h
    obtain ⟨hraw,he⟩ := mem_filter.mp h
    obtain ⟨hl,hp,hdiv,hs⟩ := mem_filter.mp hraw
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hl,hp,hdiv,
      fun q hq hc hqZ => hs q hq hc (hqZ.trans_le hz)⟩,hE ell he⟩
  have hcov : frozenCarrier N d (receiver N) Z ⊆ range ⌈Z⌉₊ ∪ large N d Z := by
    intro ell he
    by_cases h : (ell:ℝ)<Z
    · exact mem_union_left _ (mem_range.mpr ((Nat.lt_ceil).mpr h))
    · exact mem_union_right _ (mem_filter.mpr ⟨he,le_of_not_gt h⟩)
  have hhead : (frozenCarrier N d E z).card ≤ ⌈Z⌉₊ + (crossed N d Z).card := by
    calc
      _ ≤ (range ⌈Z⌉₊ ∪ large N d Z).card := card_le_card (hsub.trans hcov)
      _ ≤ _ := (card_union_le _ _).trans (by rw [card_range]; exact Nat.add_le_add_left (large_card hr) _)
  have hs : ((crossed N d Z).card:ℝ) ≤
      quadratic N 1 (d,1) (carrier Z R) (optimalWeight N hN Z R) := by
    rw [← square_eq_quadratic]
    calc
      _ = ∑ _m ∈ crossed N d Z, (1:ℝ) := by simp
      _ = ∑ m ∈ crossed N d Z, (divisorSum (carrier Z R) (optimalWeight N hN Z R)
            (twoLinear N (d,1) m))^2 := by
        apply sum_congr rfl
        intro m hm
        rw [divisorSum_eq_one (carrier_one hR) (fun _ h => carrier_dvd h)
          (optimalWeight_one N hN Z hR) (mem_filter.mp hm).2,one_pow]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)
  rw [rough_quadratic hN hr hR] at hs
  have hp : 0 < denominator N Z R := by
    rw [← denominator_eq N hN]
    exact TruncatedSelberg.G_pos _ hR
  have hmain := div_le_div_of_nonneg_right (interval_size (N:=N) hd) hp.le
  have herr := (le_abs_self _).trans (optimal_remainder_bound N hN 1 Z R (d,1) hR)
  have hh : ((frozenCarrier N d E z).card:ℝ) ≤ ((⌈Z⌉₊:ℕ):ℝ) + (crossed N d Z).card := by
    exact_mod_cast hhead
  change (((frozenCarrier N d E z).card:ℕ):ℝ) ≤ _
  linarith only [hh,hs,hmain,herr]

/-- Finite normalized version. The denominator bound is supplied by the
pinned varying-even-centre theorem simultaneously for all these Bq and z. -/
theorem actual_frozen_two_log {beta : ℝ} (hb : 0<beta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (d : ℕ) (Z z : ℝ) (E : ℕ → Prop),
      0<d → (N:ℝ)^beta < Z → ChenPrimeRough Z d → Z≤z →
      (∀ ell, E ell → receiver N ell) →
      (frozenCount N d E z:ℝ) ≤
        (N:ℝ)/d * ((64/beta^2)*SingularSeries.liuSingularSeries N/(Real.log N)^2) +
        ((⌈Z⌉₊:ℕ):ℝ) + 2*((N:ℝ)^beta+1)^2*((N:ℝ)^beta)^4 := by
  filter_upwards [eventually_denominator_two_log hb,eventually_ge_atTop (2:ℕ)] with N hh hN
  intro hev d Z z E hd hZ hr hz hE
  have hR := Real.one_le_rpow (by exact_mod_cast (show 1≤N by omega)) hb.le
  have hm := optimal_main_le_two_log hev hb (by omega : 1<N) (hh hev Z hZ)
  rw [mainMatrix_optimal N hev Z hR] at hm
  have hpos : 0≤(N:ℝ)/d := by positivity
  have hp := mul_le_mul_of_nonneg_left hm hpos
  have hf := actual_frozen_selberg hev hd hr hR hz hE
  have heq : (N:ℝ)/d / denominator N Z ((N:ℝ)^beta) =
      (N:ℝ)/d*(1/denominator N Z ((N:ℝ)^beta)) := by ring
  rw [heq] at hf
  linarith only [hp,hf]

/-- The original half-open prime window, with its centre and B-deletions, is
bounded uniformly in its two moving exponents before any history is chosen. -/
theorem moving_prime_window :
    ∃ K : ℝ, 1<K ∧ ∀ (N B : ℕ), 1<N → ∀ (a lo hi : ℝ),
      0<a → a≤lo → lo≤hi → hi≤1 → 3≤(N:ℝ)^a →
      (∑ q ∈ primeWindow (B*N) ((N:ℝ)^lo) ((N:ℝ)^hi), 1/(q:ℝ)) ≤
        (hi-lo)/a + K/(a^2*Real.log N) := by
  obtain ⟨K,hK,hin⟩ := exists_uniform_exponent_window_envelope
  refine ⟨K,hK,?_⟩
  intro N B hN a lo hi ha hl ho hhi hfloor
  have hsub : primeWindow (B*N) ((N:ℝ)^lo) ((N:ℝ)^hi) ⊆
      roughPrimeFinset N (Nat.ceil ((N:ℝ)^hi)) ((N:ℝ)^lo) ((N:ℝ)^hi) := by
    intro q hq
    obtain ⟨hp,hcop,hl,hr⟩ := mem_primeWindow.mp hq
    exact (mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)).mpr
      ⟨hp,hp.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp hcop).2,hl,hr⟩
  calc
    _ ≤ ∑ q ∈ primeWindow (B*N) ((N:ℝ)^lo) ((N:ℝ)^hi), 1/((q:ℝ)-1) := by
      apply sum_le_sum
      intro q hq
      have hp : (1:ℝ)<q := by exact_mod_cast (mem_primeWindow.mp hq).1.one_lt
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    _ ≤ actualPrimeReciprocalMass N lo hi := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro q hq _
      have hp : (1:ℝ)<q := by exact_mod_cast (mem_roughPrimeFinset.mp hq).2.1.one_lt
      positivity
    _ ≤ _ := by simpa using hin N hN a 1 lo hi ha hl ho hhi hfloor


private theorem true_atom_scale {N B : ℕ} {Q : ℝ} (hN : 4≤N) (hB : 0<B)
    (hQ : 1<Q/(B:ℝ)) (hQ' : Q/(B:ℝ)≤N) :
    SingularSeries.liuSingularSeries N * (N:ℝ) / ((B:ℝ)*(Real.log N)^2)
      ≤ thetaAtom N Q B := by
  have hNp : 0<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hlog := Real.log_pos hNr
  have hL := Real.log_pos hQ
  have hLb := Real.log_le_log (zero_lt_one.trans hQ) hQ'
  have hS := wuSingularSeries_pos N hNp
  have hS' := wuSingularSeries_le_mul (N:=N) (d:=B) hNp hB
  have hb : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have hphi : (0:ℝ)<Nat.totient B := Nat.cast_pos.mpr (Nat.totient_pos.mpr hB)
  have hphiB : (Nat.totient B:ℝ)≤B := by exact_mod_cast Nat.totient_le B
  rw [← wuSingularSeries_eq_liu N hNp]
  change _ ≤ 4*logarithmicIntegral N * (wuSingularSeries (B*N) /
    ((Nat.totient B:ℝ)*Real.log (Q/(B:ℝ))))
  calc
    _ ≤ 4*((N:ℝ)/(2*Real.log N))*(wuSingularSeries N/((B:ℝ)*Real.log N)) := by
      field_simp [hb.ne',hlog.ne']; nlinarith [mul_nonneg hS.le (Nat.cast_nonneg N)]
    _ ≤ _ := by gcongr <;> first | assumption | exact box_trueLi_lower hN | positivity

open P2EnhancedLowerPhysicalNode P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback Part5OriginalH430SelectedMemberBox
open Part5OriginalH430HistoryQuotientCounts Part5OriginalH430AllLaneMemberQuery
open Part5OriginalH430StrictCutoffTransfer

def sieveError (N : ℕ) (beta Z : ℝ) : ℝ :=
  ((⌈Z⌉₊:ℕ):ℝ) + 2*((N:ℝ)^beta+1)^2*((N:ℝ)^beta)^4

private theorem rough_prime_mul {B q : ℕ} {Z : ℝ} (hB : ChenPrimeRough Z B)
    (hq : q.Prime) (hZ : Z ≤ q) : ChenPrimeRough Z (B*q) := by
  intro r hr hdiv
  rcases hr.dvd_mul.mp hdiv with h | h
  · exact hB r hr h
  · rw [((hq.eq_one_or_self_of_dvd r h).resolve_left hr.ne_one)]
    exact hZ

/-- Uniform letter-wise majorization at the same parent theta. All assumptions
besides N belong to the geometry of the physical window. Both endpoint
errors are included with the original B and contain no unknown prime count. -/
theorem finite_parent_window {beta : ℝ} (hb : 0<beta) :
    ∃ K : ℝ, 1<K ∧ ∀ᶠ N : ℕ in atTop, Even N → ∀ (B : ℕ) (Q a lo hi Z : ℝ)
      (E : ℕ → Prop), 0<B → 1<Q/(B:ℝ) → Q/(B:ℝ)≤N →
      0<a → a≤lo → lo≤hi → hi≤1 → 3≤(N:ℝ)^a →
      (N:ℝ)^beta < Z → Z≤(N:ℝ)^lo → (N:ℝ)^hi≤Q/(B:ℝ) →
      ChenPrimeRough Z B → (∀ ell,E ell → receiver N ell) →
      (∑ q ∈ primeWindow (B*N) ((N:ℝ)^lo) ((N:ℝ)^hi),
        (frozenCount N (B*q) E (q:ℝ):ℝ)) ≤
      ((64/beta^2)*thetaAtom N Q B+(Q/(B:ℝ))*sieveError N beta Z) *
        ((hi-lo)/a + K/(a^2*Real.log N)) := by
  obtain ⟨K,hK,win⟩ := moving_prime_window
  refine ⟨K,hK,?_⟩
  filter_upwards [actual_frozen_two_log hb,eventually_ge_atTop (4:ℕ)] with N hrow hN
  intro hev B Q a lo hi Z E hB hQ hQN ha hl ho h1 hfloor hbZ hZ hMB hrB hE
  let S := primeWindow (B*N) ((N:ℝ)^lo) ((N:ℝ)^hi)
  let T := thetaAtom N Q B
  let A := (64/beta^2)*T+(Q/(B:ℝ))*sieveError N beta Z
  have hS := true_atom_scale hN hB hQ hQN
  have hbase := SingularSeries.liuSingularSeries_pos N
  have hlog := Real.log_pos (by exact_mod_cast (show 1<N by omega) : (1:ℝ)<N)
  have hB' : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have hE0 : 0≤sieveError N beta Z := by unfold sieveError; positivity
  have hT : 0≤T := le_trans (by positivity) hS
  have hA : 0≤A := add_nonneg (mul_nonneg (by positivity) hT) (mul_nonneg (by linarith) hE0)
  have each (q : ℕ) (hq : q∈S) : (frozenCount N (B*q) E (q:ℝ):ℝ) ≤ A*(1/(q:ℝ)) := by
    obtain ⟨hpr,_,hal,hah⟩ := mem_primeWindow.mp hq
    have hq0 : (0:ℝ)<q := Nat.cast_pos.mpr hpr.pos
    have heach := hrow hev (B*q) Z (q:ℝ) E (Nat.mul_pos hB hpr.pos) hbZ
      (rough_prime_mul hrB hpr (hZ.trans hal)) (hZ.trans hal) hE
    have hmain : (N:ℝ)/(B*q:ℕ) *
          ((64/beta^2)*SingularSeries.liuSingularSeries N/(Real.log N)^2) =
        (64/beta^2) * (SingularSeries.liuSingularSeries N*(N:ℝ)/((B:ℝ)*(Real.log N)^2)) /
          (q:ℝ) := by push_cast; ring
    have he : sieveError N beta Z ≤ (Q/(B:ℝ))*sieveError N beta Z / (q:ℝ) := by
      apply (le_div_iff₀ hq0).mpr
      simpa [mul_comm] using mul_le_mul_of_nonneg_right (hah.le.trans hMB) hE0
    calc
      _ ≤ (64/beta^2) * (SingularSeries.liuSingularSeries N*(N:ℝ)/
          ((B:ℝ)*(Real.log N)^2))/(q:ℝ) + sieveError N beta Z := by
        rw [hmain] at heach
        simpa only [sieveError,add_assoc] using heach
      _ ≤ (64/beta^2)*T/(q:ℝ)+(Q/(B:ℝ))*sieveError N beta Z/(q:ℝ) :=
        add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS
          (by positivity)) hq0.le) he
      _ = A*(1/(q:ℝ)) := by dsimp [A]; ring
  calc
    _ ≤ ∑ q ∈ S, A*(1/(q:ℝ)) := sum_le_sum each
    _ = A*(∑ q ∈ S, 1/(q:ℝ)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (win N B (by omega) a lo hi ha hl ho h1 hfloor) hA


private theorem remainder_absorbed {beta : ℝ} (hb : 0<beta) (hb' : beta≤1/100) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q : ℝ) (B : ℕ), 0<B → 1<Q/(B:ℝ) → Q/(B:ℝ)≤N →
      Q≤(N:ℝ)^(5/6:ℝ) → (Q/(B:ℝ))*sieveError N beta ((N:ℝ)^(2*beta)) ≤ thetaAtom N Q B := by
  let c := wuSingularSeries 1
  have hc : 0<c := wuSingularSeries_pos 1 (by decide)
  have hg := ((tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0:ℝ)<1/12)).const_mul
    (10:ℝ)).eventually (gt_mem_nhds (by simpa using hc : (10:ℝ)*0<c))
  filter_upwards [hg,eventually_ge_atTop (4:ℕ)] with N hsmall hN
  intro Q B hB hQ hQN hQb
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hB' : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have hlog := Real.log_pos hNr
  let R := (N:ℝ)^beta
  let Z := (N:ℝ)^(2*beta)
  let W := (N:ℝ)^(1/12:ℝ)
  have hW : 1≤W := Real.one_le_rpow hNr.le (by norm_num)
  have hR : 1≤R := Real.one_le_rpow hNr.le hb.le
  have hZ : Z≤W := Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
  have h6 : R^6≤W := by
    dsimp only [R,W]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    norm_num
    linarith
  have hZc : ((⌈Z⌉₊:ℕ):ℝ) ≤ Z+1 := (Nat.ceil_lt_add_one
    (Real.rpow_nonneg hNp.le _)).le
  have hE : sieveError N beta Z ≤ 10*W := by
    have h2 : (R+1)^2≤(2*R)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 := mul_le_mul_of_nonneg_right h2 (show 0≤R^4 by positivity)
    change ((⌈Z⌉₊:ℕ):ℝ)+2*(R+1)^2*R^4 ≤ 10*W
    nlinarith only [h4,h6,hZ,hZc,hW]
  have power : (N:ℝ)^(5/6:ℝ)*W*W = N := by
    dsimp only [W]
    rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
    norm_num
  have hS : c ≤ SingularSeries.liuSingularSeries N := by
    rw [←wuSingularSeries_eq_liu N (by omega)]
    exact wuSingularSeries_le_of_dvd (by decide) (by omega) (one_dvd N)
  have hs : 10*((Real.log N)^2/W) ≤ c := le_of_lt hsmall
  have hWs : 0<W := lt_of_lt_of_le zero_lt_one hW
  have hscale : 10 * (Real.log N)^2 ≤ SingularSeries.liuSingularSeries N * W := by
    have hdiv : 10*(Real.log N)^2/W ≤ SingularSeries.liuSingularSeries N := by
      simpa only [mul_div_assoc] using hs.trans hS
    exact (div_le_iff₀ hWs).mp hdiv
  apply le_trans _ (true_atom_scale hN hB hQ hQN)
  apply (le_div_iff₀ (mul_pos hB' (sq_pos_of_pos hlog))).mpr
  have hpos : 0≤Q := by
    have := (lt_div_iff₀ hB').mp hQ
    linarith
  calc
    _ = Q*sieveError N beta Z*(Real.log N)^2 := by field_simp [hB'.ne']; ring
    _ ≤ (N:ℝ)^(5/6:ℝ)*(10*W)*(Real.log N)^2 := by gcongr
    _ = ((N:ℝ)^(5/6:ℝ)*W)*(10*(Real.log N)^2) := by ring
    _ ≤ ((N:ℝ)^(5/6:ℝ)*W)*(SingularSeries.liuSingularSeries N*W) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg (Real.rpow_nonneg hNp.le _) hWs.le)
    _ = SingularSeries.liuSingularSeries N*((N:ℝ)^(5/6:ℝ)*W*W) := by ring
    _ = _ := by rw [power]

/-- A rate relative to the literal positive theta at EVERY original U3/U4
position. Thus summing against its label mark or an absolute signed price
preserves the same parent measure, even on arbitrarily sparse fibres. -/
theorem actual_padded_window_theta :
    ∃ a C K : ℝ, 0<a ∧ 0<C ∧ 1<K ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (n m mesh fine : ℕ) (k : Root) (t : ℝ) (G : Fin 431) (c : RootKey n m)
        (u : Key mesh fine) (x : Position N n k t G) (eta : ℝ) (E : ℕ → Prop),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → x ∈ atKey k t G c u →
      logPrimeMeshStep 1 6 fine ≤ 1 → 0≤eta → eta≤1 →
      (∀ ell,E ell → receiver N ell) →
      let o := levelOccurrence x.2
      let Q := cellQ N n c.1
      (paddedShell Q o (query u+eta) E:ℝ) ≤
        C*((logPrimeMeshStep 1 6 fine+eta)/a+K/(a^2*Real.log N)) *
          thetaAtom N Q (parentProduct o.current.old) := by
  let a := frozenResidualFloor/8
  let beta := min (a/4) (1/100)
  have hA : 0<a := div_pos frozenResidualFloor_pos (by norm_num)
  have hb : 0<beta := lt_min (by positivity) (by norm_num)
  have hb1 : beta≤1/100 := min_le_right _ _
  have hba : 2*beta≤a := by have h := min_le_left (a/4) (1/100:ℝ); linarith
  obtain ⟨K,hK,H⟩ := finite_parent_window hb
  let C := 64/beta^2+1
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨a,C,K,hA,hC,hK,?_⟩
  have hbig : ∀ᶠ N : ℕ in atTop, (3:ℝ)≤(N:ℝ)^a := by
    exact ((tendsto_rpow_atTop hA).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (3:ℝ))
  filter_upwards [H,remainder_absorbed hb hb1,hbig,eventually_ge_atTop (4:ℕ)] with N hcard herror hbig hN
  intro hev n m mesh fine k t G c u x eta E ht hu hn hx hm heta heta1 hE
  have hp := (Finset.mem_sigma.mp (Finset.mem_filter.mp hx).1).1
  have ho := (levelOccurrence_source x.2).1
  have hband := (Finset.mem_filter.mp hp).1
  have h2 : 2≤N := by omega
  have hgeom := original_band_geometry h2 hband
  have hq := (original_fibre_geometry h2 ht hu hn hp).1
  have hh := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hband) hgeom ho
  have hw := owned_query h2 ht hu hn hx
  let o := levelOccurrence x.2
  let Q := rootQ N n k t x.1
  let B := parentProduct o.current.old
  let L := residual o.current.node.physical
  let s := o.current.node.physical.argument
  let w := query u + eta
  let lo := L/w
  let hi := L/s
  let Z := (N:ℝ)^(2*beta)
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hB : 0<B := hh.1.2.1
  have hB' : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have hQR : 1<Q/(B:ℝ) := (parentWindow_logs hh.1).2.1
  have hBQ : (B:ℝ)<Q := hh.1.2.2.1
  have hBp : (1:ℝ)≤B := by exact_mod_cast hB
  have hQN : Q/(B:ℝ) ≤ N :=
    (div_le_self (hB'.trans hBQ).le hBp).trans hh.1.2.2.2.1
  have hLl : frozenResidualFloor ≤ L := hh.2.2.1.trans_eq hh.2.1.symm
  have hLp : 0<L := frozenResidualFloor_pos.trans_le hLl
  have hbaseEq : Q=(B:ℝ)*(N:ℝ)^L := by
    change Q=(B:ℝ)*(N:ℝ)^residual o.current.node.physical
    rw [hh.2.1]
    exact hh.2.2.2.2.2
  have hLK : Q/(B:ℝ) = (N:ℝ)^L := by
    rw [hbaseEq]
    field_simp [hB'.ne']
  have hL1 : L≤1 := by
    apply (Real.rpow_le_rpow_left_iff hNr).mp
    simpa only [←hLK,Real.rpow_one] using hQN
  have hs1 : 1≤s := hh.2.2.2.1.1
  have hs6 : s≤6 := hh.2.2.2.1.2
  have hs0 : 0<s := zero_lt_one.trans_le hs1
  have hsw : s≤w := hw.2.2.2.1.trans (le_add_of_nonneg_right heta)
  have hw0 : 0<w := hs0.trans_le hsw
  have hw8 : w≤8 := by dsimp only [w]; linarith only [hw.2.2.2.2.1,hs6,hm,heta1]
  have ha0 : a≤lo := by
    apply (le_div_iff₀ hw0).mpr
    calc
      a*w ≤ a*8 := mul_le_mul_of_nonneg_left hw8 hA.le
      _ = frozenResidualFloor := by dsimp only [a]; ring
      _ ≤ _ := hLl
  have horder : lo≤hi := div_le_div_of_nonneg_left hLp.le hs0 hsw
  have hhi : hi≤1 := (div_le_iff₀ hs0).mpr (by linarith only [hL1,hs1])
  have hwe : hi-lo ≤ logPrimeMeshStep 1 6 fine+eta := by
    have hden : 1≤s*w := one_le_mul_of_one_le_of_one_le hs1 (hs1.trans hsw)
    have hid : hi-lo=L*(w-s)/(s*w) := by dsimp [hi,lo]; field_simp [hs0.ne',hw0.ne']; ring
    rw [hid]
    apply le_trans (div_le_self (mul_nonneg hLp.le (sub_nonneg.mpr hsw)) hden)
    have hh' := mul_le_mul_of_nonneg_right hL1 (sub_nonneg.mpr hsw)
    dsimp only [w] at hh'
    linarith only [hh',hw.2.2.2.2.1]
  have hpwr (v : ℝ) : cutoff Q B v = (N:ℝ)^(L/v) :=
    history_cutoff_power h2 ht hu hn hband ho v
  have hrough := (history_integer_roughness h2 ht hu hn hband ho).1
  have hZ : Z≤(N:ℝ)^lo := Real.rpow_le_rpow_of_exponent_le hNr.le (hba.trans ha0)
  have hroughB : ChenPrimeRough Z B := by
    intro p hp hd
    exact hZ.trans ((Real.rpow_le_rpow_of_exponent_le hNr.le horder).trans
      ((hpwr s).ge.trans (hrough p hp hd)))
  have hupper : (N:ℝ)^hi≤Q/(B:ℝ) := by
    rw [hLK]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le (div_le_self hLp.le hs1)
  have hQbound : Q≤(N:ℝ)^(5/6:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    have hfl := (frozenLevel_bounds (root_total_bounds ht hu hgeom) n).1
    have hr := (sourceResidual_bounds ht hu hgeom).2
    have hx' : physicalPrime N x.1 ≤ 1/3 := (rootBand_subset k hgeom).2
    exact hfl.trans (by change physicalPrime N x.1+sourceResidual k t (physicalPrime N x.1)≤5/6; linarith)
  have hr := hcard hev B Q a lo hi Z E hB hQR hQN hA ha0 horder hhi hbig
    (Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith : beta<2*beta)) hZ hupper hroughB hE
  have herr := herror Q B hB hQR hQN hQbound
  have hseries := SingularSeries.liuSingularSeries_pos N
  have hscale0 : 0≤SingularSeries.liuSingularSeries N*(N:ℝ)/((B:ℝ)*(Real.log N)^2) := by positivity
  have hT : 0≤thetaAtom N Q B := hscale0.trans (true_atom_scale hN hB hQR hQN)
  have hprice : 0≤(hi-lo)/a+K/(a^2*Real.log N) := by
    have := sub_nonneg.mpr horder
    have := Real.log_pos hNr
    positivity
  have hfac : (64/beta^2)*thetaAtom N Q B+(Q/(B:ℝ))*sieveError N beta Z ≤
      C*thetaAtom N Q B := by dsimp [C]; nlinarith only [herr]
  have hwidth := add_le_add_right (div_le_div_of_nonneg_right hwe hA.le) (K/(a^2*Real.log N))
  dsimp only
  rw [hq]
  change ((∑ q ∈ primeWindow (B*N) (cutoff Q B w) (cutoff Q B s),
    frozenCount N (B*q) E (q:ℝ)):ℝ) ≤ _
  rw [hpwr w,hpwr s,Int.cast_sum]
  exact hr.trans ((mul_le_mul hfac hwidth hprice (mul_nonneg hC.le hT)).trans_eq (by ring))


/-- Actual upper envelope for an ordinary, masked or rejected prime count at
the unmodified Member query. Multiplying an entire lost square collar by this
one constant transfers its true theta budget to the true nonnegative counts. -/
theorem actual_member_count_dominated :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (n p : ℕ) (k : Root) (t : ℝ) (o : Occurrence N) (E : ℕ → Prop),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p ∈ originalBand N k →
      o ∈ rootHistory N n k t p → (∀ ell,E ell → receiver N ell) →
      let Q := rootQ N n k t p
      let B := parentProduct o.current.old
      (frozenCount N B E (memberCutoff Q o):ℝ) ≤ C*thetaAtom N Q B := by
  let beta := min (frozenLeafCutoffFloor/4) (1/100)
  have hb : 0<beta := lt_min (div_pos frozenLeafCutoffFloor_pos (by norm_num)) (by norm_num)
  have hb1 : beta≤1/100 := min_le_right _ _
  have hbf : 2*beta≤frozenLeafCutoffFloor := by
    have h := min_le_left (frozenLeafCutoffFloor/4) (1/100:ℝ)
    linarith only [h,frozenLeafCutoffFloor_pos]
  refine ⟨64/beta^2+1,by positivity,?_⟩
  filter_upwards [actual_frozen_two_log hb,remainder_absorbed hb hb1,eventually_ge_atTop (4:ℕ)]
    with N H H' hN
  intro hev n p k t o E ht hu hn hp ho hE
  let B := parentProduct o.current.old
  let Q := rootQ N n k t p
  let Z := (N:ℝ)^(2*beta)
  let z := memberCutoff Q o
  have h2 : 2≤N := by omega
  have hband := original_band_geometry h2 hp
  have hh := rootHistory_support (by omega : 1<N) ht hu hn (original_band_prime hp) hband ho
  have hg := history_integer_roughness h2 ht hu hn hp ho
  have hB : 0<B := hh.1.2.1
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hZ : Z≤z := (Real.rpow_le_rpow_of_exponent_le hNr.le hbf).trans hg.2.1
  have hQ : 1<Q/(B:ℝ) := (parentWindow_logs hh.1).2.1
  have hBQ : (B:ℝ)<Q := hh.1.2.2.1
  have hBr : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have hQN : Q/(B:ℝ)≤N := (div_le_self (hBr.trans hBQ).le (by exact_mod_cast hB)).trans hh.1.2.2.2.1
  have hQB : Q≤(N:ℝ)^(5/6:ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hNr.le
    have hf := (frozenLevel_bounds (root_total_bounds ht hu hband) n).1
    have hr := (sourceResidual_bounds ht hu hband).2
    have hx : physicalPrime N p ≤ 1/3 := (rootBand_subset k hband).2
    exact hf.trans (by change physicalPrime N p+sourceResidual k t (physicalPrime N p)≤5/6; linarith)
  have hrow := H hev B Z z E hB (Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith : beta<2*beta))
    (fun r hr hd => hZ.trans (hg.1 r hr hd)) hZ hE
  have herr0 : 0≤sieveError N beta Z := by dsimp [sieveError]; positivity
  have herr : sieveError N beta Z≤thetaAtom N Q B :=
    (le_mul_of_one_le_left herr0 hQ.le).trans (H' Q B hB hQ hQN hQB)
  have hscale := mul_le_mul_of_nonneg_left (true_atom_scale hN hB hQ hQN) (by positivity : 0≤64/beta^2)
  calc
    (frozenCount N B E z:ℝ) ≤ (N:ℝ)/B*((64/beta^2)*SingularSeries.liuSingularSeries N/
        (Real.log N)^2)+sieveError N beta Z := by simpa [sieveError,add_assoc] using hrow
    _ = (64/beta^2)*(SingularSeries.liuSingularSeries N*(N:ℝ)/((B:ℝ)*(Real.log N)^2))+
        sieveError N beta Z := by ring
    _ ≤ _ := (add_le_add hscale herr).trans_eq (by ring)

end
end ImbalancedChen.Part5OriginalH430RoughCutoffSelberg
