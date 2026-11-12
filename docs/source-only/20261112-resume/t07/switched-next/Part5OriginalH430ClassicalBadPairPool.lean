import ImbalancedChen.Part5OriginalH430ClassicalBadPairReceivers
import ImbalancedChen.P2EnhancedW1FixedPowerLabelMultiplicity

/-! One complete-modulus sum for every original rejected Γ5 pair, with
the external p and both ordered prime factors retained. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairPool
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open MathlibNt.SieveTheory.BombieriVinogradov MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2ActualMarkedCountState (rootLevel root_coefficient_full_Q)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2SeedOmegaLiteralFibre (K)
open P2EnhancedW1FixedPowerLabelMultiplicity (prime_factor_fibre_card_le_inv_power)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430ClassicalBadPairGeometry
open Part5OriginalH430ClassicalBadPairReceivers
open Part5OriginalH430SeedPurifiedPrimeFibres (fibre)
open Part5OriginalH430RootRosserSurplus (signedAP)
open Part5OriginalH430FrozenClassicalRootModuli
open scoped Classical BigOperators Topology

def major (N k : ℕ) : ℝ := trueError N k+(3/log 2)*log (N:ℝ)

def difference (N p : ℕ) (Q : ℝ) (l : List ℕ) : ℝ :=
  let y := cutoff Q p (227/50)
  max (sourceAt N p Q l) (fibre true N (p*l.prod) y)-
    (K/4)*thetaConversion N p*fibre false N (p*l.prod) y

private theorem major_nonneg {N : ℕ} (hn : 1≤N) (k : ℕ) : 0≤major N k :=
  add_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (log_nonneg (by exact_mod_cast hn)))

private theorem row_pool {N D : ℕ} {Q z τ : ℝ} (hN : 2≤N) (hlog : 1≤log (N:ℝ))
    (hd : 0<D) (hcop : D.Coprime N) (hr : 1<Q/(D:ℝ)) (hQ : Q≤(N:ℝ)^(1/2-τ)) :
    signedAP N D Q z+(N.primeFactors.card:ℝ) ≤
      2*∑ k ∈ (pool N τ).filter (fun k => D∣k), major N k := by
  let A := (ordinarySievePrimeProduct (D*N) z).divisors
  let weight := ordinaryRosserWeight true N D (rootLevel Q D) z
  let S := A.filter (fun r => weight r≠0)
  let P := (pool N τ).filter (fun k => D∣k)
  let g := fun k : ℕ => finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N k+
    (((chenAdditivePrimeCarrier N).card:ℝ)-logarithmicIntegral N-chenPrimeDivisorCount N k)/(Nat.totient k:ℝ)
  have hcap (r : ℕ) (h : r∈S) : D*r∈P := by
    obtain ⟨ha,hw⟩ := mem_filter.mp h
    have hr' := root_coefficient_full_Q hd hr hw
    have hr0 := Nat.pos_of_mem_divisors ha
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hd hr0,Nat.le_floor (hr'.1.trans hQ)⟩,
      Nat.coprime_mul_iff_left.mpr ⟨hcop,(Nat.coprime_mul_iff_right.mp hr'.2).2⟩⟩,dvd_mul_right _ _⟩
  have hD : D∈P := by
    have hDlt : (D:ℝ)<Q := by simpa using (lt_div_iff₀ (Nat.cast_pos.mpr hd)).mp hr
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨hd,Nat.le_floor (hDlt.le.trans hQ)⟩,hcop⟩,dvd_refl _⟩
  have he : signedAP N D Q z=∑ r∈S,weight r*g (D*r) := by
    unfold signedAP
    rw [show S=A.filter (fun r => weight r≠0) by rfl,sum_filter]
    apply sum_congr rfl
    intro r _
    change weight r*g (D*r) = if weight r≠0 then _ else _
    split_ifs with hh
    · rfl
    · rw [not_not.mp hh,zero_mul]
  have hrow : signedAP N D Q z≤∑ k∈P,major N k := by
    rw [he]
    calc
      _ ≤ ∑ r∈S,major N (D*r) := by
        apply sum_le_sum
        intro r hr'
        have hk := mem_filter.mp (mem_filter.mp (hcap r hr')).1
        have hb := atom_bound (by omega : 0<N) (mem_Icc.mp hk.1).1 hk.2 hlog
        calc
          _ ≤ |weight r*g (D*r)| := le_abs_self _
          _ ≤ |g (D*r)| := by rw [abs_mul]; exact (mul_le_mul_of_nonneg_right
            (ordinaryRosserWeight_abs_le_one true N D (rootLevel Q D) r z) (abs_nonneg _)).trans_eq (one_mul _)
          _ ≤ _ := hb
      _ = ∑ k∈S.image (fun r => D*r), major N k :=
        (sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd h)).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
        intro k hk
        obtain ⟨r,h,rfl⟩ := mem_image.mp hk
        exact hcap r h) (fun k _ _ => major_nonneg (by omega) k)
  have hs := Finset.single_le_sum (s:=P) (f:=major N) (fun k _ => major_nonneg (by omega) k) hD
  have hc := chen_primeFactors_card_le_log (show 0<N by omega)
  have hn : 0≤log (N:ℝ)/log 2 := div_nonneg (by linarith only [hlog]) (by positivity)
  have hb : log (N:ℝ)/log 2≤major N D := by
    unfold major
    have hl : (3/log 2)*log (N:ℝ)=3*(log (N:ℝ)/log 2) := by ring
    linarith only [hl,hn,(abs_nonneg (chenQuotientPrimeAPError N (trueLogarithmicIntegral N) D))]
  linarith only [hc.trans (hb.trans hs),hrow]

private def hits (N n p k : ℕ) (τ : ℝ) :=
  (badLabels N (rootQ N n .U3 τ p) p).filter (fun l => p*l.prod∣k)

private theorem multiplicity {N n k : ℕ} {τ : ℝ} (hn : 2≤N) (hτ : 0≤τ) (hτ' : τ≤1/12)
    (hm : 1/((n:ℝ)+1)≤11/384) (hk : k∈pool N τ) (B : Finset ℕ) (hB : B⊆classicalBand N) :
    (∑ p∈B, ((hits N n p k τ).card:ℝ))≤(200:ℝ)^3 := by
  let P := k.primeFactors.filter (fun q => floorScale N≤(q:ℝ))
  have hki := mem_Icc.mp (mem_filter.mp hk).1
  have hr : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hkN : k≤N := by
    have h := (Nat.floor_le (rpow_nonneg (Nat.cast_nonneg N) (1/2-τ))).trans
      (rpow_le_rpow_of_exponent_le hr (show 1/2-τ≤(1:ℝ) by linarith))
    exact_mod_cast (show (k:ℝ)≤N from (Nat.cast_le.mpr hki.2).trans (by simpa using h))
  have hP : (P.card:ℝ)≤200 := by
    have h := prime_factor_fibre_card_le_inv_power N k P (1/200) (by omega) hki.1 hkN
      (Finset.filter_subset _ _) (by norm_num) (fun _ hx => (mem_filter.mp hx).2)
    norm_num at h
    exact h
  have data (p : ℕ) (hp : p∈B) (l : List ℕ) (hl : l∈hits N n p k τ) :
      p∈P ∧ l.getD 0 0∈P ∧ l.getD 1 0∈P := by
    obtain ⟨hl',hd⟩ := mem_filter.mp hl
    have h := actual_pair hn hτ hτ' hm (hB hp) hl'
    have put (q : ℕ) (hq : q.Prime) (hz : floorScale N≤(q:ℝ)) (hv : q∣p*l.prod) : q∈P :=
      mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq,hv.trans hd,(by omega : k≠0)⟩,hz⟩
    have hv (q : ℕ) (hq : q∈l) : q∣p*l.prod := dvd_mul_of_dvd_right (List.dvd_prod hq) p
    exact ⟨put p h.outer.1 h.scale.1 (dvd_mul_right _ _),
      put _ h.first.1 h.scale.2.1 (hv _ (by rw [h.pair]; simp)),
      put _ h.second.1 h.scale.2.2 (hv _ (by rw [h.pair]; simp))⟩
  have rows (p : ℕ) (hp : p∈B) :
      (hits N n p k τ).card≤(if p∈P then P.card^2 else 0) := by
    split_ifs with h
    · have hc := Finset.card_le_card_of_injOn (s:=hits N n p k τ) (t:=P×ˢP)
          (fun l : List ℕ => (l.getD 0 0,l.getD 1 0))
          (fun l hl => mem_product.mpr (data p hp l hl).2) (fun l hl l' hl' he => by
            have h₁ := (actual_pair hn hτ hτ' hm (hB hp) (mem_filter.mp hl).1).pair
            have h₂ := (actual_pair hn hτ hτ' hm (hB hp) (mem_filter.mp hl').1).pair
            exact h₁.trans ((congrArg (fun z : ℕ×ℕ => [z.1,z.2]) he).trans h₂.symm))
      simpa only [card_product,pow_two] using hc
    · have he : hits N n p k τ=∅ := eq_empty_iff_forall_notMem.mpr (fun l hl => h (data p hp l hl).1)
      rw [he,card_empty]
  have hc := sum_le_sum (s:=B) rows
  rw [←sum_filter,sum_const,nsmul_eq_mul] at hc
  have hh : (B.filter (fun p => p∈P)).card≤P.card :=
    card_le_card (fun _ hx => (mem_filter.mp hx).2)
  have htot : (∑ p∈B,(hits N n p k τ).card)≤P.card^3 := by
    calc
      _ ≤ _ := hc
      _ ≤ P.card*(P.card^2) := Nat.mul_le_mul_right _ hh
      _ = _ := by ring
  have hreal : (∑ p∈B,((hits N n p k τ).card:ℝ))≤(P.card:ℝ)^3 := by exact_mod_cast htot
  exact hreal.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hP _)

/-- Uniform source-only finite estimate for any subfamily of the
original classical roots; no division by the subfamily mass occurs. -/
theorem actual_bad_whole_pool :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (n : ℕ) (τ : ℝ), 0≤τ → τ≤1/12 →
      1/((n:ℝ)+1)≤11/384 → ∀ B ⊆ classicalBand N,
      (∑ p∈B,∑ l∈badLabels N (rootQ N n .U3 τ p) p,
        difference N p (rootQ N n .U3 τ p) l) ≤
        (2*200^3:ℝ)*∑ k∈pool N τ,major N k := by
  filter_upwards [actual_classical_bad_row,eventually_ge_atTop (4:ℕ),eventually_one_le_nat_log]
    with N hf hN hlog
  intro he n τ ht ht' hn B hB
  let Q := fun p => rootQ N n .U3 τ p
  let L := fun p => badLabels N (Q p) p
  let A := pool N τ
  have row (p : ℕ) (hp : p∈B) (l : List ℕ) (hl : l∈L p) :
      difference N p (Q p) l≤2*∑ k∈A.filter (fun k => p*l.prod∣k),major N k := by
    have hg := actual_pair (by omega) ht ht' hn (hB hp) hl
    exact (hf he n p τ ht ht' hn (hB hp) l hl).trans
      (row_pool (by omega) hlog hg.big.1 hg.big.2.2 hg.child
        (classical_geometry (m:=0) (by omega) ht ht' hn (hB hp)).2.2)
  have flip (p : ℕ) : (∑ l∈L p,∑ k∈A.filter (fun k => p*l.prod∣k),major N k) =
      ∑ k∈A,((hits N n p k τ).card:ℝ)*major N k := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro k _
    rw [←sum_filter,sum_const,nsmul_eq_mul]
  calc
    _ ≤ ∑ p∈B,∑ l∈L p,2*∑ k∈A.filter (fun k => p*l.prod∣k),major N k :=
      sum_le_sum (fun p hp => sum_le_sum (row p hp))
    _ = 2*∑ p∈B,∑ k∈A,((hits N n p k τ).card:ℝ)*major N k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      rw [←mul_sum,flip]
    _ = 2*∑ k∈A,(∑ p∈B,((hits N n p k τ).card:ℝ))*major N k := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [sum_mul]
    _ ≤ 2*∑ k∈A,200^3*major N k := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum (fun k hk => mul_le_mul_of_nonneg_right
        (multiplicity (by omega) ht ht' hn hk B hB) (major_nonneg (by omega) k))
    _ = _ := by rw [←mul_sum,mul_assoc]

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairPool
