import ImbalancedChen.P4BOriginalRankTwoBlockPayment
import ImbalancedChen.P4BOriginalRankTwoChartPayment

/-! A participating block is selected by a genuinely nonzero prime pair,
before any congruence is inspected. Low product blocks use the existing
off-target signed-row bound. Near-target blocks have two long prime ranges. -/
namespace ImbalancedChen.P4BOriginalRankTwoPhysicalBlocks
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalRankTwoGateVariation P4BOriginalRankTwoPositiveRestoration
open P4BOriginalRankTwoPrimeMesh
open P4BOriginalPairFibreDictionary (naturalWeight kernel trimmed_on pair_mem)
open P4BOriginalFiniteSmoothCount (weight coefficient)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BOriginalRankTwoChartPayment (carrier tau)
open P4BOuterRampRoughness (baseline)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow signedKernel)
open P4BLabelledPairDictionary (pairTuple tuplePair_pairTuple)

/-- Every point used for the geometric bounds is an original nonzero
point. Evaluating an auxiliary row at a grid edge requires no primality. -/
theorem active_block {N i j p t : ℕ} (hN : 2≤N)
    {b kap s kap0 : ℝ} (hb : 0<b) (hk : 0<kap) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (hp : p∈box N i) (ht : t∈box N j)
    (hn : naturalWeight b kap s kap0 N p t≠0) :
    (N:ℝ)^(19/96:ℝ)<2*(base i:ℝ) ∧ (N:ℝ)^(19/96:ℝ)<2*(base j:ℝ) ∧
      (base i:ℝ)*(base j:ℝ)≤Real.exp 1*(N:ℝ) := by
  obtain ⟨hp',hpl,hpu⟩ := box_spec hp
  obtain ⟨ht',htl,htu⟩ := box_spec ht
  let u := pairTuple N (p,t) (mem_chenPrimePrefix.mp hp').1 (mem_chenPrimePrefix.mp ht').1
  have hu : u∈Part3.labelledPrimeTuples 2 N := pair_mem hp' ht'
  have he := trimmed_on b kap s kap0 hu
  rw [tuplePair_pairTuple] at he
  have hw : weight b kap s N u≠0 := (mul_ne_zero_iff.mp (show trimmedWeight b kap s kap0 N u≠0 from
    fun h => hn (he.symm.trans h))).2
  have hR := P4BSmoothOuterRampRoughness.smooth_physical_ramp_nonzero_prime_factors_rough
    hb hN hs hg hu hw
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hprod := P4B.smoothPhysicalPairOuterRamp_nonzero_product_lt_exp_mul_N hNr hs hu hw
  change (N:ℝ)^(19/96:ℝ)<((P4BLabelledPairDictionary.tuplePair u).1:ℝ) ∧ _ at hR
  simp only [u,tuplePair_pairTuple,Nat.cast_mul] at hR hprod
  have hs1 := P4BArbitraryWidthUpperPairProfile.legal_width_le_one hb hk
    (by norm_num : 0<(1:ℝ)) (by norm_num : 0<(19/96:ℝ)) (by simpa only [one_mul] using hg)
  exact ⟨hR.1.trans_le (by exact_mod_cast hpu),hR.2.trans_le (by exact_mod_cast htu),
    (mul_le_mul (Nat.cast_le.mpr hpl.le) (Nat.cast_le.mpr htl.le) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)).trans (hprod.le.trans
       (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hs1) (Nat.cast_nonneg _)))⟩

theorem physical_moduli (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (k N : ℕ) (hN : 1<N) (ell : ℝ) (hell : ell<1/1000) :
    let S := carrier m r n e q a omega k N ell
    let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
    (∀ d∈S,0<d ∧ (d:ℝ)<(N:ℝ)^(2/5:ℝ) ∧ N.Coprime d ∧ |c d|≤1) ∧
      S⊆Finset.Icc 1 N ∧ (∀ d,|c d|≤1) := by
  dsimp only
  have HH (d : ℕ) (hd : d∈carrier m r n e q a omega k N ell) := (Finset.mem_inter.mp hd).2
  have hcap := fun d hd => P4AFiniteFallbackLowRankRho.activeLow_power m r n e q a omega N hN
    (tau m e q a k) ell hell (HH d hd)
  have hpos := fun d hd => Nat.pos_of_ne_zero
    (P4AFiniteFallbackLowRankRho.activeLow_squarefree m r n e q a omega N _ ell (HH d hd)).ne_zero
  have hc (d : ℕ) : |coefficient m r n e q a omega k N ((N:ℝ)^ell) d|≤1 :=
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d
  have hn : (1:ℝ)≤N := by exact_mod_cast hN.le
  refine ⟨fun d hd => ⟨hpos d hd,hcap d hd,
    P4AFiniteFallbackLowRankRho.activeLow_target_coprime m r n e q a omega N _ ell (HH d hd),hc d⟩,
    fun d hd => Finset.mem_Icc.mpr ⟨hpos d hd,?_⟩,hc⟩
  apply Nat.cast_le.mp (α:=ℝ)
  exact (hcap d hd).le.trans (by simpa using
    Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (2/5:ℝ)≤1))

theorem kernel_row (N x : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) :
    ((∑ d∈S,c d*kernel N d x:ℝ):ℂ)=signedRow S (fun d => (c d:ℂ)) N x := by
  simp only [signedRow,Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : Nat.ModEq d x N <;> by_cases k : x.Coprime d <;>
    simp [signedKernel,kernel,h,k]

theorem modulus_last (N : ℕ) (H T S : Finset ℕ) (c : ℕ → ℝ) (W : ℕ → ℕ → ℝ) :
    discrepancy N S c H T W=∑ p∈H,∑ t∈T,W p t*(∑ d∈S,c d*kernel N d (p*t)) := by
  simp only [discrepancy,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem low_block {N i j : ℕ} {C : ℝ} (hC : 0<C) (hN : 1<N)
    (hcut : 4*(N:ℝ)^(9/10:ℝ)<N) (hx : (base i:ℝ)*(base j:ℝ)≤(N:ℝ)^(9/10:ℝ))
    (S : Finset ℕ) (c : ℕ → ℝ) (b kap s kap0 : ℝ)
    (hr : ∀ z : ℕ,1≤z → (z:ℝ)≤Real.exp 1*(N:ℝ) → z≠N →
      ‖signedRow S (fun d => (c d:ℂ)) N z‖≤C*(N:ℝ)^(1/50:ℝ)) :
    |discrepancy N S c (box N i) (box N j) (naturalWeight b kap s kap0 N)|≤C*(N:ℝ)^(23/25:ℝ) := by
  let Y := C*(N:ℝ)^(1/50:ℝ)
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hp (p t : ℕ) (hp : p∈box N i) (ht : t∈box N j) :
      |naturalWeight b kap s kap0 N p t*(∑ d∈S,c d*kernel N d (p*t))|≤Y := by
    have hpp := box_spec hp
    have htt := box_spec ht
    have H : (p:ℝ)*(t:ℝ)≤4*((base i:ℝ)*(base j:ℝ)) := by
      have hp' : (p:ℝ)≤2*(base i:ℝ) := by exact_mod_cast hpp.2.2
      have ht' : (t:ℝ)≤2*(base j:ℝ) := by exact_mod_cast htt.2.2
      convert mul_le_mul hp' ht' (Nat.cast_nonneg _) (by positivity) using 1 <;> ring
    have hz : ((p*t:ℕ):ℝ)<N := by rw [Nat.cast_mul]; linarith
    have he : ((p*t:ℕ):ℝ)≤Real.exp 1*(N:ℝ) := hz.le.trans
      (le_mul_of_one_le_left (Nat.cast_nonneg _) (Real.one_le_exp (by norm_num)))
    have hnorm := hr (p*t) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (mem_chenPrimePrefix.mp hpp.1).2.ne_zero (mem_chenPrimePrefix.mp htt.1).2.ne_zero))
      he (by exact_mod_cast hz.ne)
    rw [← kernel_row,Complex.norm_real,Real.norm_eq_abs] at hnorm
    have hw := weight_unit b kap s kap0 N p t
    rw [abs_mul,abs_of_nonneg hw.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) hw.2).trans hnorm
  rw [modulus_last]
  calc
    _ ≤ ∑ p∈box N i,∑ t∈box N j,Y := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun p hp' => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun t ht => hp p t hp' ht))))
    _ = ((box N i).card:ℝ)*((box N j).card:ℝ)*Y := by simp [nsmul_eq_mul,mul_assoc]
    _ ≤ ((N:ℝ)^(9/10:ℝ))*Y := mul_le_mul_of_nonneg_right
      ((mul_le_mul (Nat.cast_le.mpr (box_le N i)) (Nat.cast_le.mpr (box_le N j))
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans hx) hY
    _ = _ := by
      dsimp only [Y]
      rw [show (23/25:ℝ)=9/10+1/50 by norm_num,Real.rpow_add (by exact_mod_cast (show 0<N by omega):0<(N:ℝ))]
      ring

end
end ImbalancedChen.P4BOriginalRankTwoPhysicalBlocks
