import ImbalancedChen.P4BOriginalRankTwoCommonBudget

/-! All original ordered prime labels on the actual outstanding
rough-rank-two carrier, and the resulting remaining higher-rank source. -/
namespace ImbalancedChen.P4BOriginalRankTwoGlobalPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalRankTwoPrimeMesh
open P4BOriginalRankTwoPhysicalBlocks (active_block physical_moduli low_block)
open P4BOriginalRankTwoPositiveRestoration (discrepancy reciprocalMass reciprocalMass_nonneg modulus_budget)
open P4BOriginalRankTwoCommonBudget (gridSize eventually_geometry eventually_block_cost)
open P4BOriginalRankTwoChartPayment (carrier)
open P4BOriginalTwoAtlasSmallPayment (remaining small atlasPair)
open P4BOriginalPairFibreDictionary (naturalWeight)
open P4BOriginalFiniteSmoothCount (coefficient Q)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BOriginalFiniteProperArithmetic (modulusExponent exists_row_costs)
open P4BOuterRampRoughness (baseline)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ActualDyadicRankPolynomial (bankLogConstant bankLogConstant_pos eventually_actual_cutoffIndex_le_log)
open Part3 (primeProductSignedError)

/-- Uniform over all complete moduli in the stated range and arbitrary one-bounded
weights on that finite set. The early constants come from the same proof on dyadic blocks. -/
theorem eventually_each_bounded_block (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kap s kap0 : ℝ),0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d ∧ (d:ℝ)<(N:ℝ)^(2/5:ℝ) ∧ N.Coprime d ∧ |c d|≤1) →
      ∀ i∈bank N,∀ j∈bank N,|discrepancy N S c (box N i) (box N j)
        (naturalWeight b kap s kap0 N)|≤delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  let B := A+2
  let D := B+(A+1)
  obtain ⟨K,hK,x0,hx0,HB⟩ := P4BOriginalRankTwoBlockPayment.exists_block_bound D
  obtain ⟨C,Cdiag,hC,_,rows⟩ := exists_row_costs (1/50) (by norm_num)
  have smallProduct := eventually_powerLog_le_logAccuracy C (23/25) 0 A (by norm_num) delta hd
  filter_upwards [eventually_geometry B x0,eventually_block_cost A K delta hK hd,smallProduct]
    with N geom hbudget hsmall
  obtain ⟨hN,hlog,hcut,hJ,hJlo,hJhi,Hgeom⟩ := geom
  intro b kap s kap0 hb hk hs hg S c hS
  intro i hi j hj
  let P := base i
  let V := base j
  let x := (P:ℝ)*(V:ℝ)
  let T := box N j
  let W := naturalWeight b kap s kap0 N
  have hn0 : 1<N := by omega
  have hn : (1:ℝ)<N := by exact_mod_cast hn0
  have hSN : S⊆Finset.Icc 1 N := by
    intro d hd
    refine Finset.mem_Icc.mpr ⟨(hS d hd).1,Nat.cast_le.mp (α:=ℝ) ?_⟩
    exact (hS d hd).2.1.le.trans (by simpa using
      Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num : (2/5:ℝ)≤1))
  have hgoal : 0≤delta*(N:ℝ)/(Real.log (N:ℝ))^A := by positivity
  by_cases hlow : x≤(N:ℝ)^(9/10:ℝ)
  · let cc := fun d => if d∈S then c d else 0
    obtain ⟨HR,_⟩ := rows N (by omega) S cc (fun d ht => (hS d ht).1)
      (fun d => by
        by_cases h : d∈S
        · simpa only [cc,if_pos h] using (hS d h).2.2.2
        · simp [cc,h])
      (fun d h => by
        by_cases ht : d∈S
        · exact (hS d ht).2.1.trans_le (Real.rpow_le_rpow_of_exponent_le hn.le
            (by norm_num [modulusExponent]))
        · exact (h (by simp [cc,ht])).elim)
    have same (z : ℕ) : signedRow S (fun d => (c d:ℂ)) N z=signedRow S (fun d => (cc d:ℂ)) N z :=
      Finset.sum_congr rfl (fun d hd' => by simp [cc,hd'])
    apply (low_block hC hn0 hcut hlow S c b kap s kap0 (fun z hz hc' hn' => by
      rw [same]; exact HR z hz hc' hn')).trans
    simpa only [pow_zero,mul_one] using hsmall
  · by_cases live : ∃ p∈box N i,∃ t∈box N j,W p t≠0
    · obtain ⟨p,hp,t,ht,hw⟩ := live
      obtain ⟨hpr,hvr,hxhi⟩ := active_block hN hb hk hs hg hp ht hw
      have hxlo : (N:ℝ)^(9/10:ℝ)≤x := (lt_of_not_ge hlow).le
      obtain ⟨hstart,hPx,hVx,hJP,hcap,hlogx⟩ := Hgeom P V x hxlo hxhi hpr hvr
      have hPH : P≤cap N P := le_min (base_le (by omega) hi) (by omega)
      have hT : T⊆Finset.Icc 1 (2*V) := by
        intro t ht
        obtain ⟨hp',_,hu⟩ := box_spec ht
        exact Finset.mem_Icc.mpr ⟨(mem_chenPrimePrefix.mp hp').2.pos,hu⟩
      have hmain := HB N P V (cap N P) (gridSize B N) S T c b kap s kap0 hn hs hstart hPx hVx
        hPH (min_le_right _ _) hJ hJP hT (box_le N j) (fun d hd' => ⟨(hS d hd').1,
          (hS d hd').2.1.le.trans hcap,(hS d hd').2.2.1,(hS d hd').2.2.2⟩)
      have hm : reciprocalMass S c≤4*(1+Real.log (N:ℝ)) := by
        simpa only [max_eq_right hn.le] using modulus_budget hSN (fun d hd => (hS d hd).2.2.2)
      exact hmain.trans (hbudget x (reciprocalMass S c) (zero_lt_one.trans (hx0.trans_le hstart))
        hxhi hlogx (reciprocalMass_nonneg _ _) hm hJlo hJhi)
    · have he : discrepancy N S c (box N i) (box N j) W=0 := by
        unfold discrepancy
        apply Finset.sum_eq_zero
        intro d _
        rw [show (∑ p∈box N i,∑ t∈box N j,W p t*P4BOriginalPairFibreDictionary.kernel N d (p*t))=0 from
          Finset.sum_eq_zero (fun p hp => Finset.sum_eq_zero (fun t ht => by
            rw [show W p t=0 by by_contra h; exact live ⟨p,hp,t,ht,h⟩,zero_mul])),mul_zero]
      change |discrepancy N S c (box N i) (box N j) W|≤_
      simpa only [he,abs_zero] using hgoal

theorem eventually_each_block (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kap s kap0 : ℝ),0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),ell<1/1000 →
      let S := carrier m r n e q a omega k N ell
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      ∀ i∈bank N,∀ j∈bank N,|discrepancy N S c (box N i) (box N j)
        (naturalWeight b kap s kap0 N)|≤delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_each_bounded_block A delta hd,eventually_ge_atTop (2:ℕ)] with N H hN
  intro b kap s kap0 hb hk hs hg m r n e q a omega k ell hell
  exact H b kap s kap0 hb hk hs hg _ _ (physical_moduli m r n e q a omega k N (by omega) ell hell).1

/-- The complete pre-HB prime-product error for every such finite subset and signed row. -/
theorem eventually_bounded_moduli_prime (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kap s kap0 : ℝ),0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d ∧ (d:ℝ)<(N:ℝ)^(2/5:ℝ) ∧ N.Coprime d ∧ |c d|≤1) →
      |primeProductSignedError 2 N N S c (trimmedWeight b kap s kap0 N)|≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  let C := bankLogConstant
  have hC : 0<C := bankLogConstant_pos
  have hfee : 0<delta/C^2 := by positivity
  filter_upwards [eventually_each_bounded_block (A+2) (delta/C^2) hfee,
    eventually_actual_cutoffIndex_le_log 1 (by norm_num),eventually_one_le_nat_log] with N H hc hl
  intro b kap s kap0 hb hk hs hg S c hS
  let F := fun i j => discrepancy N S c (box N i) (box N j) (naturalWeight b kap s kap0 N)
  let L := Real.log (N:ℝ)
  have hl0 : 0<L := zero_lt_one.trans_le hl
  have hbnd := H b kap s kap0 hb hk hs hg S c hS
  let E := (delta/C^2)*(N:ℝ)/L^(A+2)
  have he : 0≤E := by dsimp [E]; positivity
  have hcnt : ((bank N).card:ℝ)≤C*L := by
    have hh : ((P5Z.ExactOriginalSmoothDyadicPartition.cutoffIndex N+2:ℕ):ℝ)≤C*L := by
      simpa [L,C] using hc.2
    apply le_trans ?_ hh
    simp only [bank,Finset.card_range,P5Z.ExactOriginalSmoothDyadicPartition.cutoffIndex]
    exact_mod_cast (show Nat.log2 N+1≤Nat.log2 N+1+2 by omega)
  rw [source_blocks]
  calc
    _ ≤ ∑ i∈bank N,∑ j∈bank N,E := (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i hi => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j hj => hbnd i hi j hj))))
    _ = ((bank N).card:ℝ)^2*E := by simp [nsmul_eq_mul,pow_two,mul_assoc]
    _ ≤ (C*L)^2*E := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hcnt 2) he
    _ = _ := by dsimp only [E,L]; rw [pow_add]; field_simp [hC.ne',hl0.ne'] <;> ring

/-- Unconditional original signed prime-product payment on every
remaining complete modulus of rough rank two. The same c appears inside
the progression and the exact mean, with no global support premise. -/
theorem eventually_original_prime_rank_two (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (b kap s kap0 : ℝ),0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),ell<1/1000 →
      let S := carrier m r n e q a omega k N ell
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      |primeProductSignedError 2 N N S c (trimmedWeight b kap s kap0 N)|≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_bounded_moduli_prime A delta hd,eventually_ge_atTop (2:ℕ)] with N H hN
  intro b kap s kap0 hb hk hs hg m r n e q a omega k ell hell
  exact H b kap s kap0 hb hk hs hg _ _ (physical_moduli m r n e q a omega k N (by omega) ell hell).1

/-- The joint sum of BOTH original HB alternatives over ALL original
dyadic labels of the actual remaining low-rank piece. -/
theorem eventually_original_atlases_rank_two (K : ℕ) (hK : 2≤K) {b kap : ℝ} (hb : 0<b) (hk : 0<kap)
    (A : ℕ) (delta : ℝ) (hd : 0<delta) :
    ∀ᶠ N : ℕ in atTop,∀ (s : ℝ) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96),
      ∀ (kap0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      ell<1/1000 →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖atlasPair hb hs hg K N kap0 zeta (carrier m r n e q a omega k N ell) c‖≤
        delta*(N:ℝ)/(Real.log (N:ℝ))^A := by
  filter_upwards [eventually_original_prime_rank_two A (delta/2) (half_pos hd),
    P4BOriginalRestrictedAtlasProper.eventually_subset_atlases K hK hb hk A (delta/2) (half_pos hd)]
    with N hprime hair
  intro s hs hg kap0 zeta m r n e q a omega k ell hell
  dsimp only
  intro hrange
  let S := carrier m r n e q a omega k N ell
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let DD : ℂ := (primeProductSignedError 2 N N S c (trimmedWeight b kap s kap0 N):ℝ)
  let HH := atlasPair hb hs hg K N kap0 zeta S c
  let fee := (delta/2)*(N:ℝ)/(Real.log (N:ℝ))^A
  have hp : ‖DD‖≤fee := by simpa only [DD,Complex.norm_real,Real.norm_eq_abs] using
    hprime b kap s kap0 hb hk hs hg m r n e q a omega k ell hell
  have hsub : S⊆Q omega N := fun d hd' => (Finset.mem_filter.mp (Finset.mem_inter.mp hd').1).1
  have hh : ‖DD-HH‖≤fee := hair s hs hg kap0 zeta m r n e q a omega k ((N:ℝ)^ell) S hsub hrange
  rw [norm_sub_rev] at hh
  have tri := norm_add_le (HH-DD) DD
  rw [sub_add_cancel] at tri
  exact tri.trans ((add_le_add hh hp).trans_eq (by dsimp only [fee]; ring))

end
end ImbalancedChen.P4BOriginalRankTwoGlobalPayment
