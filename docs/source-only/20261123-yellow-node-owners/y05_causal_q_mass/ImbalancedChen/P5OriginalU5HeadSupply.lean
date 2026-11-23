import ImbalancedChen.P5OriginalU5MarkedMass

/-! A nonconstant branch of the original maximum. For each larger prime
in the prescribed band, all smaller marked primes have the same physical
root and the same native root plan. The exact fibre has mass on the 1/q
scale; across the entire original rectangle its mass is bounded below
by a fixed constant. -/
namespace ImbalancedChen.P5OriginalU5HeadSupply

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite (pairSupport)
open P5OriginalU5MarkedMass
open P5OriginalU5PlateauPrimeBV (Policy integerRho fullModulus)
open P2OriginalU5SmallPartnerRootPayment (rootQ)
open P2GammaSelectedPhysicalTheta (reciprocalMass)
open P2LowerCapPlanIntegerRetention (coordinate coordinate_power)
open P2OriginalSelectedPairNativeData (rootLevel rootSeed selectedPolicy)
open P5OriginalU5NativeRootCover (policyAt marks)
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)

abbrev lowerBand (N : ℕ) := powerBand N (1/10) (11/100)
abbrev upperBand (N : ℕ) := powerBand N (7/50) (3/20)
def headLevel (N q : ℕ) := VariableEnvelope.A (coordinate N q)
def headFloor : ℝ := Real.log (11/10 : ℝ)/4
def upperFloor : ℝ := Real.log (15/14 : ℝ)/4

theorem separated_pair {N p q : ℕ} (hN : 2 ≤ N)
    (hp : p ∈ lowerBand N) (hq : q ∈ upperBand N) :
    (p,q) ∈ pairSupport N ∧ rootLevel false N (p,q) = headLevel N q ∧
      P2GammaU5PlateauGeometry.plateauLevel < headLevel N q := by
  obtain ⟨hpp,hpN,hplo,hphi⟩ := mem_powerBand.mp hp
  obtain ⟨hqp,hqN,hqlo,hqhi⟩ := mem_powerBand.mp hq
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hle (r : ℝ) (hr : r ≤ 1) : (N : ℝ)^r ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn.le hr
  have hpair : (p,q) ∈ pairSupport N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_, ?_⟩
    · exact mem_chenAdditivePrimeCarrier.mpr ⟨by exact_mod_cast hphi.trans_le (hle _ (by norm_num)),
        hpp, hpp.coprime_iff_not_dvd.mpr hpN⟩
    · exact mem_chenAdditivePrimeCarrier.mpr ⟨by exact_mod_cast hqhi.trans_le (hle _ (by norm_num)),
        hqp, hqp.coprime_iff_not_dvd.mpr hqN⟩
    · exact (Real.rpow_le_rpow_of_exponent_le hn.le
        (by norm_num : (417/5000 : ℝ) ≤ 1/10)).trans hplo
    · exact_mod_cast hphi.trans_le ((Real.rpow_le_rpow_of_exponent_le hn.le
        (by norm_num : (11/100 : ℝ) ≤ 7/50)).trans hqlo)
    · exact hqhi.trans_le (Real.rpow_le_rpow_of_exponent_le hn.le
        (by norm_num : (3/20 : ℝ) ≤ 19/125))
  have hp' := coordinate_power hn hpp.pos
  have hq' := coordinate_power hn hqp.pos
  have hu : (1/10 : ℝ) ≤ coordinate N p :=
    (Real.rpow_le_rpow_left_iff hn).mp (hplo.trans_eq hp'.symm)
  have ht : (7/50 : ℝ) ≤ coordinate N q :=
    (Real.rpow_le_rpow_left_iff hn).mp (hqlo.trans_eq hq'.symm)
  have ht' : coordinate N q < (3/20 : ℝ) :=
    (Real.rpow_lt_rpow_left_iff hn).mp (hq'.trans_lt hqhi)
  have htmu : coordinate N q ≤ VariableEnvelope.mu := by dsimp [VariableEnvelope.mu]; linarith
  have hsum : VariableEnvelope.mu ≤ coordinate N q + coordinate N p := by
    dsimp [VariableEnvelope.mu]; linarith
  have hhead : P2GammaU5PlateauGeometry.plateauLevel < headLevel N q := by
    rw [P2GammaU5PlateauGeometry.plateauLevel_exact]
    dsimp [headLevel, VariableEnvelope.A]
    linarith
  have hfall : VariableEnvelope.C (coordinate N q + coordinate N p) ≤ headLevel N q := by
    dsimp [VariableEnvelope.C, headLevel, VariableEnvelope.A]
    linarith
  refine ⟨hpair, ?_, hhead⟩
  change max (VariableEnvelope.v (coordinate N q))
    (max (VariableEnvelope.v (coordinate N q + coordinate N p))
      P2GammaU5PlateauGeometry.plateauLevel) = _
  rw [VariableEnvelope.v_eq_A htmu, VariableEnvelope.v_eq_C hsum]
  exact max_eq_left (max_le hfall hhead.le)

theorem eventually_head_supply :
    ∀ᶠ N : ℕ in atTop, (upperBand N).Nonempty ∧
      ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh) (b : ℚ) (e : ℝ),
      0 < e → e < 1/8 →
      let P := selectedPolicy R bank b false N
      let sigma := unitWeight N e P
      headFloor*upperFloor ≤ reciprocalMass
        (activeUnits N e P ((lowerBand N).product (upperBand N))) sigma ∧
      ∀ q ∈ upperBand N,
        let S := activeUnits N e P ((lowerBand N).product {q})
        headFloor/(q : ℝ) ≤ reciprocalMass S sigma ∧
        (∀ t ∈ S, rootQ N t = (N : ℝ)^(headLevel N q) ∧
          rootSeed false b N t = headLevel N q - 2*(b : ℝ) ∧
          P t = policyAt R bank b (headLevel N q) N t ∧
          P2GammaU5PlateauGeometry.plateauLevel < headLevel N q ∧
          integerRho N e P (fullModulus t 1) = 1) := by
  have hlo := eventually_powerBand_mass (by norm_num : (0 : ℝ)<1/10)
    (by norm_num : (1/10 : ℝ)<11/100)
  have hhi := eventually_powerBand_mass (by norm_num : (0 : ℝ)<7/50)
    (by norm_num : (7/50 : ℝ)<3/20)
  filter_upwards [hlo,hhi,eventually_ge_atTop (2 : ℕ)] with N hlow hhigh hN
  have hl : headFloor ≤ ∑ p ∈ lowerBand N, 1/(p : ℝ) := by
    simpa only [headFloor, show (11/100 : ℝ)/(1/10)=11/10 by norm_num] using hlow
  have hh : upperFloor ≤ ∑ q ∈ upperBand N, 1/(q : ℝ) := by
    simpa only [upperFloor, show (3/20 : ℝ)/(7/50)=15/14 by norm_num] using hhigh
  have hf : 0 < upperFloor := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have hl0 : 0 < headFloor := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  constructor
  · by_contra hn
    have hem : upperBand N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hem, Finset.sum_empty] at hh
    exact (not_le_of_gt hf) hh
  intro R mesh bank b e he he8
  let P := selectedPolicy R bank b false N
  have hall : (lowerBand N).product (upperBand N) ⊆ pairSupport N := by
    rintro ⟨p,q⟩ ht
    exact (separated_pair hN (Finset.mem_product.mp ht).1 (Finset.mem_product.mp ht).2).1
  dsimp only
  constructor
  · rw [active_product_mass hN he he8 P _ _ hall]
    exact mul_le_mul hl hh hf.le (hl0.le.trans hl)
  · intro q hq
    have hsub : (lowerBand N).product {q} ⊆ pairSupport N := by
      rintro ⟨p,r⟩ ht
      obtain ⟨hp,hr⟩ := Finset.mem_product.mp ht
      have heq : r=q := Finset.mem_singleton.mp hr
      subst r
      exact (separated_pair hN hp hq).1
    dsimp only
    constructor
    · rw [active_product_mass hN he he8 P _ _ hsub, Finset.sum_singleton]
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right hl (show 0 ≤ 1/(q : ℝ) by positivity)
    · rintro ⟨p,r⟩ ht
      obtain ⟨hp,hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
      have heq : r=q := Finset.mem_singleton.mp hr
      subst r
      obtain ⟨hpair,hv,hgt⟩ := separated_pair hN hp hq
      refine ⟨?_, ?_, P5OriginalU5NativeRootCover.native_policy_at R bank b
        (Finset.mem_filter.mpr ⟨hpair,hv⟩), hgt,
        (P5OriginalU5UnitMark.original_integer_unit hN he he8 P hpair).2⟩
      · change (N : ℝ)^(rootLevel false N (p,q)) = _
        rw [hv]
      · rw [rootSeed, hv]

/-- For the very same positive native unit rows, the inverse logarithmic
mass hypothesis of the older rank theorem fails at each individual
nonconstant head. This is a limitation of that conversion estimate. -/
theorem eventually_head_below_log_floor (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ e : ℝ, 0 < e → e < 1/8 → ∀ P : Policy,
      ∀ q ∈ upperBand N, reciprocalMass
        (activeUnits N e P ((lowerBand N).product {q})) (unitWeight N e P) <
          c/(Real.log (N : ℝ))^r := by
  let D := Real.log (11/10 : ℝ)+1
  have hD : 0 < D := by
    dsimp [D]; linarith [Real.log_pos (by norm_num : (1 : ℝ)<11/10)]
  have hm := tendsto_actualPrimeReciprocalMass (by norm_num : (0 : ℝ)<1/10)
    (by norm_num : (1/10 : ℝ)<11/100)
  have hlim : Real.log ((11/100 : ℝ)/(1/10)) < D := by
    rw [show (11/100 : ℝ)/(1/10) = 11/10 by norm_num]; dsimp [D]; linarith
  have hpow := (tendsto_nat_log_pow_div_rpow r (by norm_num : (0 : ℝ)<7/50)).eventually
    (lt_mem_nhds (div_pos hc hD))
  filter_upwards [hm.eventually (lt_mem_nhds hlim), hpow, eventually_ge_atTop (2 : ℕ)]
    with N hmN hpowN hN
  intro e he he8 P q hq
  have hqp := (mem_powerBand.mp hq).1
  have hqbound := (mem_powerBand.mp hq).2.2.1
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hqp.pos
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have hpowpos : 0 < (N : ℝ)^(7/50 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hn) _
  have hlpos := Real.log_pos hn
  have hsub : (lowerBand N).product {q} ⊆ pairSupport N := by
    rintro ⟨p,s⟩ ht
    obtain ⟨hp,hs⟩ := Finset.mem_product.mp ht
    have heq : s = q := Finset.mem_singleton.mp hs
    subst s
    exact (separated_pair hN hp hq).1
  have hsmall : (∑ p ∈ lowerBand N, 1/(p : ℝ)) ≤ D := by
    refine (Finset.sum_le_sum ?_).trans hmN.le
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_powerBand.mp hp).1.two_le
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [active_product_mass hN he he8 P _ _ hsub, Finset.sum_singleton, mul_one_div]
  calc
    _ ≤ D/(q : ℝ) := div_le_div_of_nonneg_right hsmall hq0.le
    _ ≤ D/(N : ℝ)^(7/50 : ℝ) := div_le_div_of_nonneg_left hD.le hpowpos hqbound
    _ < _ := (div_lt_div_iff₀ hpowpos (pow_pos hlpos r)).mpr (by
      have hh := (div_lt_div_iff₀ hpowpos hD).mp hpowN
      linarith only [hh])

end
end ImbalancedChen.P5OriginalU5HeadSupply
