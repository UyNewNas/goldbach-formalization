import ImbalancedChen.P3OriginalU5JointCountReserve

/-! The signed high-modulus remainder on the actual U5 rectangle has
at least four rough primes. Pulling it back to the unique small/rough
factorization preserves the two external primes and the sign of beta. -/

namespace ImbalancedChen.P3OriginalU5JointHighRank

noncomputable section
open Filter
open scoped Classical BigOperators Topology
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)
open P2GammaU5PlateauGeometry (rectangle mem_rectangle boxHi)
open P2LowerCanonicalRetainedTrace (canonical_subword_of_universe)
open P2LowerFiniteCellRounding (universe_rough)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5CoarseRootV (meshStep)
open P3OriginalU5JointBetaAttachment (rho rho_at_product small betaMinus betaPlus)
open P3OriginalU5JointCellCoefficient (coefficient roughCarrier)
open P3OriginalU5JointClassicalPayment (highPrimitive lowPrimitive correction primitive)
open P3OriginalU5RoundedCountInsertion (roundedSupport)
open P5OriginalU5CausalFinite (attachmentNu cutoff smallLevel)
open P5OriginalU5PlateauPrimeBV (fullModulus markedProduct)

/-- At the chosen beta precision, three rough primes, both marks and the
complete active small factor still have total exponent less than 0.4912. -/
theorem rank_three_level (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ) (m : ℕ)
    {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : epsilon < 1/272) (tau : ℝ)
    {t : ℕ × ℕ} (ht : t ∈ rectangle N) {s d : ℕ}
    (hs : s ∈ small N epsilon) (hd : d ∈ roughCarrier N epsilon)
    (hk : rho R bank b m N epsilon tau t (s*d) ≠ 0) (hr : d.primeFactorsList.length ≤ 3) :
    (fullModulus t (s*d) : ℝ) < (N : ℝ) ^ (307/625 : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hNr
  have hcut : 1 ≤ cutoff N := Real.one_le_rpow hNr.le (by norm_num)
  rw [rho_at_product R bank b m N epsilon tau t hs hd] at hk
  let c := coefficient R bank b m N epsilon tau (t,d)
  change c * (if 0 ≤ c then betaMinus N epsilon s else betaPlus N epsilon s) ≠ 0 at hk
  have hb := (mul_ne_zero_iff.mp hk).2
  have hsmall : (s : ℝ) ≤ smallLevel N epsilon := by
    by_cases hc : 0 ≤ c
    · rw [if_pos hc] at hb
      exact (actualSmallRosserMinus_active hb).2.1.le
    · rw [if_neg hc] at hb
      exact (actualSmallRosserPlus_active hb).2.1.le
  obtain ⟨hsub, hprod⟩ := canonical_subword_of_universe _ _ _ _ hd
  have hu := List.prod_map_le_prod_map₀ (fun p : ℕ => (p : ℝ)) (fun _ : ℕ => cutoff N)
    (fun p _ => Nat.cast_nonneg p) (fun p hp => (mem_roughPrimeUniverse_upper (hsub.subset hp)).le)
  have hrough : (d : ℝ) ≤ cutoff N ^ 3 := by
    apply le_trans ?_ (pow_le_pow_right₀ hcut hr)
    simpa only [List.map_const', List.prod_replicate, actualNatList_cast_prod, hprod, List.length_reverse] using hu
  have hp := mem_actualPrimeBoxTuples_iff.mp ((mem_rectangle N t).mp ht)
  have h1 : (t.1 : ℝ) ≤ (N : ℝ)^(11/100 : ℝ) := by
    simpa only [boxHi, Matrix.cons_val_zero] using (hp 0).2.2.2.le
  have h2 : (t.2 : ℝ) ≤ (N : ℝ)^(13/100 : ℝ) := by
    simpa only [boxHi, Matrix.cons_val_one, Matrix.cons_val_zero] using (hp 1).2.2.2.le
  calc
    _ = ((t.1 : ℝ)*t.2)*((s : ℝ)*d) := by simp only [fullModulus, markedProduct, Nat.cast_mul]
    _ ≤ ((N : ℝ)^(11/100 : ℝ)*(N : ℝ)^(13/100 : ℝ))*(smallLevel N epsilon * cutoff N^3) :=
      mul_le_mul (mul_le_mul h1 h2 (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _))
        (mul_le_mul hsmall hrough (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _))
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (Real.rpow_nonneg hNp.le _) (Real.rpow_nonneg hNp.le _))
    _ = (N : ℝ)^((11/100 + 13/100) + (attachmentNu*epsilon + ((417/5000 + 417/5000) + 417/5000)) : ℝ) := by
      simp only [smallLevel, cutoff, Real.rpow_add hNp]
      ring
    _ < _ := Real.rpow_lt_rpow_of_exponent_lt hNr (by dsimp only [attachmentNu]; linarith only [he])

/-- The actual integer BV cutoff eventually contains every modulus below
the fixed rectangle exponent. B is fixed before the target threshold. -/
theorem eventually_low_rank_le_BV (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, Nat.floor ((N : ℝ) ^ (307/625 : ℝ)) ≤ panModulusCutoff N B := by
  let delta := (1/2 : ℝ) - 307/625
  have hd : 0 < delta := by norm_num [delta]
  have hlim := tendsto_nat_log_pow_div_rpow (Nat.ceil B) hd
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)), eventually_ge_atTop (2 : ℕ)] with N hsmall hL hN
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 < (N : ℝ)^delta := Real.rpow_pos_of_pos hNp delta
  have hs : Real.log (N : ℝ)^Nat.ceil B ≤ (N : ℝ)^delta := by
    have h := (div_lt_iff₀ hδ).mp hsmall
    simpa only [one_mul] using h.le
  have hpow : Real.log (N : ℝ) ^ B ≤ (N : ℝ)^delta := by
    calc
      _ ≤ Real.log (N : ℝ) ^ (Nat.ceil B : ℝ) := Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil B)
      _ = Real.log (N : ℝ) ^ Nat.ceil B := Real.rpow_natCast _ _
      _ ≤ _ := hs
  unfold panModulusCutoff
  apply Nat.floor_mono
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) B)).mpr
  calc
    _ ≤ (N : ℝ)^(307/625 : ℝ) * (N : ℝ)^delta :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; norm_num [delta]

/-- A physical sum over the unique small factor and its rough divisor.
Each residual rank is at least four; the two prime marks remain external. -/
def highRankPrimitive (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m N : ℕ) (epsilon tau : ℝ) (Q : ℕ) : ℝ :=
  ∑ t ∈ rectangle N, ∑ x ∈ (smallRoughPairs (small N epsilon) (roughCarrier N epsilon)).filter
      (fun x => Q < fullModulus t (x.1*x.2) ∧ 4 ≤ x.2.primeFactorsList.length),
    let c := coefficient R bank b m N epsilon tau (t,x.2)
    (c * (if 0 ≤ c then betaMinus N epsilon x.1 else betaPlus N epsilon x.1)) *
      primitive N (fullModulus t (x.1*x.2))

theorem highPrimitive_eq_highRank (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : epsilon < 1/272) (tau : ℝ)
    {Q : ℕ} (hQ : Nat.floor ((N : ℝ) ^ (307/625 : ℝ)) ≤ Q) :
    highPrimitive R bank b m N epsilon tau (rectangle N) Q = highRankPrimitive R bank b m N epsilon tau Q := by
  unfold highPrimitive highRankPrimitive
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_filter]
  let F (k : ℕ) := if Q < fullModulus t k then rho R bank b m N epsilon tau t k * primitive N (fullModulus t k) else 0
  change (∑ k ∈ smallRoughModuli (small N epsilon) (roughCarrier N epsilon), F k) = _
  rw [sum_smallRoughModuli (fun _ h => actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ h)
    (fun _ h => universe_rough _ _ _ _ h) F]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hs, hd⟩ := Finset.mem_product.mp hx
  dsimp only [F]
  by_cases hhi : Q < fullModulus t (x.1*x.2)
  · rw [if_pos hhi]
    by_cases h4 : 4 ≤ x.2.primeFactorsList.length
    · rw [if_pos ⟨hhi, h4⟩, rho_at_product R bank b m N epsilon tau t hs hd]
    · rw [if_neg (fun h => h4 h.2)]
      have hz : rho R bank b m N epsilon tau t (x.1*x.2) = 0 := by
        by_contra hn
        have hsmall := rank_three_level R bank b m hN he tau ht hs hd hn (by omega)
        exact (not_lt_of_ge ((Nat.le_floor hsmall.le).trans hQ)) hhi
      rw [hz, zero_mul]
  · rw [if_neg hhi, if_neg (fun h => hhi h.1)]

/-- The positive count reserve with precisely the surviving high ranks,
without any estimate for their signed primitive sum. -/
theorem exists_joint_highRank_count_reserve :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : PairRange, ∃ c : ℝ, 0 < c ∧
      ∀ epsilonMax : ℝ, 0 < epsilonMax →
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧ epsilon < 1/272 ∧
          ∀ m : ℕ, meshStep R m ≤ 1/32000 → ∀ {mesh : ℕ} (bank : CandidateBank mesh),
            ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
              ∀ tau : ℝ, 0 < tau → tau ≤ tau0 → ∀ N ≥ N0, Even N →
                c * singularNormalization N + highRankPrimitive R bank (1/1000) m N epsilon tau (panModulusCutoff N B) ≤
                    currentChenUpsilon5 N ∧
                |lowPrimitive R bank (1/1000) m N epsilon tau (rectangle N) (panModulusCutoff N B)| +
                  |correction R bank (1/1000) m N epsilon tau (rectangle N)| ≤ c * singularNormalization N ∧
                ∀ (t : ℕ × ℕ) (k : ℕ), rho R bank (1/1000) m N epsilon tau t k ≠ 0 →
                  (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  obtain ⟨B, hB, hres⟩ := P3OriginalU5JointCountReserve.exists_joint_rectangle_count_reserve
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp (eventually_low_rank_le_BV B)
  refine ⟨B, hB, ?_⟩
  intro R
  obtain ⟨c, hc, hR⟩ := hres R
  refine ⟨c, hc, ?_⟩
  intro epsilonMax hmax
  obtain ⟨epsilon, he, he8, hemax, he272, hs⟩ := hR epsilonMax hmax
  refine ⟨epsilon, he, he8, hemax, he272, ?_⟩
  intro m hm mesh bank
  obtain ⟨tau0, htau0, Ns, hNs, hh⟩ := hs m hm bank
  refine ⟨tau0, htau0, max Ns Nb, hNs.trans (le_max_left _ _), ?_⟩
  intro tau htau ht N hN hEven
  have hsN := (le_max_left Ns Nb).trans hN
  have h := hh tau htau ht N hsN hEven
  rw [highPrimitive_eq_highRank R bank (1/1000) m (hNs.trans hsN) he272 tau
    (hNb N ((le_max_right _ _).trans hN))] at h
  exact h

end
end ImbalancedChen.P3OriginalU5JointHighRank
