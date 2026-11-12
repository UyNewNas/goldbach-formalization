import ImbalancedChen.Part5OriginalH430OwnedPrimeBoxWeight

/-! Absolute H_N normalization of the arithmetic prefactor for a fixed
ordered word rank. The support test ranges over the entire owned catalog.
The word contributes once and its accumulated coefficient is bounded by
the caller's specified mark. -/
namespace ImbalancedChen.Part5OriginalH430AbsoluteWordBox
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P2OriginalChildPhysicalNormalization P2EnhancedLowerPrimeChildCarriers
open P2EnhancedLowerPrimeChildGeometry Part5OriginalH430OwnedPrimeBoxWeight
open Part5OriginalH430OwnedThetaWord Part5OriginalH430OwnedMemberMass
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430SameQHistoryCells
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SelectedBankCarrierSupply
open Part5OriginalH430RootIntervalTheta (literalScale)

/-- The published root-interval module keeps this lemma private. Expose
its same li identity to the word comparison. -/
theorem literalScale_tendsto : Tendsto literalScale atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => Real.log (N : ℝ)/(N : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using
      (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh : Tendsto (fun N : ℕ =>
      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N * Real.log N / (N:ℝ) -
        (2/Real.log 2)*(Real.log N/(N:ℝ))) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      tendsto_currentChen_trueLi_normalized.sub (hz.const_mul (2/Real.log 2))
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro N
  rw [P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add]
  unfold literalScale
  ring

def price (N : ℕ) : ℝ := (|literalScale N|*boxRate N+|literalScale N-1|)*(4/frozenResidualFloor)

theorem price_tendsto : Tendsto price atTop (𝓝 0) := by
  simpa [price] using ((literalScale_tendsto.abs.mul boxRate_tendsto).add
    (literalScale_tendsto.sub_const 1).abs).mul_const (4/frozenResidualFloor)

private theorem nonneg_rate {N : ℕ} (h : 4 ≤ primeFloor N) : 0 ≤ boxRate N := by
  have ha : 0 < primeFloor N := by linarith only [h]
  exact sub_nonneg.mpr (one_le_pow₀ (by linarith only [div_pos (by norm_num : (0:ℝ)<4) ha]))

theorem owned_primeBox_price {N n m mesh : ℕ} {k : Root} {tau : ℝ} {c : RootKey n m}
    {h : Label N mesh} (hN : 2 ≤ N) (he : Even N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hA : 4 ≤ primeFloor N)
    (hh : h ∈ ownedMembers N n m mesh k tau c) :
    |thetaAtom N (cellQ N n c.1) (labelPrefix h) / singularNormalization N -
        (4/Lkey c h)*primeBoxWord (labelWord h)| ≤ price N * primeBoxWord (labelWord h) := by
  let ps := labelWord h
  let L := Lkey c h
  let b := primeBoxWord ps
  let T := thetaAtom N (cellQ N n c.1) (labelPrefix h)/singularNormalization N
  have hp (p : ℕ) (hm : p ∈ ps) : primeFloor N ≤ (p:ℝ) := owned_letter_floor hN ht ht' hn hh hm
  have hs := owned_support hN ht ht' hn hh
  dsimp only at hs
  have hL : frozenResidualFloor ≤ L := hs.2.2.1.1
  have hL0 := frozenResidualFloor_pos.trans_le hL
  have h4 : 0 ≤ 4/L := (div_pos (by norm_num) hL0).le
  have hprod : (0:ℝ) < ps.prod := Nat.cast_pos.mpr
    (Part5OriginalH430IntegerItineraries.prod_pos (old := ps) (fun p hps => by
      exact_mod_cast (show (0:ℝ)<p by linarith only [hp p hps,hA])))
  have hrec : 1/(ps.prod:ℝ) ≤ b := (div_le_iff₀ hprod).mpr (primeBox_ratio hA ps hp).1
  have hb : 0 ≤ b := (one_div_pos.mpr hprod).le.trans hrec
  have hr := nonneg_rate hA
  have herr := owned_primeBox_absolute hN he ht ht' hn hA hh
  have hb1 : |T-literalScale N*(4/L)*b| ≤ |literalScale N|*(4/L)*(boxRate N*b) := by
    apply herr.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) h4)
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hrec hr
  have hb2 : |literalScale N*(4/L)*b-(4/L)*b| = |literalScale N-1|*(4/L)*b := by
    rw [show literalScale N*(4/L)*b-(4/L)*b = (literalScale N-1)*(4/L)*b by ring,
      abs_mul,abs_mul,abs_of_nonneg h4,abs_of_nonneg hb]
  change |T-(4/L)*b| ≤ price N*b
  calc
    _ ≤ |T-literalScale N*(4/L)*b| + |literalScale N*(4/L)*b-(4/L)*b| := abs_sub_le _ _ _
    _ ≤ (|literalScale N|*boxRate N+|literalScale N-1|)*(4/L)*b := by
      rw [hb2]
      linarith only [hb1]
    _ ≤ _ := by
      unfold price
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by norm_num) frozenResidualFloor_pos hL)
        (add_nonneg (mul_nonneg (abs_nonneg _) hr) (abs_nonneg _))) hb

def wordError {r : ℕ} (N n m mesh : ℕ) (k : Root) (tau : ℝ) (v : Fin (r+1) → ℕ) : ℝ :=
  let c := keyAt N n m k tau (v 0)
  let ps := List.ofFn v
  let Q := cellQ N n c.1
  if ∃ h ∈ ownedMembers N n m mesh k tau c, labelWord h = ps then
    |thetaAtom N Q ps.prod / singularNormalization N -
      (4/physicalLevel N Q ps)*primeBoxWord ps| else 0

/-- Preassigned prime-box endpoints, then one arithmetic threshold valid
for every precision, owner, root and bounded changing word mark. The error
is the sum of absolute H_N-normalized arithmetic-prefactor differences. -/
theorem uniform_wordBox_normalization {r : ℕ} (a b : Fin (r+1) → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) {eps : ℝ} (heps : 0 < eps) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N → ∀ n m mesh : ℕ, ∀ k : Root, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ w : (Fin (r+1) → ℕ) → ℝ, (∀ v ∈ actualPrimeBoxTuples N a b, |w v| ≤ 1) →
        ∑ v ∈ actualPrimeBoxTuples N a b, |w v| * wordError N n m mesh k tau v ≤ eps := by
  have hl : Tendsto (fun N => price N*actualPrimeBoxMass N a b) atTop (𝓝 0) := by
    simpa only [zero_mul] using price_tendsto.mul (tendsto_actualPrimeBoxMass a b ha hab)
  have hall := ((eventually_ge_atTop (2:ℕ)).and (primeFloor_tendsto.eventually_ge_atTop 4)).and
    (hl.eventually (eventually_lt_nhds heps))
  obtain ⟨T,hT⟩ := eventually_atTop.1 hall
  refine ⟨T,?_⟩
  intro N hN he n m mesh k tau ht ht' hn w hw
  obtain ⟨⟨hN2,hA⟩,hbound⟩ := hT N hN
  have hprice : 0 ≤ price N := by
    unfold price
    exact mul_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (nonneg_rate hA)) (abs_nonneg _))
      (div_nonneg (by norm_num) frozenResidualFloor_pos.le)
  apply le_trans _ hbound.le
  unfold actualPrimeBoxMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  let c := keyAt N n m k tau (v 0)
  by_cases hs : ∃ h ∈ ownedMembers N n m mesh k tau c, labelWord h = List.ofFn v
  · obtain ⟨h,hh,heq⟩ := hs
    have hrow := owned_primeBox_price hN2 he ht ht' hn hA hh
    change |thetaAtom N (cellQ N n c.1) (labelWord h).prod / singularNormalization N -
        (4/physicalLevel N (cellQ N n c.1) (labelWord h))*primeBoxWord (labelWord h)| ≤ _ at hrow
    rw [heq,primeBoxWord_ofFn] at hrow
    rw [wordError,if_pos (show ∃ h ∈ ownedMembers N n m mesh k tau c,
      labelWord h = List.ofFn v from ⟨h,hh,heq⟩),primeBoxWord_ofFn]
    exact ((mul_le_mul_of_nonneg_right (hw v hv) (abs_nonneg _)).trans_eq (one_mul _)).trans hrow
  · rw [wordError,if_neg hs,mul_zero]
    exact mul_nonneg hprice (actualPrimeBoxWeight_nonneg hv)

end
end ImbalancedChen.Part5OriginalH430AbsoluteWordBox

