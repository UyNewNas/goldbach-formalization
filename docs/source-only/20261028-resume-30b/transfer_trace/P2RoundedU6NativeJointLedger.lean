import ImbalancedChen.P2CompiledCausalPrimeSourceLower
import ImbalancedChen.P5JointNativeSignedRegroup

/-!
# Rounded lower U6 and original native U10/U11 in one signed ledger

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

`P5JointNativeSignedRegroup.LowerData` fixes the unrounded raw lower rho.
The finite-cell compiler cannot be passed to that constructor by identifying
it with a new raw policy. Here each sixth pair receives the actual rounded
coefficient, including its mesh. The negative joint side is unchanged:
FULL16 native low fourth-prime band unmasked, high band with the same
last-pair complement and the full D endpoint. The actual fallback is paid.

Count, exact coprime mean, signed primitive error and prime-centre deletion
are all evaluated against one signed fibre coefficient, before any norm.
No final Chen mean, distribution, certificate or D12 estimate is assumed.
-/

namespace ImbalancedChen.P2RoundedU6NativeJointLedger

noncomputable section
open scoped Classical BigOperators
open P5SelectedMaskTransport
open P5Z.U1011OriginalSixteenArithmeticProducts
open P5Z.U1011OriginalSixteenJointNearCapCompiler

structure RoundedLowerData where
  policy : (ℕ × ℕ) → List ℕ → Bool
  w : (ℕ × ℕ) → ℝ
  L : (ℕ × ℕ) → ℝ
  mesh : (ℕ × ℕ) → ℝ

abbrev lowerRows := P5JointNativeSignedRegroup.lowerRows

def lowerDivisors (D : RoundedLowerData) (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  P2LowerFiniteCellBetaCompiler.support N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (D.w t) (P5CausalRhoQuotientBridge.cutoff N)

def lowerRho (D : RoundedLowerData) (N : ℕ) (t : ℕ × ℕ) (d : ℕ) : ℝ :=
  P2LowerFiniteCellBetaCompiler.rho (D.policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (D.w t) (P5CausalRhoQuotientBridge.cutoff N) (D.mesh t) (D.L t) d

/-- The new lower row is tested on the actual quotient receivers. It is
not obtained by pretending the rounded support is a retained tree. -/
theorem rounded_quotient_sum_le_sifted (keep : List ℕ → Bool)
    (N b cap : ℕ) (w z tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (∑ d ∈ P2LowerFiniteCellBetaCompiler.support N cap w z,
      P2LowerFiniteCellBetaCompiler.rho keep N cap w z tau L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  rw [← P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N b,
        if ChenPrimeRough z q then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      have h := P2LowerFiniteCellBetaCompiler.rho_minorant keep N cap
        w z tau L hL hwL hwz hzcap (q : ℤ)
      have hind : actualSmallRoughIndicator N z (q : ℤ) =
          if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (q : ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
          Nat.coprime_comm]
      have hr := chenPrimeRough_iff_coprime_sieveProduct z
        (chenQuotientPrimeSource_data hq).2.2
      simpa only [Int.natAbs_natCast, hind, ← hr] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Literal selected sixth pairs keep the complement of E; the local
hypotheses are just beta attachment gates, not a desired mean bound. -/
theorem rounded_U6_lower (D : RoundedLowerData) (N : ℕ) (E : ℕ × ℕ → Prop)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < D.L t ∧ D.w t ≤ D.L t ∧ D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d *
        (chenPrimeAPCount N N ((t.1 * t.2) * d) -
          chenCentrePrimeAPCount N N ((t.1 * t.2) * d))) ≤ currentChenUpsilon6 N E := by
  rw [currentChenUpsilon6_eq_siftedQuotientPrimeSource]
  apply Finset.sum_le_sum
  intro t ht
  obtain ⟨hL, hwL, hwz⟩ := hgates t ht
  exact rounded_quotient_sum_le_sifted (D.policy t) N (t.1 * t.2)
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)) (D.w t)
    (P5CausalRhoQuotientBridge.cutoff N) (D.mesh t) (D.L t)
    hL hwL hwz (Nat.le_ceil _)

abbrev LowerMark := Σ _ : ℕ × ℕ, ℕ

def lowerMarks (D : RoundedLowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset LowerMark :=
  (lowerRows N E).sigma (lowerDivisors D N)

def lowerModulus (m : LowerMark) : ℕ := (m.1.1 * m.1.2) * m.2

def lowerSupport (D : RoundedLowerData) (N : ℕ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  (lowerMarks D N E).image lowerModulus

def lowerSigma (D : RoundedLowerData) (N : ℕ) (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  ∑ m ∈ (lowerMarks D N E).filter (fun m => lowerModulus m = q),
    lowerRho D N m.1 m.2

def support (D : RoundedLowerData) (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : Finset ℕ :=
  lowerSupport D N E ∪
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E

def sigma (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (q : ℕ) : ℝ :=
  lowerSigma D N E q -
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q

/-- The rounded side retains genuine positive primitive FULL moduli. This
uses the enlarged compiler support theorem from the first batch. -/
theorem lowerSupport_primitive (D : RoundedLowerData) (N : ℕ)
    (E : ℕ × ℕ → Prop) {q : ℕ} (hq : q ∈ lowerSupport D N E) :
    0 < q ∧ Nat.Coprime q N := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hm
  have hp := chenY6PrimeSelector_sieve_data (Finset.mem_filter.mp ht).1
  have hdpos : 0 < m.2 := Nat.pos_of_ne_zero
    (P2CompiledCausalPrimeSourceLower.support_squarefree N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (D.w m.1) (P5CausalRhoQuotientBridge.cutoff N) hd).ne_zero
  have hdcop := P2CompiledCausalPrimeSourceLower.support_coprime_target N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (D.w m.1) (P5CausalRhoQuotientBridge.cutoff N) hd
  exact ⟨mul_pos (lt_trans Nat.zero_lt_one hp.1) hdpos, hp.2.1.mul_left hdcop⟩

/-- Every modulus in the combined signed carrier has the actual primitive
residue N, including the native upper side. No distribution licence follows
merely from this arithmetic fact. -/
theorem support_primitive (D : RoundedLowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) {q : ℕ}
    (hq : q ∈ support D n N eta E) : 0 < q ∧ Nat.Coprime N q := by
  rcases Finset.mem_union.mp hq with hl | hu
  · have h := lowerSupport_primitive D N E hl
    exact ⟨h.1, h.2.symm⟩
  · have h :=
      P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport_profile
        hN heta hu
    exact ⟨h.1, h.2.2.1.symm⟩


/-- The two negative bands are the ORIGINAL native bands, including
unmasked low U10 and high U11 complement. No new E-filter is inserted. -/
theorem sigma_actual_low_high (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (q : ℕ) :
    sigma D n N eta E q = lowerSigma D N E q -
      P5JointNativeSignedRegroup.nativeLowSigma n N eta (fun _ => False) q -
      P5JointNativeSignedRegroup.nativeHighSigma n N eta E q := by
  unfold sigma
  rw [P5JointNativeSignedRegroup.native_sigma_low_high]
  ring

theorem lowerSigma_zero_off_support (D : RoundedLowerData) (N : ℕ)
    (E : ℕ × ℕ → Prop) {q : ℕ} (hq : q ∉ lowerSupport D N E) :
    lowerSigma D N E q = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  obtain ⟨hm, heq⟩ := Finset.mem_filter.mp hm
  exact (hq (Finset.mem_image.mpr ⟨m, hm, heq⟩)).elim

/-- Finite fibre grouping preserves actual tuple/divisor multiplicities. -/
theorem lower_pushforward (D : RoundedLowerData) (N : ℕ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) =
      ∑ q ∈ lowerSupport D N E, lowerSigma D N E q * F q := by
  have hm : (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) =
      ∑ m ∈ lowerMarks D N E,
        lowerRho D N m.1 m.2 * F (lowerModulus m) := by
    rw [lowerMarks, Finset.sum_sigma]
    rfl
  rw [hm]
  have hf := Finset.sum_fiberwise_of_maps_to (s := lowerMarks D N E)
    (t := lowerSupport D N E) (g := lowerModulus)
    (fun m hm => Finset.mem_image_of_mem lowerModulus hm)
    (fun m => lowerRho D N m.1 m.2 * F (lowerModulus m))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q _
  unfold lowerSigma
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

/-- Rounded U6 and native U10/U11 are subtracted INSIDE each physical
modulus fibre; the coefficient is allowed to be signed and non-unit. -/
theorem signed_pushforward (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) (F : ℕ → ℝ) :
    (∑ t ∈ lowerRows N E, ∑ d ∈ lowerDivisors D N t,
      lowerRho D N t d * F ((t.1 * t.2) * d)) -
    (∑ t ∈ ordinaryTuples n N E, ∑ d ∈
      P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t d * F (fullPrefix t * d)) =
      ∑ q ∈ support D n N eta E, sigma D n N eta E q * F q := by
  rw [lower_pushforward,
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward]
  have hl : (∑ q ∈ lowerSupport D N E, lowerSigma D N E q * F q) =
      ∑ q ∈ support D n N eta E, lowerSigma D N E q * F q := by
    apply Finset.sum_subset Finset.subset_union_left
    intro q hq hnot
    rw [lowerSigma_zero_off_support D N E hnot, zero_mul]
  have hu : (∑ q ∈
      P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E,
      P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q * F q) =
      ∑ q ∈ support D n N eta E,
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q * F q := by
    apply Finset.sum_subset Finset.subset_union_right
    intro q hq hnot
    rw [P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma_zero_off_support hnot,
      zero_mul]
  rw [hl, hu, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  unfold sigma
  ring

def estimator (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q *
    (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)

def exactCoprimeMean (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q *
    (finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) q / (Nat.totient q : ℝ))

def primitiveError (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q *
    finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q

def centreCorrection (D : RoundedLowerData) (n N : ℕ) (eta : ℚ)
    (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ support D n N eta E, sigma D n N eta E q * chenCentrePrimeAPCount N N q

/-- Count and exact coprime mean use the SAME signed physical coefficient. -/
theorem same_sigma_count_exact_mean (D : RoundedLowerData) (n N : ℕ)
    (eta : ℚ) (E : ℕ × ℕ → Prop) :
    estimator D n N eta E = exactCoprimeMean D n N eta E +
      primitiveError D n N eta E - centreCorrection D n N eta E := by
  unfold estimator exactCoprimeMean primitiveError centreCorrection
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N q =
      chenPrimeAPCount N N q := by simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [finitePrimitiveDiscrepancy, hAP]
  ring

/-- Replacing coprime mass by total prime mass has a signed modulus-prime
correction. It is retained even though the eventual primitive residue is N. -/
theorem exact_mean_total_prefix_correction (D : RoundedLowerData) (n N : ℕ)
    (eta : ℚ) (E : ℕ × ℕ → Prop) :
    exactCoprimeMean D n N eta E =
      ((chenPrimePrefix N).card : ℝ) *
        physicalDensitySum (support D n N eta E) (sigma D n N eta E) -
      ∑ q ∈ support D n N eta E, sigma D n N eta E q *
        (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
  unfold exactCoprimeMean physicalDensitySum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [chenPrimePrefix_coprime_mass]
  ring

/-- The actual negative count keeps both native bands and its literal
fallback. No bound for this fallback or a numerical joint kernel is assumed. -/
theorem original_joint_rounded_lower (D : RoundedLowerData) {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < D.L t ∧ D.w t ≤ D.L t ∧ D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    estimator D n N eta E - P5JointNativeSignedRegroup.fallback n N E ≤
      currentChenUpsilon6 N E - currentChenUpsilon10 N - currentChenUpsilon11 N E := by
  have hl := rounded_U6_lower D N E hgates
  have hu :=
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.original_count_upper_sigma
      (n := n) hN heta E
  have heq := signed_pushforward D n N eta E
    (fun q => chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)
  change _ - _ = estimator D n N eta E at heq
  have hn : (∑ t ∈ ordinaryTuples n N E, ∑ d ∈
      P5Z.U1011OriginalSixteenJointNearCapCompiler.support n N eta t,
      coefficient n N eta t d *
        (chenPrimeAPCount N N (fullPrefix t * d) -
          chenCentrePrimeAPCount N N (fullPrefix t * d))) =
      ∑ q ∈
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.modulusSupport n N eta E,
        P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E q *
          (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) :=
    P5Z.U1011OriginalSixteenJointNearCapModulusConvolution.exact_pushforward n N eta E _
  rw [hn] at heq
  change currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
    P5JointNativeSignedRegroup.fallback n N E + _ at hu
  linarith only [hl, hu, heq]

/-- This is a finite insertion into the ORIGINAL eleven-term ledger.
Only the local compiled beta gates are hypotheses. All other Chen terms,
exact signed discrepancy and the native fallback remain visible. -/
theorem original_eleven_term_rounded_same_sigma (D : RoundedLowerData)
    {n N : ℕ} {eta : ℚ} (hN : 1 < N) (heta : 0 < eta)
    (E : ℕ × ℕ → Prop)
    (hgates : ∀ t ∈ lowerRows N E,
      1 < D.L t ∧ D.w t ≤ D.L t ∧ D.w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    P5JointNativeSignedRegroup.otherRows N + exactCoprimeMean D n N eta E +
      primitiveError D n N eta E - centreCorrection D n N eta E -
      P5JointNativeSignedRegroup.fallback n N E ≤ currentChenPairedPrimeSum N E := by
  have h := original_joint_rounded_lower D hN heta E hgates
  rw [same_sigma_count_exact_mean D n N eta E] at h
  rw [currentChenPairedPrimeSum_eq_upsilon]
  unfold P5JointNativeSignedRegroup.otherRows
  linarith only [h]

end
end ImbalancedChen.P2RoundedU6NativeJointLedger
