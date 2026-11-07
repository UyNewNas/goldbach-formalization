import ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW
import ImbalancedChen.Part3TransposedGCDPoissonMask
import ImbalancedChen.Part3CanonicalReciprocalData
import ImbalancedChen.Part3TransposedPrimitiveUPayment

/-!
# Deleting large supported parts of the original paired alpha integers

The literal asymmetric mask is applied before splitting any tail gcd. Whole W,
raw Poisson zero and the complete integer Fourier remainder retain that same
mask, every original physical fiber, and the full primitive first-factor carrier.
The final payment includes the original beta and gamma1 second moments.

Finite square-support and square-divisor-density proofs below are adapted from
Apache-2.0 goldbach sources at commit 09b97db5764ade1246bfb77206baa1b124760958:
* MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryLargeSupport.lean:15-46,
  SHA256 ef580af4abaac65d7db868c3cc060414a19af89ad6c0ca1af006edfe98753276;
* MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryLargeSupportDensity.lean:19-84,
  SHA256 09e327646a4c68a197bc02970018f6dc4b52b65b02c94262d32753df98d221c4.
Changes: private namespace isolation and specialization to the already owned
CanonicalReciprocalData.supportedPart. The original WGCD/phase import chain is
not imported. These source adaptations assert no native-object replay.

The whole-W pointwise proofs are local extractions of the already owned
Part3SharedFirstFactorLargePairedGCDW. The finite tail grouping is reconstructed
locally from the actual definitions and public lcm moment. No private imported
name or unaccepted Fourier-bound module supplies an estimate.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter Topology
open scoped BigOperators Pointwise
open TransposedGCDPoissonMask TransposedPrimitiveUPayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def smallPairedLargeSupportedMask (Ybeta Ysupport : ℝ) (N1 N2 : ℕ) : Prop :=
  ((N1.gcd N2 : ℝ) ≤ Ybeta) ∧
    Ysupport < (CanonicalReciprocalData.supportedPart
      (N1 / N1.gcd N2) (N1.gcd N2) : ℝ)

def MediumAtom.sharedSmallPairedLargeSupportedW (d : MediumAtom) (Ybeta Ysupport : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (∑ N1 ∈ d.transposedAtom.betaCarrier,
      (∑ N2 ∈ d.transposedAtom.betaCarrier,
        (if smallPairedLargeSupportedMask Ybeta Ysupport N1 N2 then
          d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
            (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight N1 N2
        else 0)))

def MediumAtom.sharedSmallPairedLargeSupportedZero (d : MediumAtom) (Ybeta Ysupport : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (∑ N1 ∈ d.transposedAtom.betaCarrier,
      (∑ N2 ∈ d.transposedAtom.betaCarrier,
        (if smallPairedLargeSupportedMask Ybeta Ysupport N1 N2 then
          d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
            (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight N1 N2
        else 0)))

def MediumAtom.sharedSmallPairedLargeSupportedNonzero (d : MediumAtom) (Ybeta Ysupport : ℝ) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (∑ N1 ∈ d.transposedAtom.betaCarrier,
      (∑ N2 ∈ d.transposedAtom.betaCarrier,
        (if smallPairedLargeSupportedMask Ybeta Ysupport N1 N2 then
          d.transposedAtom.beta N1 * star (d.transposedAtom.beta N2) *
            (d.q1SliceAtom p).transposedAtom.commonFactorPairNonzeroWeight N1 N2
        else 0)))

namespace SharedFirstFactorLargeSupportedDeletion

/-- A squarefree integer supported on the primes of a positive integer divides it. -/
private theorem squarefree_dvd_of_prime_support {a d : ℕ} (ha : Squarefree a)
    (hd : 0 < d) (hs : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ d) : a ∣ d := by
  rw [← Nat.prod_primeFactors_of_squarefree ha]
  apply (Nat.prod_primeFactors_dvd_iff hd.ne').mpr
  intro p hp
  exact Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp,
      hs p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), hd.ne'⟩

/-- The square witness uses the squarefree part of `s`, so it need not
contain any individually large prime. -/
private theorem exists_square_dvd_of_prime_support {s d : ℕ} (hs : 0 < s) (hd : 0 < d)
    (hsd : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) :
    ∃ b : ℕ, 0 < b ∧ s ≤ b ^ 2 ∧ b ^ 2 ∣ d * s := by
  obtain ⟨a, c, ha, hc, he, hsq⟩ := Nat.sq_mul_squarefree_of_pos hs
  have has : a ∣ s := he ▸ dvd_mul_left a (c ^ 2)
  have had : a ∣ d :=
    squarefree_dvd_of_prime_support hsq hd (fun p hp hpa => hsd p hp (hpa.trans has))
  have hb : (c * a) ^ 2 = a * s := by rw [← he]; ring
  refine ⟨c * a, Nat.mul_pos hc ha, ?_, ?_⟩
  · rw [hb]
    exact Nat.le_mul_of_pos_left s ha
  · rw [hb]
    exact mul_dvd_mul_right had s

/-- The extraction transfers to any multiple of `d * s`. -/
private theorem exists_square_dvd_of_supported_mul_dvd {s d n : ℕ}
    (hs : 0 < s) (hd : 0 < d)
    (hsd : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) (hn : d * s ∣ n) :
    ∃ b : ℕ, 0 < b ∧ s ≤ b ^ 2 ∧ b ^ 2 ∣ n := by
  obtain ⟨b, hb, hsb, hbd⟩ := exists_square_dvd_of_prime_support hs hd hsd
  exact ⟨b, hb, hsb, hbd.trans hn⟩



/-- Positive integers at most `T` with a square divisor whose root exceeds `Z`. -/
private def largeSquareDivisorSet (T : ℕ) (Z : ℝ) : Finset ℕ := by
  classical
  exact (Ioc 0 T).filter (fun n => ∃ b : ℕ, Z < (b : ℝ) ∧ b ^ 2 ∣ n)

/-- The square-root upper endpoint and the floor lower endpoint are exact. -/
private theorem largeSquareDivisorSet_eq_biUnion (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    largeSquareDivisorSet T Z =
      (Ioc ⌊Z⌋₊ T.sqrt).biUnion (fun b => (Ioc 0 T).filter (fun n => b ^ 2 ∣ n)) := by
  ext n
  simp only [largeSquareDivisorSet, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨hn, b, hb, hbn⟩
    refine ⟨b, mem_Ioc.mpr ⟨(Nat.floor_lt hZ).mpr hb, ?_⟩, hn, hbn⟩
    exact Nat.le_sqrt'.mpr ((Nat.le_of_dvd (mem_Ioc.mp hn).1 hbn).trans
      (mem_Ioc.mp hn).2)
  · rintro ⟨b, hb, hn, hbn⟩
    exact ⟨hn, b, (Nat.floor_lt hZ).mp (mem_Ioc.mp hb).1, hbn⟩

/-- An exact integer floor-sum majorant, with no asymptotic endpoint convention. -/
private theorem card_largeSquareDivisorSet_le_floor_sum (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    (largeSquareDivisorSet T Z).card ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, T / b ^ 2 := by
  rw [largeSquareDivisorSet_eq_biUnion T hZ]
  calc
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((Ioc 0 T).filter (fun n => b ^ 2 ∣ n)).card :=
      card_biUnion_le
    _ = _ := sum_congr rfl (fun b _ => Nat.Ioc_filter_dvd_card_eq_div T (b ^ 2))

/-- A uniform reciprocal-square estimate retains the natural floor at the cutoff. -/
private theorem card_largeSquareDivisorSet_le_floor (T : ℕ) {Z : ℝ} (hZ : 0 ≤ Z) :
    ((largeSquareDivisorSet T Z).card : ℝ) ≤ 2 * T / ((⌊Z⌋₊ : ℝ) + 1) := by
  have htail :
      (∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((b : ℝ) ^ 2)⁻¹) ≤ 2 / ((⌊Z⌋₊ : ℝ) + 1) := by
    calc
      _ = ∑ b ∈ Ioo ⌊Z⌋₊ (T.sqrt + 1), ((b : ℝ) ^ 2)⁻¹ := by
        congr 1
        ext b
        simp only [mem_Ioc, mem_Ioo]
        omega
      _ ≤ _ := sum_Ioo_inv_sq_le _ _
  calc
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((T / b ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast card_largeSquareDivisorSet_le_floor_sum T hZ
    _ ≤ ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, (T : ℝ) / (b : ℝ) ^ 2 := by
      apply sum_le_sum
      intro b _
      exact_mod_cast (Nat.cast_div_le (m := T) (n := b ^ 2) (α := ℝ))
    _ = (T : ℝ) * ∑ b ∈ Ioc ⌊Z⌋₊ T.sqrt, ((b : ℝ) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, mul_sum]
    _ ≤ (T : ℝ) * (2 / ((⌊Z⌋₊ : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg T)
    _ = _ := by ring

/-- Large square divisors have density at most `2 / Z` for every positive cutoff. -/
private theorem card_largeSquareDivisorSet_le (T : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    ((largeSquareDivisorSet T Z).card : ℝ) ≤ 2 * T / Z := by
  calc
    _ ≤ 2 * T / ((⌊Z⌋₊ : ℝ) + 1) := card_largeSquareDivisorSet_le_floor T hZ.le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hZ (Nat.lt_floor_add_one Z).le

/-- Real upper endpoints are truncated exactly before the density estimate. -/
private theorem card_largeSquareDivisorSet_le_real {T Z : ℝ} (hT : 0 ≤ T) (hZ : 0 < Z) :
    ((largeSquareDivisorSet ⌊T⌋₊ Z).card : ℝ) ≤ 2 * T / Z := by
  calc
    _ ≤ 2 * (⌊T⌋₊ : ℝ) / Z := card_largeSquareDivisorSet_le ⌊T⌋₊ hZ
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Nat.floor_le hT) (by positivity)) hZ.le



end SharedFirstFactorLargeSupportedDeletion

/-- A positive canonical supported quotient supplies a square divisor at least
as large as that quotient. Equality is retained in this statement. -/
theorem canonicalSupportedPart_square_witness (N2 : ℕ) {N1 : ℕ} (hN1 : 0 < N1) :
  ∃ b : ℕ, 0 < b ∧
    CanonicalReciprocalData.supportedPart (N1 / N1.gcd N2) (N1.gcd N2) ≤ b ^ 2 ∧
      b ^ 2 ∣ N1 := by
  let g := N1.gcd N2
  have hg : 0 < g := Nat.gcd_pos_of_pos_left N2 hN1
  have hu : 0 < N1 / g :=
    Nat.div_pos (Nat.le_of_dvd hN1 (Nat.gcd_dvd_left N1 N2)) hg
  apply SharedFirstFactorLargeSupportedDeletion.exists_square_dvd_of_supported_mul_dvd
    (CanonicalReciprocalData.supportedPart_pos _ _) hg
    (fun _ hp hps ↦ CanonicalReciprocalData.prime_dvd_supportedPart hp hps)
  calc
    g * CanonicalReciprocalData.supportedPart (N1 / g) g ∣ g * (N1 / g) :=
      mul_dvd_mul_left g (CanonicalReciprocalData.supportedPart_dvd hu g)
    _ = N1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left N1 N2)

/-- Positive finite carriers with a large square divisor are sparse even for
cutoffs below one. Zero is excluded by the literal prefix hypothesis. -/
theorem card_squareDivisorThinCarrier_le {T Y : ℝ} (hT : 0 ≤ T) (hY : 0 < Y)
    (N : Finset ℕ) (hN : N ⊆ Finset.Ioc 0 (Nat.floor T)) :
    (((N.filter (fun n => ∃ b : ℕ, 0 < b ∧ b ^ 2 ∣ n ∧ Y < (b : ℝ) ^ 2)).card : ℝ)) ≤
      2 * T / Real.sqrt Y := by
  have hsub : N.filter (fun n => ∃ b : ℕ, 0 < b ∧ b ^ 2 ∣ n ∧ Y < (b : ℝ) ^ 2) ⊆
      SharedFirstFactorLargeSupportedDeletion.largeSquareDivisorSet
        (Nat.floor T) (Real.sqrt Y) := by
    intro n hn
    obtain ⟨hnN, b, _hb, hbn, hYb⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hN hnN, b,
      (Real.sqrt_lt hY.le (Nat.cast_nonneg b)).mpr hYb, hbn⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (SharedFirstFactorLargeSupportedDeletion.card_largeSquareDivisorSet_le_real
      hT (Real.sqrt_pos.mpr hY))

/-- Keep both unit gates, the same-p congruence and the exact support mask.
The second coordinate is counted by its quotient block; diagonals remain. -/
theorem card_sharedPrimitiveLargeSupportedPairs_le {T Y : ℝ}
    (hT : 0 ≤ T) (hY : 0 < Y) {p : ℕ} (hp : 0 < p)
    (N : Finset ℕ) (hN : N ⊆ Finset.Ioc 0 (Nat.floor T)) (Ybeta : ℝ) :
    (((N ×ˢ N).filter (fun z => z.1.Coprime p ∧ z.2.Coprime p ∧
      Nat.ModEq p z.1 z.2 ∧ smallPairedLargeSupportedMask Ybeta Y z.1 z.2)).card : ℝ) ≤
        (2 * T / Real.sqrt Y) * (T / (p : ℝ) + 1) := by
  let S := N.filter (fun n => ∃ b : ℕ, 0 < b ∧ b ^ 2 ∣ n ∧ Y < (b : ℝ) ^ 2)
  let P := (N ×ˢ N).filter (fun z => z.1.Coprime p ∧ z.2.Coprime p ∧
    Nat.ModEq p z.1 z.2 ∧ smallPairedLargeSupportedMask Ybeta Y z.1 z.2)
  have hcard : P.card ≤ S.card * (Nat.floor T / p + 1) := by
    calc
      _ ≤ (S ×ˢ Finset.range (Nat.floor T / p + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ ↦ (z.1, z.2 / p))
        · intro z hz
          obtain ⟨hzN, _hz1p, _hz2p, _hzmod, hzmask⟩ := Finset.mem_filter.mp hz
          obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzN
          obtain ⟨b, hb, hsb, hbn⟩ := canonicalSupportedPart_square_witness z.2
            (Finset.mem_Ioc.mp (hN hz1)).1
          have hYb : Y < (b : ℝ) ^ 2 :=
            hzmask.2.trans_le (by exact_mod_cast hsb)
          exact Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨hz1, b, hb, hbn, hYb⟩,
              Finset.mem_range.mpr (Nat.lt_succ_of_le
                (Nat.div_le_div_right (Finset.mem_Ioc.mp (hN hz2)).2))⟩
        · intro z hz w hw he
          obtain ⟨_, _hz1p, _hz2p, hzmod, _⟩ := Finset.mem_filter.mp hz
          obtain ⟨_, _hw1p, _hw2p, hwmod, _⟩ := Finset.mem_filter.mp hw
          have hfirst : z.1 = w.1 := by
            simpa only using congrArg (fun t : ℕ × ℕ ↦ t.1) he
          have hquot : z.2 / p = w.2 / p := by
            simpa only using congrArg (fun t : ℕ × ℕ ↦ t.2) he
          apply Prod.ext hfirst
          apply Nat.ext_div_modEq hquot
          rw [hfirst] at hzmod
          exact hzmod.symm.trans hwmod
      _ = _ := by simp only [Finset.card_product, Finset.card_range]
  have hquot : ((Nat.floor T / p : ℕ) : ℝ) ≤ T / (p : ℝ) :=
    (show ((Nat.floor T / p : ℕ) : ℝ) ≤ (Nat.floor T : ℝ) / p from
      Nat.cast_div_le).trans
        (div_le_div_of_nonneg_right (Nat.floor_le hT)
          (show (0 : ℝ) ≤ p by exact_mod_cast hp.le))
  calc
    _ ≤ (S.card : ℝ) * ((Nat.floor T / p : ℕ) + 1 : ℝ) := by exact_mod_cast hcard
    _ ≤ (2 * T / Real.sqrt Y) * (T / (p : ℝ) + 1) := by
      exact mul_le_mul (card_squareDivisorThinCarrier_le hT hY N hN)
        (add_le_add hquot le_rfl) (by positivity) (by positivity)

namespace SharedFirstFactorLargeSupportedDeletion

/- The auxiliary beta=1 record has the original geometry. The row proof
uses the public owned tau-four bound, never a mangled private name. -/
private theorem absoluteRow_le_tauFour_of_not_dvd
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m n : ℕ)
    (hn : ¬(n : ℤ) ∣ d.residue) :
    d.absoluteFactorModulusRow m n ≤
      (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) := by
  let e : MediumAtom := { d with beta := fun _ ↦ 1 }
  have he : MediumAdmissible 0 sigma kappa c0 e := by
    obtain ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, _hBeta, hGamma1, hGamma2, hGamma3⟩ := hd
    refine ⟨hU, hV, hQ1, hQ2, hQ3, hx, ha0, ha1, hg1, hg2, hg3, hg4,
      hAlpha, hRough, ?_, hGamma1, hGamma2, hGamma3⟩
    intro k _
    change ‖(1 : ℂ)‖ ≤ (k.divisors.card : ℝ) ^ 0
    norm_num
  have hgood : e.cleanedBeta n ≠ 0 := by
    change (if (n : ℤ) ∣ d.residue then (0 : ℂ) else 1) ≠ 0
    simpa only [if_neg hn] using (one_ne_zero : (1 : ℂ) ≠ 0)
  exact e.absoluteFactorModulusRow_le_tauFour he m n hgood

/- These three private polynomial-difference and subpower proofs are
literal extractions from the already owned TransposedLargeGCDFourier. -/
private theorem one_le_scale
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ d.scale := by
  unfold MediumAtom.scale
  calc
    1 = (1 : ℝ) * 1 := by norm_num
    _ ≤ d.U * d.V := mul_le_mul hd.1 hd.2.1 zero_le_one (by linarith [hd.1])

private theorem actual_difference_le_polynomial
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m n : ℕ}
    (hn : n ∈ d.transposedAtom.betaCarrier)
    (hm : d.transposedAtom.commonSmoothWeight m ≠ 0) :
    (((m : ℤ) * n - d.residue).natAbs : ℝ) ≤
      7 * d.scale ^ (max 1 (1 + kappa)) := by
  have hx := one_le_scale hd
  obtain ⟨hU, hV, _, _, _, _, _, ha, _⟩ := hd
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx (le_max_left (1 : ℝ) (1 + kappa))
  have haK : |(d.residue : ℝ)| ≤ d.scale ^ (max 1 (1 + kappa)) := by
    have ha' : |(d.residue : ℝ)| ≤ d.scale ^ (1 + kappa) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using ha
    exact ha'.trans (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hms : (m : ℝ) ∈ tsupport (CommonSmoothCutoff.scaledDyadicCutoff d.V) :=
    subset_closure hm
  have hmhi := (CommonSmoothCutoff.scaledDyadicCutoff_tsupport_subset
    (lt_of_lt_of_le zero_lt_one hV) hms).2
  have hnhi : (n : ℝ) ≤ 2 * d.U :=
    (show (n : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hn).2).trans
        (Nat.floor_le (by linarith : 0 ≤ 2 * d.U))
  have hmn : (m : ℝ) * n ≤ 6 * d.scale := by
    calc
      _ ≤ (3 * d.V) * (2 * d.U) :=
        mul_le_mul hmhi hnhi (Nat.cast_nonneg _) (by linarith)
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ = |(m : ℝ) * n - d.residue| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      push_cast
      rfl
    _ ≤ |(m : ℝ) * n| + |(d.residue : ℝ)| := abs_sub _ _
    _ ≤ 6 * d.scale + d.scale ^ (max 1 (1 + kappa)) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) * n)]
      exact add_le_add hmn haK
    _ ≤ _ := by linarith

private theorem tauFour_difference_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ m n : ℕ,
        n ∈ d.transposedAtom.betaCarrier → d.transposedAtom.commonSmoothWeight m ≠ 0 →
          ¬(n : ℤ) ∣ d.residue →
            (fouvryTau 4 (((m : ℤ) * n - d.residue).natAbs) : ℝ) ≤
              C * d.scale ^ (epsilon / 2) := by
  let K : ℝ := max 1 (1 + kappa)
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let eta : ℝ := epsilon / (2 * K)
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hKpos)
  have hKeta : K * eta = epsilon / 2 := by dsimp [eta]; field_simp [hKpos.ne']
  obtain ⟨D, hD, hbound⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 4) (by norm_num) heta
  refine ⟨D * (7 : ℝ) ^ eta, by positivity, fun B sigma c0 d hd m n hn hm hndiv ↦ ?_⟩
  have hne : (m : ℤ) * n - d.residue ≠ 0 := by
    intro h
    exact hndiv ⟨m, by nlinarith⟩
  have hx := one_le_scale hd
  calc
    _ ≤ D * (((m : ℤ) * n - d.residue).natAbs : ℝ) ^ eta :=
      hbound _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hne))
    _ ≤ D * (7 * d.scale ^ K) ^ eta :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (actual_difference_le_polynomial hd hn hm) heta.le) hD.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 7) (Real.rpow_nonneg (by linarith) _),
        ← Real.rpow_mul (by linarith : 0 ≤ d.scale), hKeta]
      ring


private theorem p_pos_lower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) : 0 < p ∧ d.Q1 ≤ (p : ℝ) := by
  have hlo := (mem_Icc.mp (mem_filter.mp hp).1).1
  have hlower : d.Q1 ≤ (p : ℝ) := (Nat.le_ceil d.Q1).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < p := (zero_lt_one.trans_le hd.2.2.1).trans_le hlower
  exact ⟨by exact_mod_cast hpos, hlower⟩

private theorem p_coprime_residue
    {d : MediumAtom} {p : ℕ} (hp : p ∈ d.primitiveFirstFactorCarrier) :
    Int.gcd d.residue p = 1 := by
  simpa only [Int.gcd, Int.natAbs_natCast] using (mem_filter.mp hp).2.symm

private theorem slice_gamma (d : MediumAtom) (p : ℕ) (r : ℕ × ℕ × ℕ) :
    (d.q1SliceAtom p).transposedAtom.complexFactorGamma r =
      (if r.1 = p then (1 : ℂ) else 0) * d.gamma2 r.2.1 * d.gamma3 r.2.2 := rfl

/-- This is the actual p-divisibility support, with all complex labels. -/
private theorem absoluteRow_eq_zero_of_not_product (d : MediumAtom) (p m n : ℕ)
    (hnot : ¬Int.ModEq p ((m : ℤ) * n) d.residue) :
    (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n = 0 := by
  unfold MediumAtom.absoluteFactorModulusRow
  rw [show (d.q1SliceAtom p).transposedAtom.residue = d.residue from rfl]
  apply sum_eq_zero
  intro r _
  by_cases hq : r.1 = p
  · by_cases hr : Int.ModEq (complexFactorModulus r) ((m : ℤ) * n) d.residue
    · have hdiv : (p : ℤ) ∣ (complexFactorModulus r : ℤ) := by
        refine ⟨((r.2.1 * r.2.2 : ℕ) : ℤ), ?_⟩
        simp only [complexFactorModulus]
        rw [hq]
        push_cast
        ring
      exact (hnot (hr.of_dvd hdiv)).elim
    · simp only [if_neg hr]
  · simp only [slice_gamma, if_neg hq, zero_mul, norm_zero, ite_self]

/- Exact primitive-product and congruence cancellation from the owned
ComplexCRTConsumer, specialized to the same p. The original numerator
is signed and no size condition is used. -/
private theorem coprime_of_product_congruent {a : ℤ} {p n m : ℕ}
    (ha : Int.gcd a p = 1) (h : Int.ModEq p ((n : ℤ) * m) a) :
    n.Coprime p ∧ m.Coprime p := by
  have hg : Int.gcd ((n : ℤ) * m) p = 1 := by
    rw [← Int.gcd_emod ((n : ℤ) * m) p, h.eq, Int.gcd_emod, ha]
  have hnm : (n * m).Coprime p := by
    simpa [Int.gcd, Int.natAbs_mul] using hg
  exact Nat.coprime_mul_iff_left.mp hnm

private theorem shared_conditions_of_products {a : ℤ} {p m n₁ n₂ : ℕ}
    (hp : 0 < p) (ha : Int.gcd a p = 1)
    (h₁ : Int.ModEq p ((m : ℤ) * n₁) a)
    (h₂ : Int.ModEq p ((m : ℤ) * n₂) a) :
    n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ := by
  refine ⟨(coprime_of_product_congruent ha h₁).2,
    (coprime_of_product_congruent ha h₂).2, ?_⟩
  have hcross : Int.ModEq p (a * n₁) (a * n₂) :=
    (h₂.mul_right (n₁ : ℤ)).symm.trans
      (by simpa [mul_assoc, mul_comm, mul_left_comm] using h₁.mul_right (n₂ : ℤ))
  apply Int.natCast_modEq_iff.mp
  simpa only [Int.gcd_comm (p : ℤ) a, ha, Nat.cast_one, Int.ediv_one]
    using hcross.cancel_left_div_gcd (by exact_mod_cast hp : (0 : ℤ) < p)

/-- The finite progression count is the owned Alpha quotient-block count. -/
private theorem sum_weight_product_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {p n : ℕ}
    (hp : 0 < p) (hn : n.Coprime p) (a : ℤ) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if Int.ModEq p ((m : ℤ) * n) a then
        d.transposedAtom.commonSmoothWeight m else 0) ≤ 4 * d.V / p + 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hceil : (Nat.ceil (3 * d.V) : ℝ) ≤ 4 * d.V := by
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ 3 * d.V)
    linarith
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n) a then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro m _
      split_ifs
      · exact CommonSmoothCutoff.scaledDyadicCutoff_le_one _ _
      · exact le_rfl
    _ = (((Icc 0 (Nat.ceil (3 * d.V))).filter
        (fun m : ℕ ↦ Int.ModEq p ((m : ℤ) * n) a)).card : ℝ) := by
      rw [← sum_filter]
      simp [MediumAtom.commonSmoothCarrier, MediumAtom.transposedAtom]
    _ ≤ ((Nat.ceil (3 * d.V) / p + 1 : ℕ) : ℝ) := by
      exact_mod_cast PairedAlphaDeletion.card_product_modEq_le (Nat.ceil (3 * d.V)) p n a hn
    _ ≤ (Nat.ceil (3 * d.V) : ℝ) / p + 1 := by
      push_cast
      have hh : ((Nat.ceil (3 * d.V) / p : ℕ) : ℝ) ≤
          (Nat.ceil (3 * d.V) : ℝ) / p := Nat.cast_div_le
      exact add_le_add hh le_rfl
    _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hceil hpR.le) le_rfl

private theorem sum_weight_two_products_le
    {d : MediumAtom} (hV : 1 ≤ d.V) {p : ℕ} (hp : 0 < p)
    (ha : Int.gcd d.residue p = 1) (n₁ n₂ : ℕ) :
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
          Int.ModEq p ((m : ℤ) * n₂) d.residue then
        d.transposedAtom.commonSmoothWeight m else 0) ≤
      if n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ then
        4 * d.V / p + 1 else 0 := by
  by_cases hc : n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂
  · rw [if_pos hc]
    apply le_trans _ (sum_weight_product_le hV hp hc.1 d.residue)
    apply sum_le_sum
    intro m _
    by_cases h₁ : Int.ModEq p ((m : ℤ) * n₁) d.residue
    · by_cases h₂ : Int.ModEq p ((m : ℤ) * n₂) d.residue
      · simp only [h₁, h₂, and_self, if_true, le_refl]
      · simpa only [h₁, h₂, and_false, if_false, if_true] using
          d.transposedAtom.commonSmoothWeight_nonneg m
    · simp only [h₁, false_and, if_false, le_refl]
  · rw [if_neg hc]
    have hz : (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
            Int.ModEq p ((m : ℤ) * n₂) d.residue then
          d.transposedAtom.commonSmoothWeight m else 0) = 0 := by
      apply sum_eq_zero
      intro m _
      apply if_neg
      exact fun hm ↦ hc (shared_conditions_of_products hp ha hm.1 hm.2)
    exact hz.le

/-- Whole factor-pair norm, with the p-progressions still inside its cost. -/
private theorem slice_factorPair_norm_subpower (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ p : ℕ,
        p ∈ d.primitiveFirstFactorCarrier → ∀ n₁ n₂ : ℕ,
          n₁ ∈ d.transposedAtom.betaCarrier → n₂ ∈ d.transposedAtom.betaCarrier →
            ¬(n₁ : ℤ) ∣ d.residue → ¬(n₂ : ℤ) ∣ d.residue →
              ‖(d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n₁ n₂‖ ≤
                C * d.scale ^ epsilon *
                  (if n₁.Coprime p ∧ n₂.Coprime p ∧ Nat.ModEq p n₁ n₂ then
                    4 * d.V / p + 1 else 0) := by
  obtain ⟨C, hC, hbound⟩ := tauFour_difference_subpower kappa hepsilon
  refine ⟨C ^ 2, by positivity, fun B sigma c0 d hd p hp n₁ n₂ hn₁ hn₂ hnd₁ hnd₂ ↦ ?_⟩
  have hs := mediumAdmissible_q1SliceAtom hd hp
  have hx := one_le_scale hd
  have hp0 := (p_pos_lower hd hp).1
  have hsum := ((d.q1SliceAtom p).transposedAtom.commonFactorPairWeight_norm_le n₁ n₂)
  have hcar : (d.q1SliceAtom p).transposedAtom.commonSmoothCarrier =
      d.transposedAtom.commonSmoothCarrier := rfl
  have hweight (m : ℕ) : (d.q1SliceAtom p).transposedAtom.commonSmoothWeight m =
      d.transposedAtom.commonSmoothWeight m := rfl
  rw [hcar] at hsum
  simp only [hweight] at hsum
  apply hsum.trans
  calc
    _ ≤ ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
            Int.ModEq p ((m : ℤ) * n₂) d.residue then
          d.transposedAtom.commonSmoothWeight m * (C ^ 2 * d.scale ^ epsilon) else 0 := by
      apply sum_le_sum
      intro m _
      by_cases hm : d.transposedAtom.commonSmoothWeight m = 0
      · simp only [hm, zero_mul, ite_self, le_refl]
      by_cases h₁ : Int.ModEq p ((m : ℤ) * n₁) d.residue
      · by_cases h₂ : Int.ModEq p ((m : ℤ) * n₂) d.residue
        · rw [if_pos ⟨h₁, h₂⟩]
          have ha₁ : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ ≤
              C * d.scale ^ (epsilon / 2) :=
            (absoluteRow_le_tauFour_of_not_dvd hs m n₁ hnd₁).trans
              (hbound B sigma c0 d hd m n₁ hn₁ hm hnd₁)
          have ha₂ : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂ ≤
              C * d.scale ^ (epsilon / 2) :=
            (absoluteRow_le_tauFour_of_not_dvd hs m n₂ hnd₂).trans
              (hbound B sigma c0 d hd m n₂ hn₂ hm hnd₂)
          have hh : (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ *
              (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂ ≤
                C ^ 2 * d.scale ^ epsilon := by
            calc
              _ ≤ (C * d.scale ^ (epsilon / 2)) * (C * d.scale ^ (epsilon / 2)) :=
                mul_le_mul ha₁ ha₂
                  ((d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow_nonneg m n₂)
                  (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hx) _))
              _ = _ := by
                rw [mul_mul_mul_comm, ← Real.rpow_add (zero_lt_one.trans_le hx),
                  show epsilon / 2 + epsilon / 2 = epsilon by ring, pow_two]
          exact (show _ = d.transposedAtom.commonSmoothWeight m *
            ((d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₁ *
              (d.q1SliceAtom p).transposedAtom.absoluteFactorModulusRow m n₂) by ring).trans_le
                (mul_le_mul_of_nonneg_left hh (d.transposedAtom.commonSmoothWeight_nonneg m))
        · rw [absoluteRow_eq_zero_of_not_product d p m n₂ h₂, mul_zero]
          simp only [h₂, and_false, if_false, le_refl]
      · rw [absoluteRow_eq_zero_of_not_product d p m n₁ h₁, mul_zero, zero_mul]
        simp only [h₁, false_and, if_false, le_refl]
    _ = (C ^ 2 * d.scale ^ epsilon) *
        ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
          if Int.ModEq p ((m : ℤ) * n₁) d.residue ∧
              Int.ModEq p ((m : ℤ) * n₂) d.residue then
            d.transposedAtom.commonSmoothWeight m else 0 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_weight_two_products_le hd.2.1 hp0 (p_coprime_residue hp) n₁ n₂)
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (zero_le_one.trans hx) _))

private theorem cleaned_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.cleanedAlphaAtom.transposedAtom.beta n‖ ≤ 1 := by
  have hclean := mediumAdmissible_cleanedAlphaAtom hd
  have hAlpha : ∀ n ∈ d.cleanedAlphaAtom.alphaCarrier, ‖d.cleanedAlphaAtom.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hclean
    exact hAlpha
  change ‖if n ∈ d.cleanedAlphaAtom.alphaCarrier then d.cleanedAlphaAtom.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.cleanedAlphaAtom.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private theorem card_primitiveCarrier_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2 * d.Q1 := by
  have hsub : d.primitiveFirstFactorCarrier ⊆ Ioc 0 (Nat.floor (2 * d.Q1)) := by
    intro p hp
    have hlo := (mem_Icc.mp (mem_filter.mp hp).1).2
    exact mem_Ioc.mpr ⟨(p_pos_lower hd hp).1, hlo⟩
  have hc := card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hc
  exact (show (d.primitiveFirstFactorCarrier.card : ℝ) ≤ (Nat.floor (2 * d.Q1) : ℝ) by
    exact_mod_cast hc).trans (Nat.floor_le (by linarith [hd.2.2.1]))



private def tailLabels (d : MediumAtom) : Finset (ℕ × ℕ) :=
  factorCarrier d.Q2 ×ˢ factorCarrier d.Q3

private def tailProducts (d : MediumAtom) : Finset ℕ :=
  (tailLabels d).image (fun u ↦ u.1 * u.2)

private def tailGamma (d : MediumAtom) (v : ℕ) : ℂ :=
  ∑ u ∈ (tailLabels d).filter (fun u ↦ u.1 * u.2 = v), d.gamma2 u.1 * d.gamma3 u.2

private def tailCap (d : MediumAtom) : ℝ := 4 * d.Q2 * d.Q3

private def tau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem factor_bounds {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
    (hn : n ∈ factorCarrier Q) : 0 < n ∧ Q ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlower : Q ≤ (n : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  have hpos : (0 : ℝ) < n := (zero_lt_one.trans_le hQ).trans_le hlower
  refine ⟨by exact_mod_cast hpos, hlower, ?_⟩
  exact (show (n : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
    (Nat.floor_le (by linarith : 0 ≤ 2 * Q))

private theorem one_le_tailCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 ≤ tailCap d := by
  have h2 := hd.2.2.2.1
  have h3 := hd.2.2.2.2.1
  unfold tailCap
  nlinarith [mul_le_mul h2 h3 zero_le_one (by linarith : 0 ≤ d.Q2)]

private theorem tail_product_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {u : ℕ × ℕ}
    (hu : u ∈ tailLabels d) : 0 < u.1 * u.2 ∧ (u.1 * u.2 : ℕ) ≤ Nat.floor (tailCap d) := by
  obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
  have hb2 := factor_bounds hd.2.2.2.1 h2
  have hb3 := factor_bounds hd.2.2.2.2.1 h3
  refine ⟨Nat.mul_pos hb2.1 hb3.1, Nat.le_floor ?_⟩
  push_cast
  calc
    (u.1 : ℝ) * u.2 ≤ (2 * d.Q2) * (2 * d.Q3) :=
      mul_le_mul hb2.2.2 hb3.2.2 (Nat.cast_nonneg _) (by linarith [hd.2.2.2.1])
    _ = tailCap d := by unfold tailCap; ring

private theorem tailProducts_subset_prefix
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    tailProducts d ⊆ Finset.Ioc 0 (Nat.floor (tailCap d)) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_Ioc.mpr (tail_product_bounds hd hu)

private theorem tailGamma_zero_off_products (d : MediumAtom) {v : ℕ}
    (hv : v ∉ tailProducts d) : tailGamma d v = 0 := by
  unfold tailGamma
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
  exact (hv (Finset.mem_image.mpr ⟨u, hu, he⟩)).elim

private theorem tailGamma_norm_le_tau
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (v : ℕ) :
    ‖tailGamma d v‖ ≤ tau v := by
  let S := (tailLabels d).filter (fun u ↦ u.1 * u.2 = v)
  have hsub : S ⊆ v.divisorsAntidiagonal := by
    intro u hu
    obtain ⟨hu, he⟩ := Finset.mem_filter.mp hu
    exact Nat.mem_divisorsAntidiagonal.mpr
      ⟨he, by rw [← he]; exact (tail_product_bounds hd hu).1.ne'⟩
  have hcard : v.divisorsAntidiagonal.card = v.divisors.card := by
    rw [← Nat.map_div_right_divisors]
    exact Finset.card_map _
  have hg : ∀ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨hu, _⟩ := Finset.mem_filter.mp hu
    obtain ⟨h2, h3⟩ := Finset.mem_product.mp hu
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hg2, hg3⟩ := hd
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul (hg2 _ h2).1 (hg3 _ h3).1
      (norm_nonneg _) zero_le_one
  calc
    ‖tailGamma d v‖ ≤ ∑ u ∈ S, ‖d.gamma2 u.1 * d.gamma3 u.2‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ S, (1 : ℝ) := Finset.sum_le_sum hg
    _ = (S.card : ℝ) := by simp
    _ ≤ tau v := by
      unfold tau
      exact_mod_cast (Finset.card_le_card hsub).trans_eq hcard

/-- Group every original complex tail label before taking its norm. -/
private theorem tail_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, tailGamma d v * F v := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := tailLabels d) (t := tailProducts d) (g := fun u ↦ u.1 * u.2)
    (fun u hu ↦ Finset.mem_image_of_mem _ hu)
    (fun u ↦ (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro v _
  rw [tailGamma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u hu
  rw [(Finset.mem_filter.mp hu).2]

private theorem tail_star_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℂ) :
    (∑ u ∈ tailLabels d, star (d.gamma2 u.1 * d.gamma3 u.2) * F (u.1 * u.2)) =
      ∑ v ∈ tailProducts d, star (tailGamma d v) * F v := by
  calc
    _ = star (∑ u ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (F (u.1 * u.2))) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ v ∈ tailProducts d, tailGamma d v * star (F v)) :=
      congrArg star (tail_sum_eq_grouped d (fun v ↦ star (F v)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem tail_pair_sum_eq_grouped (d : MediumAtom) (F : ℕ → ℕ → ℂ) :
    (∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
      (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
        F (u.1 * u.2) (v.1 * v.2)) =
      ∑ a ∈ tailProducts d, ∑ b ∈ tailProducts d,
        tailGamma d a * star (tailGamma d b) * F a b := by
  calc
    _ = ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F (u.1 * u.2) (v.1 * v.2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ a ∈ tailProducts d, tailGamma d a *
        ∑ v ∈ tailLabels d,
          star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2) :=
      tail_sum_eq_grouped d (fun a ↦ ∑ v ∈ tailLabels d,
        star (d.gamma2 v.1 * d.gamma3 v.2) * F a (v.1 * v.2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [tail_star_sum_eq_grouped d (F a), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

private theorem slice_factor_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * F a) =
      ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) * F (p, u.1, u.2) := by
  simp only [MediumAtom.complexFactorLabels, MediumAtom.complexFactorGamma,
    MediumAtom.q1SliceAtom, MediumAtom.transposedAtom, Finset.sum_product]
  change (∑ q ∈ factorCarrier d.Q1, ∑ a ∈ factorCarrier d.Q2,
    ∑ b ∈ factorCarrier d.Q3,
      ((if q = p then (1 : ℂ) else 0) * d.gamma2 a * d.gamma3 b) * F (q, a, b)) = _
  rw [Finset.sum_eq_single p]
  · simp only [ite_true, one_mul, tailLabels, Finset.sum_product]
  · intro q _ hqp
    simp only [if_neg hqp, zero_mul, Finset.sum_const_zero]
  · exact fun h ↦ (h hp).elim

private theorem slice_factor_star_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma a) * F a) =
      ∑ u ∈ tailLabels d, star (d.gamma2 u.1 * d.gamma3 u.2) * F (p, u.1, u.2) := by
  calc
    _ = star (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a * star (F a)) := by
      simp only [star_sum, star_mul', star_star]
    _ = star (∑ u ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (F (p, u.1, u.2))) :=
      congrArg star (slice_factor_sum d hp (fun a ↦ star (F a)))
    _ = _ := by simp only [star_sum, star_mul', star_star]

private theorem slice_factor_pair_sum (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (F : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ) → ℂ) :
    (∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
      ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * F a b) =
      ∑ u ∈ tailLabels d, ∑ v ∈ tailLabels d,
        (d.gamma2 u.1 * d.gamma3 u.2) * star (d.gamma2 v.1 * d.gamma3 v.2) *
          F (p, u.1, u.2) (p, v.1, v.2) := by
  calc
    _ = ∑ a ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
        (d.q1SliceAtom p).transposedAtom.complexFactorGamma a *
          ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
            star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) * F a b := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ u ∈ tailLabels d, (d.gamma2 u.1 * d.gamma3 u.2) *
        ∑ b ∈ (d.q1SliceAtom p).transposedAtom.complexFactorLabels,
          star ((d.q1SliceAtom p).transposedAtom.complexFactorGamma b) *
            F (p, u.1, u.2) b := slice_factor_sum d hp _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [slice_factor_star_sum d hp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring

private theorem slice_zero_eq_grouped (d : MediumAtom) {p : ℕ}
    (hp : p ∈ factorCarrier d.Q1) (n1 n2 : ℕ) :
    (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 =
      ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
        tailGamma d v * star (tailGamma d w) *
          ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
            d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
          else 0 : ℝ) : ℂ) := by
  unfold MediumAtom.commonFactorPairZeroWeight
  rw [slice_factor_pair_sum d hp]
  have hU : (d.q1SliceAtom p).transposedAtom.U = d.V := rfl
  simpa only [complexFactorModulus, Nat.mul_assoc, sharedFirstFactor_lcm, hU] using
    tail_pair_sum_eq_grouped d (fun v w ↦
      ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
        d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
      else 0 : ℝ) : ℂ))

private theorem tail_lcm_moment
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    (∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
      ‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ)) ≤
        (1 + Real.log (tailCap d)) ^ 9 := by
  have hh := MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds.sum_abs_lcm_weight_le_log
    2 (one_le_tailCap hd) (tailProducts d) (tailProducts_subset_prefix hd)
    (fun v ↦ ‖tailGamma d v‖)
    (fun v _ ↦ by
      simpa only [abs_norm, fouvryTau_two, tau] using tailGamma_norm_le_tau hd v)
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    exact (abs_of_nonneg (by positivity)).symm
  · norm_num

private def pairGate (p n1 n2 : ℕ) : Prop :=
  n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2

private theorem compatible_implies_pairGate (p v w n1 n2 : ℕ)
    (h : ComplexCRT.Compatible (p * v) (p * w) n1 n2) : pairGate p n1 n2 := by
  rw [sharedFirstFactor_compatible_iff] at h
  exact ⟨h.1.of_dvd_right (dvd_mul_right p v),
    h.2.1.of_dvd_right (dvd_mul_right p w), h.2.2.of_dvd (dvd_mul_right p (v.gcd w))⟩

private theorem slice_zero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (n1 n2 : ℕ) :
    ‖(d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2‖ ≤
      if pairGate p n1 n2 then
        |CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ) *
          (1 + Real.log (tailCap d)) ^ 9 else 0 := by
  have hp0 := (factor_bounds hd.2.2.1 (Finset.mem_filter.mp hp).1).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hV : 0 ≤ d.V := by linarith [hd.2.1]
  rw [slice_zero_eq_grouped d (Finset.mem_filter.mp hp).1]
  by_cases hg : pairGate p n1 n2
  · rw [if_pos hg]
    calc
      _ ≤ ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
          (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ)) *
            (‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro v _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro w _
        by_cases hc : ComplexCRT.Compatible (p * v) (p * w) n1 n2
        · have hlcm : (0 : ℝ) ≤ (v.lcm w : ℝ) := Nat.cast_nonneg _
          simp only [if_pos hc, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_div, abs_of_nonneg hV, Nat.cast_mul,
            abs_of_nonneg hpR.le, abs_of_nonneg hlcm]
          exact le_of_eq (by ring)
        · simp only [if_neg hc, Complex.ofReal_zero, mul_zero, norm_zero]
          positivity
      _ = (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ)) *
          ∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
            ‖tailGamma d v‖ * ‖tailGamma d w‖ / (v.lcm w : ℝ) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_lcm_moment hd) (by positivity)
  · rw [if_neg hg]
    have hz : (∑ v ∈ tailProducts d, ∑ w ∈ tailProducts d,
        tailGamma d v * star (tailGamma d w) *
          ((if ComplexCRT.Compatible (p * v) (p * w) n1 n2 then
            d.V / ((p * v.lcm w : ℕ) : ℝ) * CommonSmoothCutoff.cutoffMass
          else 0 : ℝ) : ℂ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v _
      apply Finset.sum_eq_zero
      intro w _
      have hc : ¬ComplexCRT.Compatible (p * v) (p * w) n1 n2 :=
        fun h ↦ hg (compatible_implies_pairGate p v w n1 n2 h)
      simp only [if_neg hc, Complex.ofReal_zero, mul_zero]
    rw [hz, norm_zero]

private theorem transposed_beta_norm_le_one
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (n : ℕ) :
    ‖d.transposedAtom.beta n‖ ≤ 1 := by
  have hAlpha : ∀ n ∈ d.alphaCarrier, ‖d.alpha n‖ ≤ 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _⟩ := hd
    exact hAlpha
  change ‖if n ∈ d.alphaCarrier then d.alpha n else 0‖ ≤ 1
  by_cases hn : n ∈ d.alphaCarrier
  · simpa only [if_pos hn] using hAlpha n hn
  · simp only [if_neg hn, norm_zero, zero_le_one]

private def supportedPairs (N : Finset ℕ) (p : ℕ) (Ybeta Ysupport : ℝ) :
    Finset (ℕ × ℕ) :=
  (N ×ˢ N).filter (fun z ↦ z.1.Coprime p ∧ z.2.Coprime p ∧
    Nat.ModEq p z.1 z.2 ∧ smallPairedLargeSupportedMask Ybeta Ysupport z.1 z.2)

private theorem alphaCarrier_subset_prefix {d : MediumAtom} (hU : 1 ≤ d.U) :
    d.transposedAtom.betaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2 * d.U)) := by
  intro n hn
  change n ∈ factorCarrier d.U at hn
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
  have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hU.trans (Nat.le_ceil d.U)
  exact Finset.mem_Ioc.mpr ⟨by omega, hnhi⟩

private theorem card_supportedPairs_actual
    {d : MediumAtom} (hU : 1 ≤ d.U) {Ysupport : ℝ} (hY : 0 < Ysupport)
    {p : ℕ} (hp : 0 < p) (Ybeta : ℝ) :
    ((supportedPairs d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) ≤
      (4 * d.U / Real.sqrt Ysupport) * (2 * d.U / (p : ℝ) + 1) := by
  have hh := card_sharedPrimitiveLargeSupportedPairs_le
    (T := 2 * d.U) (by linarith) hY hp d.transposedAtom.betaCarrier
    (alphaCarrier_subset_prefix (d := d) hU) Ybeta
  simpa only [supportedPairs, show 2 * (2 * d.U) = 4 * d.U by ring] using hh

/-- Only nonnegative termwise envelopes are enlarged. The mask is still the
literal original paired-integer mask when the triangle inequality is taken. -/
private theorem masked_pair_norm_le
    (N : Finset ℕ) (beta : ℕ → ℂ) (K : ℕ → ℕ → ℂ)
    (p : ℕ) (Ybeta Ysupport M : ℝ) (hM : 0 ≤ M)
    (hbeta : ∀ n ∈ N, ‖beta n‖ ≤ 1)
    (hK : ∀ n1 ∈ N, ∀ n2 ∈ N, beta n1 ≠ 0 → beta n2 ≠ 0 →
      ‖K n1 n2‖ ≤ if pairGate p n1 n2 then M else 0) :
    ‖∑ n1 ∈ N, ∑ n2 ∈ N,
      if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
        beta n1 * star (beta n2) * K n1 n2 else 0‖ ≤
      M * ((supportedPairs N p Ybeta Ysupport).card : ℝ) := by
  calc
    _ ≤ ∑ n1 ∈ N, ∑ n2 ∈ N,
        if n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
            smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then M else 0 := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n1 hn1
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n2 hn2
      by_cases hy : smallPairedLargeSupportedMask Ybeta Ysupport n1 n2
      · rw [if_pos hy]
        by_cases h1 : beta n1 = 0
        · simp only [h1, zero_mul, norm_zero]
          split_ifs <;> first | exact hM | exact le_rfl
        by_cases h2 : beta n2 = 0
        · simp only [h2, star_zero, mul_zero, zero_mul, norm_zero]
          split_ifs <;> first | exact hM | exact le_rfl
        have hb := hK n1 hn1 n2 hn2 h1 h2
        by_cases hc : pairGate p n1 n2
        · have hfull : n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
              smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 :=
            ⟨hc.1, hc.2.1, hc.2.2, hy⟩
          rw [if_pos hc] at hb
          rw [if_pos hfull]
          simp only [norm_mul, norm_star]
          have hcoef : ‖beta n1‖ * ‖beta n2‖ ≤ 1 := by
            simpa only [one_mul] using mul_le_mul (hbeta n1 hn1) (hbeta n2 hn2)
              (norm_nonneg _) zero_le_one
          exact (mul_le_mul hcoef hb (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
        · have hnot : ¬(n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
              smallPairedLargeSupportedMask Ybeta Ysupport n1 n2) :=
            fun h ↦ hc ⟨h.1, h.2.1, h.2.2.1⟩
          rw [if_neg hc] at hb
          have hz := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
          simp only [hz, mul_zero, norm_zero, if_neg hnot, le_refl]
      · have hnot : ¬(n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2 ∧
            smallPairedLargeSupportedMask Ybeta Ysupport n1 n2) := fun h ↦ hy h.2.2.2
        simp only [if_neg hy, if_neg hnot, norm_zero, le_refl]
    _ = _ := by
      rw [← Finset.sum_product', ← Finset.sum_filter]
      simp only [supportedPairs, Finset.sum_const, nsmul_eq_mul]
      ring

private theorem slice_supported_zero_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {p : ℕ}
    (hp : p ∈ d.primitiveFirstFactorCarrier) (Ybeta Ysupport : ℝ) :
    ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
      if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
        d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2) *
          (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 else 0‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / (p : ℝ) *
        (1 + Real.log (tailCap d)) ^ 9) *
          ((supportedPairs d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) := by
  apply masked_pair_norm_le
  · have hH : 0 ≤ 1 + Real.log (tailCap d) := by
      linarith [Real.log_nonneg (one_le_tailCap hd)]
    have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
    positivity
  · intro n _
    exact transposed_beta_norm_le_one hd n
  · intro n1 _ n2 _ _ _
    exact slice_zero_norm_le hd hp n1 n2

end SharedFirstFactorLargeSupportedDeletion

/-- The raw zero retains the true V/p denominator before the complete p sum. -/
theorem sharedSmallPairedLargeSupportedZero_bound
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Ybeta : ℝ) {Ysupport : ℝ}
    (hY : 0 < Ysupport) :
    ‖d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ ≤
      16 * |CommonSmoothCutoff.cutoffMass| * d.V *
        (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 9 *
          (d.U ^ 2 / d.Q1 + d.U) / Real.sqrt Ysupport := by
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hS : 0 < Real.sqrt Ysupport := Real.sqrt_pos.mpr hY
  have hU : 0 ≤ d.U := zero_le_one.trans hd.1
  have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hH : 0 ≤ 1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d) := by
    linarith [Real.log_nonneg (SharedFirstFactorLargeSupportedDeletion.one_le_tailCap hd)]
  have hrect (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
        if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
          d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2) *
            (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 else 0‖ ≤
      (|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
        (1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d)) ^ 9) *
          ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1)) := by
    obtain ⟨hp0, hpQ⟩ := SharedFirstFactorLargeSupportedDeletion.p_pos_lower hd hp
    have hcount := SharedFirstFactorLargeSupportedDeletion.card_supportedPairs_actual
      (d := d) hd.1 hY hp0 Ybeta
    have hcount' :
        ((SharedFirstFactorLargeSupportedDeletion.supportedPairs
          d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) ≤
        (4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1) := hcount.trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_left (by positivity) hQ hpQ) le_rfl) (by positivity))
    exact (SharedFirstFactorLargeSupportedDeletion.slice_supported_zero_norm_le
      hd hp Ybeta Ysupport).trans (mul_le_mul
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) hQ hpQ) (pow_nonneg hH _))
        hcount' (Nat.cast_nonneg _) (by positivity))
  unfold MediumAtom.sharedSmallPairedLargeSupportedZero
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
          if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
            d.transposedAtom.beta n1 * star (d.transposedAtom.beta n2) *
              (d.q1SliceAtom p).transposedAtom.commonFactorPairZeroWeight n1 n2 else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
        (|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d)) ^ 9) *
            ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1)) :=
      Finset.sum_le_sum hrect
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
        ((|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d)) ^ 9) *
            ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) *
        ((|CommonSmoothCutoff.cutoffMass| * d.V / d.Q1 *
          (1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d)) ^ 9) *
            ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1))) :=
      mul_le_mul_of_nonneg_right
        (SharedFirstFactorLargeSupportedDeletion.card_primitiveCarrier_le hd) (by positivity)
    _ = |CommonSmoothCutoff.cutoffMass| * d.V *
        (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 9 *
          (16 * d.U ^ 2 / d.Q1 + 8 * d.U) / Real.sqrt Ysupport := by
      unfold SharedFirstFactorLargeSupportedDeletion.tailCap
      field_simp [hQ.ne', hS.ne']
      ring
    _ ≤ _ := by
      have hb : 16 * d.U ^ 2 / d.Q1 + 8 * d.U ≤
          16 * (d.U ^ 2 / d.Q1 + d.U) := by
        calc
          _ ≤ 16 * d.U ^ 2 / d.Q1 + 16 * d.U :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_right
              (by norm_num : (8 : ℝ) ≤ 16) hU)
          _ = _ := by ring
      have hcoef : 0 ≤ |CommonSmoothCutoff.cutoffMass| * d.V *
          (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 9 / Real.sqrt Ysupport := by
        change 0 ≤ |CommonSmoothCutoff.cutoffMass| * d.V *
          (1 + Real.log (SharedFirstFactorLargeSupportedDeletion.tailCap d)) ^ 9 /
            Real.sqrt Ysupport
        positivity
      have hh := mul_le_mul_of_nonneg_left hb hcoef
      calc
        _ = (|CommonSmoothCutoff.cutoffMass| * d.V *
            (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 9 / Real.sqrt Ysupport) *
              (16 * d.U ^ 2 / d.Q1 + 8 * d.U) := by ring
        _ ≤ (|CommonSmoothCutoff.cutoffMass| * d.V *
            (1 + Real.log (4 * d.Q2 * d.Q3)) ^ 9 / Real.sqrt Ysupport) *
              (16 * (d.U ^ 2 / d.Q1 + d.U)) := hh
        _ = _ := by ring

/-- Whole W uses a local pointwise extraction before the new masked pair count. -/
theorem cleanedAlpha_sharedSmallPairedLargeSupportedW_bound (kappa : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d → ∀ Ybeta Ysupport : ℝ,
        0 < Ysupport →
          ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ ≤
            C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
              (d.U ^ 2 + d.Q1 * d.U) / Real.sqrt Ysupport := by
  obtain ⟨C, hC, hfactor⟩ :=
    SharedFirstFactorLargeSupportedDeletion.slice_factorPair_norm_subpower kappa hepsilon
  refine ⟨16 * C, by positivity, fun B sigma c0 d hd Ybeta Ysupport hY ↦ ?_⟩
  have hx := TransposedPrimitiveUPayment.one_le_scale hd
  have hX : 0 ≤ C * d.scale ^ epsilon := by positivity
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hS : 0 < Real.sqrt Ysupport := Real.sqrt_pos.mpr hY
  have hU : 0 ≤ d.U := zero_le_one.trans hd.1
  have hV : 0 ≤ d.V := zero_le_one.trans hd.2.1
  have hslice (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
        if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
          d.cleanedAlphaAtom.transposedAtom.beta n1 *
            star (d.cleanedAlphaAtom.transposedAtom.beta n2) *
              (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n1 n2 else 0‖ ≤
      C * d.scale ^ epsilon * (4 * d.V / (p : ℝ) + 1) *
        ((SharedFirstFactorLargeSupportedDeletion.supportedPairs
          d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) := by
    have hp0 := (SharedFirstFactorLargeSupportedDeletion.p_pos_lower hd hp).1
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    apply SharedFirstFactorLargeSupportedDeletion.masked_pair_norm_le
    · positivity
    · intro n _
      exact SharedFirstFactorLargeSupportedDeletion.cleaned_beta_norm_le_one hd n
    · intro n1 hn1 n2 hn2 h1 h2
      have hh := hfactor B sigma c0 d hd p hp n1 n2 hn1 hn2
        (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h1)
        (d.cleanedAlpha_transposedBeta_ne_zero_not_dvd h2)
      by_cases hc : n1.Coprime p ∧ n2.Coprime p ∧ Nat.ModEq p n1 n2
      · have hg : SharedFirstFactorLargeSupportedDeletion.pairGate p n1 n2 := hc
        simpa only [if_pos hc, if_pos hg] using hh
      · have hg : ¬SharedFirstFactorLargeSupportedDeletion.pairGate p n1 n2 := hc
        simpa only [if_neg hc, if_neg hg, mul_zero] using hh
  have hrect (p : ℕ) (hp : p ∈ d.primitiveFirstFactorCarrier) :
      C * d.scale ^ epsilon * (4 * d.V / (p : ℝ) + 1) *
        ((SharedFirstFactorLargeSupportedDeletion.supportedPairs
          d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) ≤
      C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
        ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1)) := by
    obtain ⟨hp0, hpQ⟩ := SharedFirstFactorLargeSupportedDeletion.p_pos_lower hd hp
    have hc := SharedFirstFactorLargeSupportedDeletion.card_supportedPairs_actual
      (d := d) hd.1 hY hp0 Ybeta
    have hc' : ((SharedFirstFactorLargeSupportedDeletion.supportedPairs
          d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) ≤
        (4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1) := hc.trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (div_le_div_of_nonneg_left (by positivity) hQ hpQ) le_rfl) (by positivity))
    have hA : 4 * d.V / (p : ℝ) + 1 ≤ 4 * d.V / d.Q1 + 1 :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hQ hpQ) le_rfl
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hA hX) hc' (Nat.cast_nonneg _) (by positivity)
  have hexpand : d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport =
      ∑ p ∈ d.primitiveFirstFactorCarrier,
        (∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
          if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
            d.cleanedAlphaAtom.transposedAtom.beta n1 *
              star (d.cleanedAlphaAtom.transposedAtom.beta n2) *
                (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n1 n2 else 0) := rfl
  rw [hexpand]
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖∑ n1 ∈ d.transposedAtom.betaCarrier, ∑ n2 ∈ d.transposedAtom.betaCarrier,
          if smallPairedLargeSupportedMask Ybeta Ysupport n1 n2 then
            d.cleanedAlphaAtom.transposedAtom.beta n1 *
              star (d.cleanedAlphaAtom.transposedAtom.beta n2) *
                (d.q1SliceAtom p).transposedAtom.commonFactorPairWeight n1 n2 else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        C * d.scale ^ epsilon * (4 * d.V / (p : ℝ) + 1) *
          ((SharedFirstFactorLargeSupportedDeletion.supportedPairs
            d.transposedAtom.betaCarrier p Ybeta Ysupport).card : ℝ) :=
      Finset.sum_le_sum hslice
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier,
        C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1)) :=
      Finset.sum_le_sum hrect
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) *
        (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d.Q1) *
        (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
          ((4 * d.U / Real.sqrt Ysupport) * (2 * d.U / d.Q1 + 1))) :=
      mul_le_mul_of_nonneg_right
        (SharedFirstFactorLargeSupportedDeletion.card_primitiveCarrier_le hd) (by positivity)
    _ = C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
        (16 * d.U ^ 2 + 8 * d.Q1 * d.U) / Real.sqrt Ysupport := by
      field_simp [hQ.ne', hS.ne']
      ring
    _ ≤ _ := by
      have hb : 16 * d.U ^ 2 + 8 * d.Q1 * d.U ≤
          16 * (d.U ^ 2 + d.Q1 * d.U) := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hb
        (show 0 ≤ C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) /
          Real.sqrt Ysupport by positivity)
      calc
        _ = (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) /
            Real.sqrt Ysupport) * (16 * d.U ^ 2 + 8 * d.Q1 * d.U) := by ring
        _ ≤ (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) /
            Real.sqrt Ysupport) * (16 * (d.U ^ 2 + d.Q1 * d.U)) := hh
        _ = _ := by ring

/-- All three signed objects use the identical oriented mask and coefficients. -/
theorem sharedSmallPairedLargeSupportedW_eq_zero_add_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Ybeta Ysupport : ℝ) :
    d.sharedSmallPairedLargeSupportedW Ybeta Ysupport =
      d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport +
        d.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport := by
  unfold MediumAtom.sharedSmallPairedLargeSupportedW
    MediumAtom.sharedSmallPairedLargeSupportedZero
    MediumAtom.sharedSmallPairedLargeSupportedNonzero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n2 _
  by_cases hy : smallPairedLargeSupportedMask Ybeta Ysupport n1 n2
  · simp only [if_pos hy, transposed_factorPair_eq_zero_add_nonzero
      (mediumAdmissible_q1SliceAtom hd hp), mul_add]
  · simp only [if_neg hy, add_zero]



namespace SharedFirstFactorLargeSupportedDeletion

private def outside (d : MediumAtom) : ℝ :=
  (∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, ‖d.gamma1 p‖ ^ 2)

private def betaLog (d : MediumAtom) : ℝ := 1 + Real.log (2 * d.V)
private def capLog (d : MediumAtom) : ℝ := 1 + Real.log d.physicalFactorCap

private theorem outside_nonneg (d : MediumAtom) : 0 ≤ outside d := by
  unfold outside
  positivity

private theorem log_and_scale_bounds
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hsigma : 0 < sigma) (hd : MediumAdmissible B sigma kappa c0 d) :
    d.U ≤ d.V ∧ d.Q1 ≤ d.U ∧ 1 ≤ betaLog d ∧ 1 ≤ capLog d ∧
      1 + Real.log (2 * d.U) ≤ betaLog d ∧
        1 + Real.log (tailCap d) ≤ capLog d := by
  have hX := one_le_scale hd
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hsq : d.U ^ 2 ≤ d.scale := by
    apply (TransposedPrimitiveUMoment.U_sq_lt_scale_rpow hd).le.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX
      (show 1 - 8 * sigma ≤ 1 by linarith)
  have hUV : d.U ≤ d.V := by
    change d.U ^ 2 ≤ d.U * d.V at hsq
    nlinarith
  have hQU : d.Q1 ≤ d.U := by
    have hq := hd.2.2.2.2.2.2.2.2.1.le
    exact hq.trans (mul_le_of_le_one_right hU.le
      (Real.rpow_le_one_of_one_le_of_nonpos hX (by linarith)))
  have hTail : tailCap d ≤ d.physicalFactorCap := by
    unfold tailCap MediumAtom.physicalFactorCap
    have h2 : 0 ≤ d.Q2 := by linarith [hd.2.2.2.1]
    have h3 : 0 ≤ d.Q3 := by linarith [hd.2.2.2.2.1]
    nlinarith [mul_nonneg h2 h3, mul_le_mul_of_nonneg_right hd.2.2.1 (mul_nonneg h2 h3)]
  refine ⟨hUV, hQU, ?_, ?_, ?_, ?_⟩
  · dsimp [betaLog]
    linarith [Real.log_nonneg (show 1 ≤ 2 * d.V by linarith [hd.2.1])]
  · dsimp [capLog]
    linarith [Real.log_nonneg (d.one_le_physicalFactorCap hd)]
  · dsimp [betaLog]
    exact add_le_add (le_refl 1) (Real.log_le_log (by linarith)
      (mul_le_mul_of_nonneg_left hUV (by norm_num)))
  · dsimp [capLog]
    exact add_le_add (le_refl 1) (Real.log_le_log
      (zero_lt_one.trans_le (one_le_tailCap hd)) hTail)

private theorem three_norms_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (Ybeta Ysupport : ℝ) :
    ‖d.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
      ‖d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ +
      ‖d.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport‖ ≤
        2 * (‖d.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
          ‖d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖) := by
  have he : d.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport =
      d.sharedSmallPairedLargeSupportedW Ybeta Ysupport -
        d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport := by
    rw [sharedSmallPairedLargeSupportedW_eq_zero_add_nonzero hd]
    ring
  have hh : ‖d.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport‖ ≤
      ‖d.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
        ‖d.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ := by
    rw [he]
    exact norm_sub_le _ _
  linarith

/-- Original geometry pays both actual outside second moments before the
large-square gain is converted to a power saving. -/
private theorem outside_three_norm_finite_bound (kappa : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom),
      0 < sigma → MediumAdmissible B sigma kappa c0 d → ∀ Ybeta Ysupport : ℝ,
        0 < Ysupport →
        outside d * (‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
          ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ +
          ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero Ybeta Ysupport‖) ≤
            C * d.scale ^ epsilon * d.scale ^ 2 *
              betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 / Real.sqrt Ysupport := by
  obtain ⟨C, hC, hwhole⟩ := cleanedAlpha_sharedSmallPairedLargeSupportedW_bound
    kappa hepsilon
  refine ⟨80 * C + 256 * |CommonSmoothCutoff.cutoffMass|, by positivity,
    fun B sigma c0 d hsigma hd Ybeta Ysupport hY ↦ ?_⟩
  have hX := one_le_scale hd
  have hX0 : 0 ≤ d.scale := zero_le_one.trans hX
  have hU : 0 < d.U := zero_lt_one.trans_le hd.1
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hQ : 0 < d.Q1 := zero_lt_one.trans_le hd.2.2.1
  have hS : 0 < Real.sqrt Ysupport := Real.sqrt_pos.mpr hY
  obtain ⟨hUV, hQU, hL, hCap, _hLU, hTail⟩ := log_and_scale_bounds hsigma hd
  have hQV : d.Q1 ≤ d.V := hQU.trans hUV
  have hLT : 0 ≤ 1 + Real.log (tailCap d) := by
    linarith [Real.log_nonneg (one_le_tailCap hd)]
  have hratio : 4 * d.V / d.Q1 + 1 ≤ 5 * d.V / d.Q1 := by
    apply (le_div_iff₀ hQ).mpr
    field_simp [hQ.ne']
    nlinarith
  have hbracket : d.U ^ 2 + d.Q1 * d.U ≤ 2 * d.U ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hQU hU.le]
  have hbracketZ : d.U ^ 2 / d.Q1 + d.U ≤ 2 * d.U ^ 2 / d.Q1 := by
    calc
      _ = (d.U ^ 2 + d.Q1 * d.U) / d.Q1 := by field_simp [hQ.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hbracket hQ.le
  have hE : 0 ≤ C * d.scale ^ epsilon := by positivity
  let F : ℝ := d.scale ^ epsilon * d.scale ^ 2 *
    betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 / Real.sqrt Ysupport
  have hw : outside d *
      ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ ≤
        (40 * C) * F := by
    calc
      _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
          (C * d.scale ^ epsilon * (4 * d.V / d.Q1 + 1) *
            (d.U ^ 2 + d.Q1 * d.U) / Real.sqrt Ysupport) :=
        mul_le_mul (d.sharedFirstFactor_outside_le hd)
          (hwhole B sigma c0 d hd Ybeta Ysupport hY) (norm_nonneg _) (by positivity)
      _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
          (C * d.scale ^ epsilon * (5 * d.V / d.Q1) *
            (2 * d.U ^ 2) / Real.sqrt Ysupport) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ hS.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left hratio hE) hbracket
          (by positivity) (by positivity)
      _ = (40 * C) * d.scale ^ epsilon * d.scale ^ 2 *
          betaLog d ^ ((2 ^ B) ^ 2 - 1) / Real.sqrt Ysupport := by
        unfold MediumAtom.scale
        field_simp [hQ.ne', hS.ne']
        ring
      _ ≤ ((40 * C) * d.scale ^ epsilon * d.scale ^ 2 *
          betaLog d ^ ((2 ^ B) ^ 2 - 1) / Real.sqrt Ysupport) * capLog d ^ 9 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hCap)
      _ = _ := by dsimp [F]; ring
  have hz : outside d *
      ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ ≤
        (128 * |CommonSmoothCutoff.cutoffMass|) * F := by
    have hzero := sharedSmallPairedLargeSupportedZero_bound
      (mediumAdmissible_cleanedAlphaAtom hd) Ybeta hY
    change ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖ ≤
      16 * |CommonSmoothCutoff.cutoffMass| * d.V * (1 + Real.log (tailCap d)) ^ 9 *
        (d.U ^ 2 / d.Q1 + d.U) / Real.sqrt Ysupport at hzero
    calc
      _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
          (16 * |CommonSmoothCutoff.cutoffMass| * d.V *
            (1 + Real.log (tailCap d)) ^ 9 *
              (d.U ^ 2 / d.Q1 + d.U) / Real.sqrt Ysupport) :=
        mul_le_mul (d.sharedFirstFactor_outside_le hd) hzero (norm_nonneg _) (by positivity)
      _ ≤ (4 * d.V * d.Q1 * betaLog d ^ ((2 ^ B) ^ 2 - 1)) *
          (16 * |CommonSmoothCutoff.cutoffMass| * d.V * capLog d ^ 9 *
            (2 * d.U ^ 2 / d.Q1) / Real.sqrt Ysupport) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ hS.le
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLT hTail 9) (by positivity))
          hbracketZ (by positivity) (by positivity)
      _ = (128 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ 2 *
          betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 / Real.sqrt Ysupport := by
        unfold MediumAtom.scale
        field_simp [hQ.ne', hS.ne']
        ring
      _ ≤ ((128 * |CommonSmoothCutoff.cutoffMass|) * d.scale ^ 2 *
          betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 / Real.sqrt Ysupport) *
            d.scale ^ epsilon := le_mul_of_one_le_right (by positivity)
              (Real.one_le_rpow hX hepsilon.le)
      _ = _ := by dsimp [F]; ring
  calc
    _ ≤ outside d *
        (2 * (‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
          ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖)) :=
      mul_le_mul_of_nonneg_left
        (three_norms_le (mediumAdmissible_cleanedAlphaAtom hd) Ybeta Ysupport)
        (outside_nonneg d)
    _ = 2 * (outside d *
        ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW Ybeta Ysupport‖ +
      outside d * ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero Ybeta Ysupport‖) :=
        by ring
    _ ≤ 2 * ((40 * C) * F + (128 * |CommonSmoothCutoff.cutoffMass|) * F) :=
      mul_le_mul_of_nonneg_left (add_le_add hw hz) (by norm_num)
    _ = _ := by dsimp [F]; ring

private theorem outside_three_norm_power_bound (B : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Ybeta : ℝ,
        outside d *
          (‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW
              Ybeta (d.scale ^ (sigma / 4))‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero
              Ybeta (d.scale ^ (sigma / 4))‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero
              Ybeta (d.scale ^ (sigma / 4))‖) ≤
            C * d.scale ^ (2 - sigma / 16) := by
  obtain ⟨C, hC, hfinite⟩ := outside_three_norm_finite_bound kappa
    (by linarith : 0 < sigma / 32)
  obtain ⟨x0, hx0, hlogs⟩ := eventually_actual_log_cost_le_rpow
    ((2 ^ B) ^ 2 - 1) 9 sigma hsigma (by linarith : 0 < sigma / 32)
  refine ⟨C, hC, x0, hx0, fun d hd hx Ybeta ↦ ?_⟩
  have hX : 0 < d.scale := zero_lt_one.trans_le (one_le_scale hd)
  have hY : 0 < d.scale ^ (sigma / 4) := Real.rpow_pos_of_pos hX _
  have hS : Real.sqrt (d.scale ^ (sigma / 4)) = d.scale ^ (sigma / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have hcost : betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 ≤
      d.scale ^ (sigma / 32) := hlogs B kappa c0 d hd hx
  calc
    _ ≤ C * d.scale ^ (sigma / 32) * d.scale ^ 2 *
        betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9 /
          Real.sqrt (d.scale ^ (sigma / 4)) :=
      hfinite B sigma c0 d hsigma hd Ybeta (d.scale ^ (sigma / 4)) hY
    _ = (C * d.scale ^ (sigma / 32) * d.scale ^ 2) *
        (betaLog d ^ ((2 ^ B) ^ 2 - 1) * capLog d ^ 9) /
          Real.sqrt (d.scale ^ (sigma / 4)) := by ring
    _ ≤ (C * d.scale ^ (sigma / 32) * d.scale ^ 2) * d.scale ^ (sigma / 32) /
        Real.sqrt (d.scale ^ (sigma / 4)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by positivity))
        (Real.sqrt_nonneg _)
    _ = C * d.scale ^ (2 - sigma / 16) := by
      rw [hS, ← Real.rpow_two]
      rw [show (C * d.scale ^ (sigma / 32) * d.scale ^ (2 : ℝ)) *
          d.scale ^ (sigma / 32) / d.scale ^ (sigma / 8) =
          C * ((d.scale ^ (sigma / 32) * d.scale ^ (2 : ℝ) *
            d.scale ^ (sigma / 32)) / d.scale ^ (sigma / 8)) by ring]
      rw [← Real.rpow_add hX, ← Real.rpow_add hX, ← Real.rpow_sub hX]
      congr 2
      ring

end SharedFirstFactorLargeSupportedDeletion

/-- One threshold precedes every original atom and every real paired-gcd
cutoff; both original outside second moments and all three norms are paid. -/
theorem actual_betaL2_gamma1L2_cleaned_sharedLargeSupported_log_payment
    (B : ℕ) (sigma kappa c0 A : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ d : MediumAtom,
      MediumAdmissible B sigma kappa c0 d → x0 ≤ d.scale → ∀ Ybeta : ℝ,
      (∑ n ∈ d.betaCarrier, (‖d.beta n‖ ^ 2)) *
        (∑ p ∈ d.primitiveFirstFactorCarrier, (‖d.gamma1 p‖ ^ 2)) *
          (‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedW
              Ybeta (d.scale ^ (sigma / 4))‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedZero
              Ybeta (d.scale ^ (sigma / 4))‖ +
            ‖d.cleanedAlphaAtom.sharedSmallPairedLargeSupportedNonzero
              Ybeta (d.scale ^ (sigma / 4))‖) ≤
              d.scale ^ 2 / (Real.log d.scale) ^ A := by
  obtain ⟨C, hC, x1, hx1, hpower⟩ :=
    SharedFirstFactorLargeSupportedDeletion.outside_three_norm_power_bound
      B sigma kappa c0 hsigma
  obtain ⟨x2, hx2⟩ := eventually_atTop.mp
    (eventually_const_rpow_two_le_logBudget C A hC.le (by linarith : 0 < sigma / 16))
  refine ⟨max x1 x2, hx1.trans_le (le_max_left _ _), fun d hd hx Ybeta ↦ ?_⟩
  exact (hpower d hd ((le_max_left _ _).trans hx) Ybeta).trans
    (hx2 d.scale ((le_max_right _ _).trans hx))

end

end ImbalancedChen.Part3
