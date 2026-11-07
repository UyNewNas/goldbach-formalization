import ImbalancedChen.Part3OriginalS2NativePsiGeometry
import Mathlib.Tactic

/-!
Actual individually owned coefficients on the actual smooth-q support.
The three mixed terms are estimated together on one d~2^k.d family.
The primitive Shiu boundary and original collapsed-tail theorem are the
only analytic inputs. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2NativeKeyTail

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2SmoothModulusValuationBridge
open ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail
open ImbalancedChen.Part3OriginalS2FullMixedTailPayment
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

private theorem nativeSmoothPart_pos (z : ℝ) (n : ℕ) : 0 < zSmoothPart z n := by
  unfold zSmoothPart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _

def keyThreeTailInner (d : MediumAtom) (x z : ℝ) (k : Key) (c : CoefficientIndex) : ℂ :=
  psiCoefficientInner d c (keyTail d x z k) (keyKept d x z k) +
    psiCoefficientInner d c (keyKept d x z k) (keyTail d x z k) +
    psiCoefficientInner d c (keyTail d x z k) (keyTail d x z k)

def nativeKeyTail (d : MediumAtom) (z : ℝ) (k : Key) : ℂ :=
  ∑ c ∈ nativeKeyFamily d z k, keyThreeTailInner d d.scale z k c

def nativeKeyModulusFamily (d : MediumAtom) (z : ℝ) (k : Key) (l : ℕ) :
    Finset CoefficientIndex :=
  (nativeKeyFamily d z k).filter (fun c => c.1.1 * c.1.2 * c.2.1 = l)

def nativeKeyModulusPacket (d : MediumAtom) (z : ℝ) (k : Key) (l : ℕ) : ℂ :=
  ∑ c ∈ nativeKeyModulusFamily d z k l, keyThreeTailInner d d.scale z k c

def nativeLogFactor
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (d : MediumAtom) : ℝ :=
  180 * hShiu.A * uniformEulerConstant 1 * logBudget (nativePhysicalCap d) *
    (1 + Real.log (roughCap d)) ^ 4 * Real.log (8 * d.scale)

theorem keyThreeTailInner_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x z : ℝ) (k : Key)
    (c : CoefficientIndex) (hc : c ∈ nativeCoefficientCarrier d z) :
    ‖keyThreeTailInner d x z k c‖ ≤
      coefficientCost d c * psiDivisorProgression d (c.1.1 * c.1.2 * c.2.1) := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hrpos := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hspos := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hlT := keyTail_norm_le_tau hd x z k c.1.2 c.2.1 (Nat.mul_pos hdpos hrpos)
  have hlK := keyKept_norm_le_tau hd x z k c.1.2 c.2.1 (Nat.mul_pos hdpos hrpos)
  have hrT := keyTail_norm_le_tau hd x z k c.1.2 c.2.2 (Nat.mul_pos hdpos hspos)
  have hrK := keyKept_norm_le_tau hd x z k c.1.2 c.2.2 (Nat.mul_pos hdpos hspos)
  have h₁ := psiCoefficientInner_norm_le hd c _ _ hlT hrK
  have h₂ := psiCoefficientInner_norm_le hd c _ _ hlK hrT
  have h₃ := psiCoefficientInner_norm_le hd c _ _ hlT hrT
  unfold keyThreeTailInner
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans (by
    dsimp [coefficientCost]
    nlinarith [h₁, h₂, h₃])

/-- Support is read from this very owned tail, even if different keys cancel. -/
theorem keyTail_small_data (d : MediumAtom) (x z : ℝ) (k : Key)
    (small rough : ℕ) (htail : keyTail d x z k small rough ≠ 0)
    (hy : 0 ≤ roughY x) :
    0 < small ∧ roughY x < (small : ℝ) ∧
      ∀ p : ℕ, z < (p : ℝ) → small.factorization p = 0 := by
  obtain ⟨v, hv, hlabel, hk, ht, hγ⟩ := keyTail_nonzero_witness d x z k small rough htail
  have hsmall : small = zSmoothPart z v.1 * zSmoothPart z v.2 :=
    congrArg Prod.fst hlabel.symm
  have h1 := nativeSmoothPart_pos z v.1
  have h2 := nativeSmoothPart_pos z v.2
  have h1R : (1 : ℝ) ≤ zSmoothPart z v.1 := by exact_mod_cast h1
  have h2R : (1 : ℝ) ≤ zSmoothPart z v.2 := by exact_mod_cast h2
  have hsmall1 : (zSmoothPart z v.1 : ℝ) ≤ small := by
    rw [hsmall, Nat.cast_mul]
    nlinarith
  have hsmall2 : (zSmoothPart z v.2 : ℝ) ≤ small := by
    rw [hsmall, Nat.cast_mul]
    nlinarith
  have hySmall : roughY x < (small : ℝ) := by
    simp only [individualSmoothWithinY, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact ht.trans_le hsmall1
    · exact ht.trans_le hsmall2
  refine ⟨by rw [hsmall]; positivity, hySmall, ?_⟩
  intro p hp
  rw [hsmall, Nat.factorization_mul h1.ne' h2.ne']
  simp [factorization_zSmoothPart, not_le.mpr hp]

theorem nonzero_keyThreeTail_has_tail (d : MediumAtom) (z : ℝ) (k : Key)
    (c : CoefficientIndex) (hne : keyThreeTailInner d d.scale z k c ≠ 0) :
    keyTail d d.scale z k c.1.2 c.2.1 ≠ 0 ∨
      keyTail d d.scale z k c.1.2 c.2.2 ≠ 0 := by
  by_contra h
  simp only [not_or, not_ne_iff] at h
  exact hne (by simp [keyThreeTailInner, psiCoefficientInner,
    samePsiTerm, s2TermWithM, h.1, h.2])

theorem nonzero_native_tail_collapsed
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key)
    (hphysical : nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)))
    (c : CoefficientIndex) (hc : c ∈ nativeCoefficientCarrier d z)
    (hne : keyThreeTailInner d d.scale z k c ≠ 0) :
    c.1.1 * c.1.2 * c.2.1 ∈ collapsedModuli d z := by
  have hqd := (Finset.mem_sigma.mp hc).1
  have hrs := (Finset.mem_sigma.mp hc).2
  have hq := (nativeQ_data (by linarith [hd.2.2.1]) (Finset.mem_product.mp hqd).1).2.2.2
  have hr := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hy : 0 ≤ roughY d.scale := Real.rpow_nonneg (by
    dsimp [MediumAtom.scale]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    positivity) _
  have hsmall : 0 < c.1.2 ∧ roughY d.scale < (c.1.2 : ℝ) ∧
      ∀ p : ℕ, z < (p : ℝ) → c.1.2.factorization p = 0 := by
    rcases nonzero_keyThreeTail_has_tail d z k c hne with h | h
    · exact keyTail_small_data d d.scale z k c.1.2 c.2.1 h hy
    · exact keyTail_small_data d d.scale z k c.1.2 c.2.2 h hy
  have hlpos : 0 < c.1.1 * c.1.2 * c.2.1 := by positivity
  have hdiv : c.1.2 ∣ c.1.1 * c.1.2 * c.2.1 := by
    refine ⟨c.1.1 * c.2.1, ?_⟩; ring
  have hsmooth := smooth_divisor_dvd_smooth_multiple z hsmall.1 hlpos hsmall.2.2 hdiv
  have hle := Nat.le_of_dvd (nativeSmoothPart_pos z _) hsmooth
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨hlpos, (native_supported_modulus_le hd z c hc).1.trans hphysical⟩,
    hsmall.2.1.trans_le (by exact_mod_cast hle)⟩

theorem nativeKeyTail_eq_collapsed_packets
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key)
    (hphysical : nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    nativeKeyTail d z k = ∑ l ∈ collapsedModuli d z, nativeKeyModulusPacket d z k l := by
  unfold nativeKeyTail nativeKeyModulusPacket nativeKeyModulusFamily
  calc
    _ = ∑ c ∈ nativeKeyFamily d z k, ∑ l ∈ collapsedModuli d z,
        if c.1.1 * c.1.2 * c.2.1 = l then keyThreeTailInner d d.scale z k c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hz : keyThreeTailInner d d.scale z k c = 0
      · simp [hz]
      · have hm := nonzero_native_tail_collapsed hd z k hphysical c
          (Finset.mem_filter.mp hc).1 hz
        simp [hm]
    _ = ∑ l ∈ collapsedModuli d z, ∑ c ∈ nativeKeyFamily d z k,
        if c.1.1 * c.1.2 * c.2.1 = l then keyThreeTailInner d d.scale z k c else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

theorem nonzero_native_packet_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (k : Key)
    (l : ℕ) (hne : nativeKeyModulusPacket d z k l ≠ 0) :
    Nat.Coprime l d.residue.natAbs := by
  have hw : ∃ c ∈ nativeKeyModulusFamily d z k l, keyThreeTailInner d d.scale z k c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun c hc => h c hc))
  obtain ⟨c, hc, hne⟩ := hw
  have hmod := (Finset.mem_filter.mp hc).2
  have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  have hqd := (Finset.mem_sigma.mp hs).1
  have hq := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).2
  have hl : keyTail d d.scale z k c.1.2 c.2.1 ≠ 0 ∨
      keyKept d d.scale z k c.1.2 c.2.1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hne (by simp [keyThreeTailInner, psiCoefficientInner,
      samePsiTerm, s2TermWithM, h.1, h.2])
  have hdc : Nat.Coprime (c.1.2 * c.2.1) d.residue.natAbs := by
    rcases hl with ht | hk
    · exact nonzero_labelSubset_coprime hd z c.1.2 c.2.1
        (fun q => keyPredicate z k q ∧ ¬individualSmoothWithinY d.scale z q) ht
    · exact nonzero_labelSubset_coprime hd z c.1.2 c.2.1
        (fun q => keyPredicate z k q ∧ individualSmoothWithinY d.scale z q) hk
  simpa only [← Nat.mul_assoc, hmod] using (Nat.coprime_mul_iff_left.mpr ⟨hq, hdc⟩)

theorem nativeKeyModulusPacket_return
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z : ℝ) (k : Key)
    (l : ℕ) (hl : 0 < l) (hmod : l ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖nativeKeyModulusPacket d z k l‖ ≤
      (nativeLogFactor hShiu d * fixedDScale d ((2 : ℝ) ^ k.d)) *
        ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
  let S := nativeKeyModulusFamily d z k l
  let Y := d.Q1 * (2 : ℝ) ^ k.d / 2
  have hS : S ⊆ nativeCoefficientCarrier d z :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hY : 0 < Y := by
    dsimp [Y]
    have hQ : 0 < d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hmodS : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l :=
    fun c hc => (Finset.mem_filter.mp hc).2
  have hlevel : ∀ c ∈ S, Y ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) :=
    fun c hc => nativeKey_level hd z k c (Finset.mem_filter.mp hc).1
  have hgeom : 0 ≤ nativeGeometryFactor d Y l := by
    unfold nativeGeometryFactor
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hlog := logBudget_nonneg (nativePhysicalCap d)
    positivity
  have hbudget : 0 ≤ progressionLogBudget hShiu d l := by
    unfold progressionLogBudget
    have hA := hShiu.A_pos.le
    have hE := (uniformEulerConstant_pos 1).le
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 8 * d.scale by linarith)
    positivity
  have hT : 0 ≤ psiDivisorProgression d l := by
    unfold psiDivisorProgression
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> positivity
  have hfin : ‖nativeKeyModulusPacket d z k l‖ ≤
      psiDivisorProgression d l * nativeGeometryFactor d Y l := by
    calc
      _ ≤ ∑ c ∈ S, ‖keyThreeTailInner d d.scale z k c‖ := norm_sum_le _ _
      _ ≤ ∑ c ∈ S, coefficientCost d c * psiDivisorProgression d l := by
        apply Finset.sum_le_sum
        intro c hc
        simpa only [hmodS c hc] using keyThreeTailInner_norm_le hd d.scale z k c (hS hc)
      _ = psiDivisorProgression d l * ∑ c ∈ S, coefficientCost d c := by
        rw [← Finset.sum_mul]; exact mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (nativeGeometry_le hd z Y hY S hS l hl hmodS hlevel) hT
  have hreturn : ‖nativeKeyModulusPacket d z k l‖ ≤
      progressionLogBudget hShiu d l * nativeGeometryFactor d Y l := by
    by_cases hz : nativeKeyModulusPacket d z k l = 0
    · rw [hz, norm_zero]
      exact mul_nonneg hbudget hgeom
    · have hcop := nonzero_native_packet_coprime hd z k l hz
      have hX0 : hShiu.X0 ≤ (firstWindowScale d : ℝ) := by
        have hK := (firstWindowScale_bounds d hx).1
        linarith
      have hmodR : (l : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5) :=
        (show (l : ℝ) ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) by exact_mod_cast hmod).trans
          (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ d.scale) _))
      exact hfin.trans (mul_le_mul_of_nonneg_right
        (psiDivisorProgression_le_logBudget hd hx hShiu l hl hcop hX0
          (physical_modulus_shiu_margin d hx hlarge l hmodR)) hgeom)
  calc
    _ ≤ progressionLogBudget hShiu d l * nativeGeometryFactor d Y l := hreturn
    _ = _ := by
      unfold progressionLogBudget nativeGeometryFactor nativeLogFactor fixedDScale Y
        MediumAtom.scale tauR
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem nativeKeyTail_le_collapsed_arithmetic
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z : ℝ) (k : Key)
    (hphysical : nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖nativeKeyTail d z k‖ ≤
      (nativeLogFactor hShiu d * fixedDScale d ((2 : ℝ) ^ k.d)) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5))) d.scale z := by
  rw [nativeKeyTail_eq_collapsed_packets hd z k hphysical]
  calc
    _ ≤ ∑ l ∈ collapsedModuli d z, ‖nativeKeyModulusPacket d z k l‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ collapsedModuli d z,
        (nativeLogFactor hShiu d * fixedDScale d ((2 : ℝ) ^ k.d)) *
          ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hli := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
      exact nativeKeyModulusPacket_return hd hShiu hx hlarge hthreshold z k l hli.1 hli.2
    _ = _ := by rw [← Finset.mul_sum]; rfl

end
end ImbalancedChen.Part3OriginalS2NativeKeyTail
