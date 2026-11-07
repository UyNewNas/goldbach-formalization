import ImbalancedChen.Part3OriginalS2ActualBlockGeometry
import ImbalancedChen.Part3OriginalGevreyFinalPsi
import Mathlib.Tactic

/-!
The same constructed Gevrey paperPsi is used at q/Q1 and m/V.
The old commonSmoothWeight is only an explicit specialization of the
m-polymorphic expression below; it is not identified with paperPsi.
The old finite commonSmoothCarrier is retained because it contains the
entire support of the new m cutoff. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2SameGevreyPacket

open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2ExactSmoothTailExpansion
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2ActualPsiWeightAdapter
open ImbalancedChen.Part3OriginalS2ShiuPrimitiveFiber
open ImbalancedChen.Part3OriginalS2LambdaDivisorPacket
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ZeroGramCompiler
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open Classical Finset
open scoped BigOperators

noncomputable section

def actualPsiMWeight (d : MediumAtom) (m : ℕ) : ℝ := paperPsi ((m : ℝ) / d.V)

theorem actualPsiMWeight_nonneg (d : MediumAtom) (m : ℕ) :
    0 ≤ actualPsiMWeight d m := paperPsi_nonneg _

theorem actualPsiMWeight_le_one (d : MediumAtom) (m : ℕ) :
    actualPsiMWeight d m ≤ 1 := paperPsi_le_one _

theorem actualPsiMWeight_zero (d : MediumAtom) : actualPsiMWeight d 0 = 0 := by
  apply paperPsi_zero_outside
  left
  norm_num

theorem actualPsiMWeight_support
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (m : ℕ)
    (hne : actualPsiMWeight d m ≠ 0) :
    d.V / 2 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 5 * d.V / 2 ∧
      m ∈ d.transposedAtom.commonSmoothCarrier := by
  have hV : 0 < d.V := by linarith [hd.2.1]
  have hlo : (1 / 2 : ℝ) ≤ (m : ℝ) / d.V := by
    by_contra h
    exact hne (paperPsi_zero_outside _ (Or.inl (lt_of_not_ge h)))
  have hhi : (m : ℝ) / d.V ≤ (5 / 2 : ℝ) := by
    by_contra h
    exact hne (paperPsi_zero_outside _ (Or.inr (lt_of_not_ge h)))
  have hmlo : d.V / 2 ≤ (m : ℝ) := by
    have h := (le_div_iff₀ hV).mp hlo
    linarith
  have hmhi : (m : ℝ) ≤ 5 * d.V / 2 := by
    have h := (div_le_iff₀ hV).mp hhi
    linarith
  refine ⟨hmlo, hmhi, ?_⟩
  change m ∈ Finset.Icc 0 (Nat.ceil (3 * d.V))
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by
    exact_mod_cast (hmhi.trans (by linarith)).trans (Nat.le_ceil (3 * d.V))⟩

/-- The two primitive alpha gates, actual moving residue and phi(q*d*s)
are unchanged when the common m majorant is made explicit. -/
def s2TermWithM (d : MediumAtom) (qWeight : ℕ → ℂ) (mWeight : ℕ → ℝ)
    (left right : ℕ → ℕ → ℂ) (t : S2Index) : ℂ :=
  if Nat.Coprime t.2.2.1.1 (t.1.1 * t.1.2 * t.2.1.1) ∧
      Nat.Coprime t.2.2.1.2 (t.1.1 * t.1.2 * t.2.1.2) ∧
      Int.ModEq (t.1.1 * t.1.2 * t.2.1.1)
        (((t.2.2.2 * t.2.2.1.1 : ℕ) : ℤ)) d.residue then
    qWeight t.1.1 * left t.1.2 t.2.1.1 * star (right t.1.2 t.2.1.2) *
      d.alpha t.2.2.1.1 * star (d.alpha t.2.2.1.2) * (mWeight t.2.2.2 : ℂ) /
        (Nat.totient (t.1.1 * t.1.2 * t.2.1.2) : ℂ)
  else 0

theorem s2TermWithM_old_specialization (d : MediumAtom) (qWeight : ℕ → ℂ)
    (left right : ℕ → ℕ → ℂ) (t : S2Index) :
    s2TermWithM d qWeight d.transposedAtom.commonSmoothWeight left right t =
      s2TermWithCoefficients d qWeight left right t := rfl

def samePsiTerm (d : MediumAtom) (left right : ℕ → ℕ → ℂ) (t : S2Index) : ℂ :=
  s2TermWithM d (actualPsiQWeight d) (actualPsiMWeight d) left right t

/-- Literal q and m use one and the same constructed function paperPsi. -/
theorem samePsiTerm_formula (d : MediumAtom) (left right : ℕ → ℕ → ℂ)
    (t : S2Index) : samePsiTerm d left right t =
    if Nat.Coprime t.2.2.1.1 (t.1.1 * t.1.2 * t.2.1.1) ∧
      Nat.Coprime t.2.2.1.2 (t.1.1 * t.1.2 * t.2.1.2) ∧
      Int.ModEq (t.1.1 * t.1.2 * t.2.1.1)
        (((t.2.2.2 * t.2.2.1.1 : ℕ) : ℤ)) d.residue then
      (paperPsi ((t.1.1 : ℝ) / d.Q1) : ℂ) * left t.1.2 t.2.1.1 *
        star (right t.1.2 t.2.1.2) * d.alpha t.2.2.1.1 *
        star (d.alpha t.2.2.1.2) *
        (paperPsi ((t.2.2.2 : ℝ) / d.V) : ℂ) /
          (Nat.totient (t.1.1 * t.1.2 * t.2.1.2) : ℂ)
    else 0 := rfl

theorem samePsiTerm_smooth_four_way (d : MediumAtom) (x z : ℝ) (t : S2Index) :
    samePsiTerm d (Lambda d z) (Lambda d z) t =
      samePsiTerm d (lambdaSmoothKept d x z) (lambdaSmoothKept d x z) t +
      samePsiTerm d (lambdaSmoothTail d x z) (lambdaSmoothKept d x z) t +
      samePsiTerm d (lambdaSmoothKept d x z) (lambdaSmoothTail d x z) t +
      samePsiTerm d (lambdaSmoothTail d x z) (lambdaSmoothTail d x z) t := by
  unfold samePsiTerm s2TermWithM
  by_cases hg : Nat.Coprime t.2.2.1.1 (t.1.1 * t.1.2 * t.2.1.1) ∧
      Nat.Coprime t.2.2.1.2 (t.1.1 * t.1.2 * t.2.1.2) ∧
      Int.ModEq (t.1.1 * t.1.2 * t.2.1.1)
        (((t.2.2.2 * t.2.2.1.1 : ℕ) : ℤ)) d.residue
  · simp only [if_pos hg]
    rw [Lambda_eq_smoothKept_add_tail d x z t.1.2 t.2.1.1,
      Lambda_eq_smoothKept_add_tail d x z t.1.2 t.2.1.2]
    simp only [star_add]
    ring
  · simp [hg]

def psiMNCarrier (d : MediumAtom) : Finset (ℕ × ℕ) :=
  (mnCarrier d).filter (fun nm => actualPsiMWeight d nm.2 ≠ 0)

def psiMNImage (d : MediumAtom) : Finset ℕ :=
  (psiMNCarrier d).image (fun nm => nm.1 * nm.2)

def psiPairWeight (d : MediumAtom) (l : ℕ) (nm : ℕ × ℕ) : ℂ :=
  if Nat.Coprime nm.1 l then d.alpha nm.1 * (actualPsiMWeight d nm.2 : ℂ) else 0

def psiProgression (d : MediumAtom) (l : ℕ) : ℂ :=
  ∑ nm ∈ mnCarrier d,
    if Int.ModEq l (((nm.1 * nm.2 : ℕ) : ℤ)) d.residue then
      psiPairWeight d l nm else 0

def psiDivisorProgression (d : MediumAtom) (l : ℕ) : ℝ :=
  ∑ v ∈ psiMNImage d,
    if Int.ModEq l (v : ℤ) d.residue then (v.divisors.card : ℝ) else 0

/-- Nonzero Gevrey product support is a fixed long interval around x=U*V.
This removes the unsupported small-v branch of a full Cartesian image. -/
theorem psiMNImage_physical_interval
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {v : ℕ}
    (hv : v ∈ psiMNImage d) :
    d.scale / 2 ≤ (v : ℝ) ∧ (v : ℝ) ≤ 5 * d.scale ∧ 0 < v := by
  obtain ⟨nm, hnm, rfl⟩ := Finset.mem_image.mp hv
  have hpair := (Finset.mem_filter.mp hnm).1
  have hpsi := (Finset.mem_filter.mp hnm).2
  have hn := (Finset.mem_product.mp hpair).1
  have hnraw := (Finset.mem_filter.mp hn).1
  have hnlo : d.U ≤ (nm.1 : ℝ) :=
    (Nat.le_ceil d.U).trans (by exact_mod_cast (Finset.mem_Icc.mp hnraw).1)
  have hnhi : (nm.1 : ℝ) ≤ 2 * d.U :=
    (show (nm.1 : ℝ) ≤ (Nat.floor (2 * d.U) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hnraw).2).trans
        (Nat.floor_le (by linarith [hd.1]))
  obtain ⟨hmlo, hmhi, _⟩ := actualPsiMWeight_support hd nm.2 hpsi
  have hU : 0 < d.U := by linarith [hd.1]
  have hV : 0 < d.V := by linarith [hd.2.1]
  have hlo := mul_le_mul hnlo hmlo (by positivity : 0 ≤ d.V / 2) (Nat.cast_nonneg _)
  have hhi := mul_le_mul hnhi hmhi (Nat.cast_nonneg _) (by positivity : 0 ≤ 2 * d.U)
  have hp : (0 : ℝ) < (nm.1 : ℝ) * (nm.2 : ℝ) := by
    nlinarith [mul_pos hU hV]
  constructor
  · dsimp [MediumAtom.scale]
    push_cast
    nlinarith [hlo]
  constructor
  · dsimp [MediumAtom.scale]
    push_cast
    nlinarith [hhi]
  · exact_mod_cast hp

private theorem psiProgression_eq_fibers (d : MediumAtom) (l : ℕ) :
    psiProgression d l = ∑ v ∈ psiMNImage d,
      if Int.ModEq l (v : ℤ) d.residue then
        ∑ nm ∈ (psiMNCarrier d).filter (fun nm => nm.1 * nm.2 = v),
          psiPairWeight d l nm else 0 := by
  have hrestrict : psiProgression d l =
      ∑ nm ∈ psiMNCarrier d,
        if Int.ModEq l (((nm.1 * nm.2 : ℕ) : ℤ)) d.residue then
          psiPairWeight d l nm else 0 := by
    unfold psiProgression psiMNCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro nm hnm
    by_cases hp : actualPsiMWeight d nm.2 = 0
    · simp [hp, psiPairWeight]
    · simp [hp]
  rw [hrestrict]
  let P := psiMNCarrier d
  let V := psiMNImage d
  calc
    _ = ∑ nm ∈ P, ∑ v ∈ V,
        if nm.1 * nm.2 = v then
          (if Int.ModEq l (v : ℤ) d.residue then psiPairWeight d l nm else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro nm hnm
          have hp : nm.1 * nm.2 ∈ V := Finset.mem_image_of_mem _ hnm
          simp [hp]
    _ = ∑ v ∈ V, ∑ nm ∈ P,
        if nm.1 * nm.2 = v then
          (if Int.ModEq l (v : ℤ) d.residue then psiPairWeight d l nm else 0)
        else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      by_cases hmod : Int.ModEq l (v : ℤ) d.residue <;>
        simp [hmod, P, Finset.sum_ite]

theorem psiProgression_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (l : ℕ) :
    ‖psiProgression d l‖ ≤ psiDivisorProgression d l := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _, _, _, _, _⟩ := hd
  have hfiber (v : ℕ) (hv : v ∈ psiMNImage d) :
      ‖∑ nm ∈ (psiMNCarrier d).filter (fun nm => nm.1 * nm.2 = v),
        psiPairWeight d l nm‖ ≤ (v.divisors.card : ℝ) := by
    let S := (psiMNCarrier d).filter (fun nm => nm.1 * nm.2 = v)
    have hsub : S ⊆ (mnCarrier d).filter (fun nm => nm.1 * nm.2 = v) := by
      intro nm hnm
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hnm).1).1,
          (Finset.mem_filter.mp hnm).2⟩
    have hcard := (Finset.card_le_card hsub).trans
      (mn_fiber_card_le_tau d v (psiMNImage_physical_interval hd hv).2.2)
    calc
      _ ≤ ∑ nm ∈ S, ‖psiPairWeight d l nm‖ := norm_sum_le _ _
      _ ≤ ∑ _nm ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro nm hnm
        have hn := (Finset.mem_product.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hnm).1).1).1
        have ha := hAlpha nm.1 hn
        have hw : ‖(actualPsiMWeight d nm.2 : ℂ)‖ ≤ 1 := by
          simpa [Complex.norm_real, abs_of_nonneg (actualPsiMWeight_nonneg d nm.2)]
            using actualPsiMWeight_le_one d nm.2
        by_cases hc : Nat.Coprime nm.1 l
        · simp only [psiPairWeight, if_pos hc, norm_mul]
          exact (mul_le_mul ha hw (norm_nonneg _) zero_le_one).trans (by norm_num)
        · simp [psiPairWeight, hc]
      _ = (S.card : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast hcard
  rw [psiProgression_eq_fibers]
  calc
    _ ≤ ∑ v ∈ psiMNImage d,
        ‖if Int.ModEq l (v : ℤ) d.residue then
          ∑ nm ∈ (psiMNCarrier d).filter (fun nm => nm.1 * nm.2 = v),
            psiPairWeight d l nm else 0‖ := norm_sum_le _ _
    _ ≤ psiDivisorProgression d l := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases hm : Int.ModEq l (v : ℤ) d.residue
      · simpa only [hm, if_true] using hfiber v hv
      · simp [hm]

def psiCoefficientInner (d : MediumAtom) (c : CoefficientIndex)
    (left right : ℕ → ℕ → ℂ) : ℂ :=
  ∑ n₁ ∈ d.alphaCarrier, ∑ n₂ ∈ d.alphaCarrier,
    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      samePsiTerm d left right ⟨c.1, (c.2, ((n₁, n₂), m))⟩

theorem psiCoefficientInner_factor (d : MediumAtom) (c : CoefficientIndex)
    (left right : ℕ → ℕ → ℂ) :
    psiCoefficientInner d c left right =
      (actualPsiQWeight d c.1.1 * left c.1.2 c.2.1 *
        star (right c.1.2 c.2.2) /
          (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℂ)) *
        freeAlphaMass d (c.1.1 * c.1.2 * c.2.2) *
        psiProgression d (c.1.1 * c.1.2 * c.2.1) := by
  let K := actualPsiQWeight d c.1.1 * left c.1.2 c.2.1 *
    star (right c.1.2 c.2.2) / (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℂ)
  let F : ℕ → ℂ := fun n₂ =>
    if Nat.Coprime n₂ (c.1.1 * c.1.2 * c.2.2) then star (d.alpha n₂) else 0
  let G : ℕ → ℕ → ℂ := fun n₁ m =>
    if Int.ModEq (c.1.1 * c.1.2 * c.2.1)
      (((n₁ * m : ℕ) : ℤ)) d.residue then
        psiPairWeight d (c.1.1 * c.1.2 * c.2.1) (n₁, m) else 0
  have hterm (n₁ n₂ m : ℕ) :
      samePsiTerm d left right ⟨c.1, (c.2, ((n₁, n₂), m))⟩ = K * F n₂ * G n₁ m := by
    by_cases h₁ : Nat.Coprime n₁ (c.1.1 * c.1.2 * c.2.1) <;>
      by_cases h₂ : Nat.Coprime n₂ (c.1.1 * c.1.2 * c.2.2) <;>
      by_cases ha : Int.ModEq (c.1.1 * c.1.2 * c.2.1)
        (((n₁ * m : ℕ) : ℤ)) d.residue <;>
      simp [samePsiTerm, s2TermWithM, psiPairWeight, K, F, G,
        h₁, h₂, Nat.mul_comm m n₁, ha] <;> ring
  unfold psiCoefficientInner
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [K, F, G, freeAlphaMass, psiProgression, mnCarrier, Finset.sum_product]

theorem psiCoefficientInner_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (c : CoefficientIndex) (left right : ℕ → ℕ → ℂ)
    (hleft : ‖left c.1.2 c.2.1‖ ≤ ((c.1.2 * c.2.1).divisors.card : ℝ))
    (hright : ‖right c.1.2 c.2.2‖ ≤ ((c.1.2 * c.2.2).divisors.card : ℝ)) :
    ‖psiCoefficientInner d c left right‖ ≤
      (((c.1.2 * c.2.1).divisors.card : ℝ) *
        ((c.1.2 * c.2.2).divisors.card : ℝ) *
          freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) /
            (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) *
        psiDivisorProgression d (c.1.1 * c.1.2 * c.2.1) := by
  have hq := actualPsiQWeight_norm_le_one d c.1.1
  have hf := freeAlphaMass_norm_le_count hd (c.1.1 * c.1.2 * c.2.2)
  have hp := psiProgression_norm_le hd (c.1.1 * c.1.2 * c.2.1)
  have hfn := freeAlphaCount_nonneg d (c.1.1 * c.1.2 * c.2.2)
  have hpn : 0 ≤ psiDivisorProgression d (c.1.1 * c.1.2 * c.2.1) :=
    (norm_nonneg _).trans hp
  rw [psiCoefficientInner_factor]
  simp only [norm_mul, norm_div, norm_star, Complex.norm_natCast]
  calc
    _ ≤ (1 * ((c.1.2 * c.2.1).divisors.card : ℝ) *
        ((c.1.2 * c.2.2).divisors.card : ℝ) /
          (Nat.totient (c.1.1 * c.1.2 * c.2.2) : ℝ)) *
        freeAlphaCount d (c.1.1 * c.1.2 * c.2.2) *
        psiDivisorProgression d (c.1.1 * c.1.2 * c.2.1) := by
          gcongr <;> first | assumption | positivity
    _ = _ := by ring

def psiThreeTailInner (d : MediumAtom) (x z : ℝ) (c : CoefficientIndex) : ℂ :=
  psiCoefficientInner d c (lambdaSmoothTail d x z) (lambdaSmoothKept d x z) +
    psiCoefficientInner d c (lambdaSmoothKept d x z) (lambdaSmoothTail d x z) +
    psiCoefficientInner d c (lambdaSmoothTail d x z) (lambdaSmoothTail d x z)

def samePsiBlockPacket (d : MediumAtom) (x z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ c ∈ blockCoefficientCarrier d z D R l, psiThreeTailInner d x z c

def samePsiFullBlockPacket (d : MediumAtom) (z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ c ∈ blockCoefficientCarrier d z D R l,
    psiCoefficientInner d c (Lambda d z) (Lambda d z)

def samePsiKeptBlockPacket (d : MediumAtom) (x z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ c ∈ blockCoefficientCarrier d z D R l,
    psiCoefficientInner d c (lambdaSmoothKept d x z) (lambdaSmoothKept d x z)

/-- The packet bounded here is exactly the difference between full and
smooth-kept actual same-psi S2, with all three cross/tail terms retained. -/
theorem samePsiFullBlockPacket_eq_kept_add_tail
    (d : MediumAtom) (x z D R : ℝ) (l : ℕ) :
    samePsiFullBlockPacket d z D R l =
      samePsiKeptBlockPacket d x z D R l + samePsiBlockPacket d x z D R l := by
  unfold samePsiFullBlockPacket samePsiKeptBlockPacket samePsiBlockPacket
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  unfold psiThreeTailInner psiCoefficientInner
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n₁ hn₁
  apply Finset.sum_congr rfl
  intro n₂ hn₂
  apply Finset.sum_congr rfl
  intro m hm
  simpa only [add_assoc] using
    samePsiTerm_smooth_four_way d x z ⟨c.1, (c.2, ((n₁, n₂), m))⟩

def samePsiPaperBlockPacket (d : MediumAtom) (x z D R : ℝ) (l : ℕ) : ℂ :=
  ∑ o ∈ (paperBlockOuterCarrier d z D R).filter
      (fun o => o.1.1 * o.1.2 * o.2.1.1 = l),
    ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      (samePsiTerm d (lambdaSmoothTail d x z) (lambdaSmoothKept d x z)
          ⟨o.1, (o.2.1, (o.2.2, m))⟩ +
        samePsiTerm d (lambdaSmoothKept d x z) (lambdaSmoothTail d x z)
          ⟨o.1, (o.2.1, (o.2.2, m))⟩ +
        samePsiTerm d (lambdaSmoothTail d x z) (lambdaSmoothTail d x z)
          ⟨o.1, (o.2.1, (o.2.2, m))⟩)

theorem samePsiPaperBlockPacket_eq_packet (d : MediumAtom)
    (x z D R : ℝ) (l : ℕ) :
    samePsiPaperBlockPacket d x z D R l = samePsiBlockPacket d x z D R l := by
  unfold samePsiPaperBlockPacket samePsiBlockPacket
    paperBlockOuterCarrier s2OuterCarrier blockCoefficientCarrier coefficientCarrier
  simp only [Finset.filter_filter, Finset.sum_filter, Finset.sum_sigma,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hb : D ≤ (small : ℝ) ∧ (small : ℝ) < 2 * D ∧
      R ≤ (r : ℝ) ∧ (r : ℝ) < 2 * R ∧
      R ≤ (s : ℝ) ∧ (s : ℝ) < 2 * R
  · by_cases hl : q * small * r = l
    · simp [inPaperBlock, hb, hl, psiThreeTailInner, psiCoefficientInner,
        Finset.sum_add_distrib]
    · simp [inPaperBlock, hb, hl]
  · simp [inPaperBlock, hb]

theorem psiThreeTailInner_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (x z : ℝ)
    (c : CoefficientIndex) (hc : c ∈ coefficientCarrier d z) :
    ‖psiThreeTailInner d x z c‖ ≤
      coefficientCost d c * psiDivisorProgression d (c.1.1 * c.1.2 * c.2.1) := by
  obtain ⟨hqd, hrs⟩ := Finset.mem_sigma.mp hc
  have hdpos := dCarrier_pos d z c.1.2 (Finset.mem_product.mp hqd).2
  have hrpos := roughFiber_pos d z c.1.2 c.2.1 (Finset.mem_product.mp hrs).1
  have hspos := roughFiber_pos d z c.1.2 c.2.2 (Finset.mem_product.mp hrs).2
  have hlT := lambdaSmoothTail_norm_le_tau hd x z c.1.2 c.2.1 (Nat.mul_pos hdpos hrpos)
  have hlK := lambdaSmoothKept_norm_le_tau hd x z c.1.2 c.2.1 (Nat.mul_pos hdpos hrpos)
  have hrT := lambdaSmoothTail_norm_le_tau hd x z c.1.2 c.2.2 (Nat.mul_pos hdpos hspos)
  have hrK := lambdaSmoothKept_norm_le_tau hd x z c.1.2 c.2.2 (Nat.mul_pos hdpos hspos)
  have h₁ := psiCoefficientInner_norm_le hd c _ _ hlT hrK
  have h₂ := psiCoefficientInner_norm_le hd c _ _ hlK hrT
  have h₃ := psiCoefficientInner_norm_le hd c _ _ hlT hrT
  unfold psiThreeTailInner
  exact ((norm_add_le _ _).trans
    (add_le_add_right (norm_add_le _ _) _)).trans (by
      dsimp [coefficientCost]
      nlinarith [h₁, h₂, h₃])

theorem samePsiBlockPacket_norm_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (l : ℕ) :
    ‖samePsiBlockPacket d x z D R l‖ ≤
      psiDivisorProgression d l * blockGeometryCost d z D R l := by
  unfold samePsiBlockPacket
  calc
    _ ≤ ∑ c ∈ blockCoefficientCarrier d z D R l,
        ‖psiThreeTailInner d x z c‖ := norm_sum_le _ _
    _ ≤ ∑ c ∈ blockCoefficientCarrier d z D R l,
        coefficientCost d c * psiDivisorProgression d l := by
      apply Finset.sum_le_sum
      intro c hc
      have hsource := (Finset.mem_filter.mp hc).1
      have hl := (Finset.mem_filter.mp hc).2.2
      simpa only [hl] using psiThreeTailInner_norm_le hd x z c hsource
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem samePsiBlockPacket_norm_le_geometry
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (hD : 0 < D) (l : ℕ) (hl : 0 < l) :
    ‖samePsiBlockPacket d x z D R l‖ ≤
      psiDivisorProgression d l * geometryFactor d D l := by
  have hp : 0 ≤ psiDivisorProgression d l := by
    unfold psiDivisorProgression
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> positivity
  exact (samePsiBlockPacket_norm_le hd x z D R l).trans
    (mul_le_mul_of_nonneg_left (blockGeometryCost_le hd z D R hD l hl) hp)

theorem nonzero_samePsiBlockPacket_coprime
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (x z D R : ℝ) (l : ℕ) (hne : samePsiBlockPacket d x z D R l ≠ 0) :
    Nat.Coprime l d.residue.natAbs := by
  have hwit : ∃ c ∈ blockCoefficientCarrier d z D R l,
      psiThreeTailInner d x z c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Finset.sum_eq_zero (fun c hc => h c hc))
  obtain ⟨c, hc, hterm⟩ := hwit
  have hsource := (Finset.mem_filter.mp hc).1
  have hl := (Finset.mem_filter.mp hc).2.2
  have hq := (Finset.mem_product.mp (Finset.mem_sigma.mp hsource).1).1
  have hqc := (Finset.mem_filter.mp hq).2
  have hleft : lambdaSmoothTail d x z c.1.2 c.2.1 ≠ 0 ∨
      lambdaSmoothKept d x z c.1.2 c.2.1 ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    exact hterm (by simp [psiThreeTailInner, psiCoefficientInner,
      samePsiTerm, s2TermWithM, h.1, h.2])
  have hdc : Nat.Coprime (c.1.2 * c.2.1) d.residue.natAbs := by
    rcases hleft with ht | hk
    · exact nonzero_smoothTail_coprime hd x z c.1.2 c.2.1 ht
    · exact nonzero_smoothKept_coprime hd x z c.1.2 c.2.1 hk
  have hprod := Nat.coprime_mul_iff_left.mpr ⟨hqc, hdc⟩
  simpa only [← Nat.mul_assoc, hl] using hprod

end
end ImbalancedChen.Part3OriginalS2SameGevreyPacket
