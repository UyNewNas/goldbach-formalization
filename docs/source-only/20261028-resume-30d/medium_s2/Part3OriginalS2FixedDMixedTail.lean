import ImbalancedChen.Part3OriginalS2FullMixedTailPayment
import Mathlib.Tactic

/-!
The manuscript preliminary d~D family is ONE subfamily containing all d
in [D,2D), and all independent r,s rough bins. Its normalizer remains
V(D)=M*N^2/(Q1*D). The weaker whole-family V0 bound is never used to pay D.
SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2FixedDMixedTail

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2SmoothYRankinStart
open ImbalancedChen.Part3OriginalS2ActualBlockPacketBound
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2MixedFamilyGeometry
open ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail
open ImbalancedChen.Part3OriginalS2FullMixedTailPayment
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def fixedDFamily (d : MediumAtom) (z D : ℝ) : Finset CoefficientIndex :=
  (coefficientCarrier d z).filter
    (fun c => D ≤ (c.1.2 : ℝ) ∧ (c.1.2 : ℝ) < 2 * D)

def fixedDModulusCarrier (d : MediumAtom) (z D : ℝ) (l : ℕ) : Finset CoefficientIndex :=
  (fixedDFamily d z D).filter (fun c => c.1.1 * c.1.2 * c.2.1 = l)

def fixedDTail (d : MediumAtom) (z D : ℝ) : ℂ := subsetPacket d z (fixedDFamily d z D)

def fixedDModulusPacket (d : MediumAtom) (z D : ℝ) (l : ℕ) : ℂ :=
  subsetPacket d z (fixedDModulusCarrier d z D l)

def fixedDScale (d : MediumAtom) (D : ℝ) : ℝ := d.V * d.U ^ 2 / (d.Q1 * D)

/-- The actual original S2 carrier, with only its one preliminary d cut. -/
def fixedDActualCoefficientSum (d : MediumAtom) (z D : ℝ)
    (left right : ℕ → ℕ → ℂ) : ℂ :=
  ∑ t ∈ (s2Carrier d z).filter
      (fun t => D ≤ (t.1.2 : ℝ) ∧ (t.1.2 : ℝ) < 2 * D),
    samePsiTerm d left right t

theorem fixedDActualCoefficientSum_eq_family (d : MediumAtom) (z D : ℝ)
    (left right : ℕ → ℕ → ℂ) :
    fixedDActualCoefficientSum d z D left right =
      ∑ c ∈ fixedDFamily d z D, psiCoefficientInner d c left right := by
  unfold fixedDActualCoefficientSum fixedDFamily coefficientCarrier
    psiCoefficientInner s2Carrier
  simp only [Finset.sum_filter, Finset.sum_sigma, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro small hsmall
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hb : D ≤ (small : ℝ) ∧ (small : ℝ) < 2 * D <;> simp [hb]

/-- This bounds exactly the difference between full and smooth-kept S2
on one d~D family of the original carrier, with both Gevrey cutoffs. -/
theorem fixedDActualS2_eq_kept_add_tail (d : MediumAtom) (z D : ℝ) :
    fixedDActualCoefficientSum d z D (Lambda d z) (Lambda d z) =
      fixedDActualCoefficientSum d z D
        (lambdaSmoothKept d d.scale z) (lambdaSmoothKept d d.scale z) +
        fixedDTail d z D := by
  rw [fixedDActualCoefficientSum_eq_family, fixedDActualCoefficientSum_eq_family]
  unfold fixedDTail subsetPacket
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
    samePsiTerm_smooth_four_way d d.scale z ⟨c.1, (c.2, ((n₁, n₂), m))⟩

/-- No r/s common-window condition occurs in this actual preliminary family. -/
theorem mem_fixedDFamily (d : MediumAtom) (z D : ℝ) (c : CoefficientIndex) :
    c ∈ fixedDFamily d z D ↔ c ∈ coefficientCarrier d z ∧
      D ≤ (c.1.2 : ℝ) ∧ (c.1.2 : ℝ) < 2 * D := by
  exact Finset.mem_filter

theorem fixedD_level_lower
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z D : ℝ) (hD : 0 < D)
    (c : CoefficientIndex) (hc : c ∈ fixedDFamily d z D) :
    d.Q1 * D ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
  have hsource := (Finset.mem_filter.mp hc).1
  have hdlo := (Finset.mem_filter.mp hc).2.1
  have hqd := (Finset.mem_sigma.mp hsource).1
  have hqraw := (Finset.mem_filter.mp (Finset.mem_product.mp hqd).1).1
  have hqlo : d.Q1 ≤ (c.1.1 : ℝ) :=
    (Nat.le_ceil d.Q1).trans (by exact_mod_cast (Finset.mem_Icc.mp hqraw).1)
  rw [Nat.cast_mul]
  exact mul_le_mul hqlo hdlo hD.le (Nat.cast_nonneg _)

theorem fixedDTail_eq_collapsed_packets
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z D : ℝ)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    fixedDTail d z D = ∑ l ∈ collapsedModuli d z, fixedDModulusPacket d z D l := by
  unfold fixedDTail fixedDModulusPacket subsetPacket fixedDModulusCarrier
  calc
    _ = ∑ c ∈ fixedDFamily d z D, ∑ l ∈ collapsedModuli d z,
        if c.1.1 * c.1.2 * c.2.1 = l then psiThreeTailInner d d.scale z c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hz : psiThreeTailInner d d.scale z c = 0
      · simp [hz]
      · have hm := nonzero_psiTail_modulus_mem_collapsed hd z hphysical c
          (Finset.mem_filter.mp hc).1 hz
        simp [hm]
    _ = ∑ l ∈ collapsedModuli d z, ∑ c ∈ fixedDFamily d z D,
        if c.1.1 * c.1.2 * c.2.1 = l then psiThreeTailInner d d.scale z c else 0 :=
      Finset.sum_comm
    _ = _ := by simp only [Finset.sum_filter]

/-- Genuine Shiu return on the whole d~D family at once. The actual
subset geometry uses Y=Q1*D BEFORE any arithmetic or dyadic sum. -/
theorem fixedDModulusPacket_return
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z D : ℝ) (hD : 0 < D)
    (l : ℕ) (hl : 0 < l) (hmod : l ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖fixedDModulusPacket d z D l‖ ≤
      (wholeLogFactor hShiu d * fixedDScale d D) *
        ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
  let S := fixedDModulusCarrier d z D l
  have hS : S ⊆ coefficientCarrier d z :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hmodS : ∀ c ∈ S, c.1.1 * c.1.2 * c.2.1 = l := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hQ : 0 < d.Q1 := by linarith [hd.2.2.1]
  have hY : 0 < d.Q1 * D := mul_pos hQ hD
  have hlevel : ∀ c ∈ S, d.Q1 * D ≤ ((c.1.1 * c.1.2 : ℕ) : ℝ) := by
    intro c hc
    exact fixedD_level_lower hd z D hD c (Finset.mem_filter.mp hc).1
  have hgeom : 0 ≤ subsetGeometryFactor d (d.Q1 * D) l := by
    unfold subsetGeometryFactor
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hlog := logBudget_nonneg (physicalCap d)
    positivity
  have hbudget : 0 ≤ progressionLogBudget hShiu d l := by
    unfold progressionLogBudget
    have hA := hShiu.A_pos.le
    have hE := (uniformEulerConstant_pos 1).le
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 8 * d.scale by linarith)
    positivity
  have hreturn : ‖fixedDModulusPacket d z D l‖ ≤
      progressionLogBudget hShiu d l * subsetGeometryFactor d (d.Q1 * D) l := by
    by_cases hz : fixedDModulusPacket d z D l = 0
    · rw [hz, norm_zero]
      exact mul_nonneg hbudget hgeom
    · have hcop := nonzero_subsetPacket_coprime hd z S hS l hmodS hz
      have hX0 : hShiu.X0 ≤ (firstWindowScale d : ℝ) := by
        have hK := (firstWindowScale_bounds d hx).1
        linarith
      have hmodR : (l : ℝ) ≤ d.scale ^ ((4 : ℝ) / 5) :=
        (show (l : ℝ) ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) by
          exact_mod_cast hmod).trans
            (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ d.scale) _))
      exact (subsetPacket_norm_le_geometry hd z (d.Q1 * D) hY S hS l hl hmodS hlevel).trans
        (mul_le_mul_of_nonneg_right
          (psiDivisorProgression_le_logBudget hd hx hShiu l hl hcop hX0
            (physical_modulus_shiu_margin d hx hlarge l hmodR)) hgeom)
  calc
    _ ≤ progressionLogBudget hShiu d l * subsetGeometryFactor d (d.Q1 * D) l := hreturn
    _ = _ := by
      unfold progressionLogBudget subsetGeometryFactor wholeLogFactor fixedDScale
        MediumAtom.scale ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean.tauR
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem fixedDTail_le_collapsed_arithmetic
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale)
    (hthreshold : 3 * hShiu.X0 ≤ d.scale) (z D : ℝ) (hD : 0 < D)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    ‖fixedDTail d z D‖ ≤
      (wholeLogFactor hShiu d * fixedDScale d D) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5))) d.scale z := by
  rw [fixedDTail_eq_collapsed_packets hd z D hphysical]
  calc
    _ ≤ ∑ l ∈ collapsedModuli d z, ‖fixedDModulusPacket d z D l‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ collapsedModuli d z,
        (wholeLogFactor hShiu d * fixedDScale d D) *
          ((l.divisors.card : ℝ) ^ 5 / (l : ℝ)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hli := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
      exact fixedDModulusPacket_return hd hShiu hx hlarge hthreshold z D hD l hli.1 hli.2
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- The same A-before-threshold order is uniform over ALL positive D.
This is V(D) saving on a complete d~D family, not a per-exact-d assertion. -/
theorem exists_fixedDTail_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (D : ℝ),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale → 0 < D →
        physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        ‖fixedDTail d (roughZ d.scale) D‖ ≤
          C * (fixedDScale d D * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Xpay, hXpay, hpay⟩ :=
    exists_collapsed_smooth_tail_arbitrary_log 5 (A + 6) (by linarith)
  let X := max Xpay (max (3 * hShiu.X0)
    (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)))
  refine ⟨finalConstant hShiu, X, finalConstant_pos hShiu,
    hXpay.trans_le (le_max_left _ _), ?_⟩
  intro B sigma kappa c0 d D hd hXd hD hphysical
  have hxpay : Xpay ≤ d.scale := (le_max_left _ _).trans hXd
  have hrest : max (3 * hShiu.X0)
      (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)) ≤ d.scale :=
    (le_max_right _ _).trans hXd
  have hthreshold : 3 * hShiu.X0 ≤ d.scale := (le_max_left _ _).trans hrest
  have hother : max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1) ≤ d.scale :=
    (le_max_right _ _).trans hrest
  have hlarge0 : (3 : ℝ) ^ (9 : ℕ) + 1 ≤ d.scale := (le_max_left _ _).trans hother
  have hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale := by linarith
  have hx : 6 ≤ d.scale := by norm_num at hlarge0; linarith
  have hexp : Real.exp 1 + 1 ≤ d.scale := (le_max_right _ _).trans hother
  have hlog : 1 ≤ Real.log d.scale := by
    have he := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ d.scale by linarith)
    simpa only [Real.log_exp] using he
  have hLpos : 0 < Real.log d.scale := by linarith
  have htail := hpay d.scale hxpay
  have htail0 : 0 ≤ collapsedSmoothTail 5
      (Nat.floor (d.scale ^ ((4 : ℝ) / 5))) d.scale (roughZ d.scale) := by
    unfold collapsedSmoothTail
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hV : 0 ≤ fixedDScale d D := by
    unfold fixedDScale
    have hM : 0 ≤ d.V := by linarith [hd.2.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hC := (finalConstant_pos hShiu).le
  have hlogs := wholeLogFactor_le_six_logs hd hShiu hx hlog hphysical
  have hpow : Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6)) =
      Real.log d.scale ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ (wholeLogFactor hShiu d * fixedDScale d D) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5)))
          d.scale (roughZ d.scale) :=
      fixedDTail_le_collapsed_arithmetic hd hShiu hx hlarge hthreshold
        (roughZ d.scale) D hD hphysical
    _ ≤ (finalConstant hShiu * Real.log d.scale ^ 6 * fixedDScale d D) *
        Real.log d.scale ^ (-(A + 6)) := by
          gcongr <;> first | exact hlogs | exact htail | positivity
    _ = finalConstant hShiu * (fixedDScale d D * (Real.log d.scale) ^ (-A)) := by
      calc
        _ = (finalConstant hShiu * fixedDScale d D) *
            (Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6))) := by ring
        _ = _ := by rw [hpow]; ring

/-- Direct actual-source deletion statement, rather than only a bound
on a separately named tail. The same one d~D family contains all mixed bins. -/
theorem exists_actualFixedDS2_deletion_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (D : ℝ),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale → 0 < D →
        physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        ‖fixedDActualCoefficientSum d (roughZ d.scale) D
            (Lambda d (roughZ d.scale)) (Lambda d (roughZ d.scale)) -
          fixedDActualCoefficientSum d (roughZ d.scale) D
            (lambdaSmoothKept d d.scale (roughZ d.scale))
            (lambdaSmoothKept d d.scale (roughZ d.scale))‖ ≤
          C * (fixedDScale d D * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hbound⟩ := exists_fixedDTail_arbitrary_log hShiu A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma kappa c0 d D hd hx hD hphysical
  rw [fixedDActualS2_eq_kept_add_tail]
  simpa only [add_sub_cancel_left] using hbound B sigma kappa c0 d D hd hx hD hphysical

def fixedDMixedBank (d : MediumAtom) (z D : ℝ) : Finset MixedKey :=
  (fixedDFamily d z D).image mixedOwner

def fixedDMixedOwnedTail (d : MediumAtom) (z D : ℝ) (key : MixedKey) : ℂ :=
  ∑ c ∈ (fixedDFamily d z D).filter (fun c => mixedOwner c = key),
    psiThreeTailInner d d.scale z c

/-- Every mixed rough pair is retained in the ONE d~D preliminary family. -/
theorem fixedDTail_eq_all_mixed_owners (d : MediumAtom) (z D : ℝ) :
    fixedDTail d z D =
      ∑ key ∈ fixedDMixedBank d z D, fixedDMixedOwnedTail d z D key := by
  have hmap : ∀ c ∈ fixedDFamily d z D, mixedOwner c ∈ fixedDMixedBank d z D :=
    fun c hc => Finset.mem_image_of_mem _ hc
  have h := Finset.sum_fiberwise_of_maps_to'
    (s := fixedDFamily d z D) (t := fixedDMixedBank d z D) (g := mixedOwner)
    hmap (fun c => psiThreeTailInner d d.scale z c)
  exact h.symm

end
end ImbalancedChen.Part3OriginalS2FixedDMixedTail
