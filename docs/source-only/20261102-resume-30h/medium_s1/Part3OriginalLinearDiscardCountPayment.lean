import ImbalancedChen.Part3OriginalLinearDiscardSmoothSupport
import ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
import ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Pay manuscript (8) for the original preliminary LINEAR deleted count
and unchanged coprime mean in the manuscript's initial one-bounded-beta
case B=0. The physical coefficient is not the quadratic S2 tail. The
general B normalization and every unestimated S2/S3 packet remain open.
-/

namespace ImbalancedChen.Part3.OriginalLinearDiscardCountPayment20261102
noncomputable section
open Classical Finset Filter Topology
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumActualPostSquareDeletion20261028
open MediumActualPsiPreliminaryDispersion20261028 MediumReceiverCutoffArithmetic20261028
open OriginalLinearDiscardModulusBinding20261028 OriginalLinearDiscardSmoothSupport20261102
open OriginalS1OuterCauchy20261028
open ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2ShiuPrimitiveFiber
open ImbalancedChen.Part3OriginalS2SameGevreyPacket
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedDivisorMoment
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open MediumPrimitiveShiuWindow20261028 MediumPrimitiveShiuEuler20261028

/-- The independent physical Cartesian source before taking any norm. -/
def originalMNCarrier (atom : MediumAtom) : Finset (ℕ × ℕ) :=
  atom.alphaCarrier ×ˢ atom.betaCarrier

theorem originalMNCarrier_subset_psiMNCarrier
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) :
    originalMNCarrier atom ⊆ psiMNCarrier atom := by
  intro nm hnm
  obtain ⟨hn, hm⟩ := mem_product.mp hnm
  have hmFactor : nm.2 ∈ factorCarrier atom.V := hm
  have hψ : actualPsiMWeight atom nm.2 = 1 :=
    actualPsi_eq_one_on_factorCarrier (zero_lt_one.trans_le hA.2.1) hmFactor
  have hψne : actualPsiMWeight atom nm.2 ≠ 0 := by rw [hψ]; norm_num
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨hn, (actualPsiMWeight_support hA nm.2 hψne).2.2⟩, hψne⟩

/-- The physical product fibre is injected into the original divisors;
the old actual paperPsi carrier is used only as a positive enlargement. -/
theorem original_product_count_le_psiDivisorProgression
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) (ell : ℕ) :
    (∑ nm ∈ originalMNCarrier atom,
      if Int.ModEq ell (((nm.1 * nm.2 : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0) ≤
        psiDivisorProgression atom ell := by
  have hmap : ∀ nm ∈ originalMNCarrier atom, nm.1 * nm.2 ∈ psiMNImage atom := by
    intro nm hnm
    exact mem_image_of_mem _ (originalMNCarrier_subset_psiMNCarrier atom hA hnm)
  have hf := sum_fiberwise_of_maps_to (s := originalMNCarrier atom)
    (t := psiMNImage atom) (g := fun nm : ℕ × ℕ => nm.1 * nm.2) hmap
    (fun nm => if Int.ModEq ell (((nm.1 * nm.2 : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0)
  rw [← hf]
  unfold psiDivisorProgression
  apply sum_le_sum
  intro v hv
  have hvpos := (psiMNImage_physical_interval hA hv).2.2
  have hsub : (originalMNCarrier atom).filter (fun nm => nm.1 * nm.2 = v) ⊆
      (mnCarrier atom).filter (fun nm => nm.1 * nm.2 = v) := by
    intro nm hnm
    have hψ := originalMNCarrier_subset_psiMNCarrier atom hA (mem_filter.mp hnm).1
    exact mem_filter.mpr ⟨(mem_filter.mp hψ).1, (mem_filter.mp hnm).2⟩
  have hcard := (card_le_card hsub).trans (mn_fiber_card_le_tau atom v hvpos)
  calc
    _ = ∑ _nm ∈ (originalMNCarrier atom).filter (fun nm => nm.1 * nm.2 = v),
        if Int.ModEq ell (v : ℤ) atom.residue then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro nm hnm
      rw [(mem_filter.mp hnm).2]
    _ ≤ _ := by
      by_cases hmod : Int.ModEq ell (v : ℤ) atom.residue
      · simp only [if_pos hmod, sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hcard
      · simp [hmod]

private theorem physicalDeletedKernel_norm_le_count_add_mean (atom : MediumAtom)
    (ell n m : ℕ) :
    ‖physicalDeletedKernel atom n ((ell, 1, 1), m)‖ ≤
      (if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0) +
        1 / (ell.totient : ℝ) := by
  have hd : ‖deletedCongruence atom n ((ell, 1, 1), m)‖ ≤
      if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0 := by
    by_cases he : ((n * m : ℕ) : ℤ) = atom.residue
    · simp only [deletedCongruence, if_pos he, norm_zero]
      split_ifs <;> norm_num
    · simp only [deletedCongruence, if_neg he, fullCongruence,
        complexFactorModulus, mul_one]
      change ‖(if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℂ) else 0)‖ ≤ _
      split_ifs <;> norm_num
  have hm : ‖physicalMeanKernel atom n ((ell, 1, 1), m)‖ ≤ 1 / (ell.totient : ℝ) := by
    simp only [physicalMeanKernel, complexFactorModulus, mul_one, norm_div,
      Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    split_ifs <;> norm_num
  exact (norm_sub_le _ _).trans (add_le_add hd hm)

/-- Real count and unchanged coprime mean of the actual deleted source.
Only the initial B=0 branch is claimed, precisely as in manuscript 124. -/
theorem original_deletedModulusDiscrepancy_le_count_add_mean
    {σ κ c0 : ℝ} (atom : MediumAtom) (hA : MediumAdmissible 0 σ κ c0 atom)
    (ell : ℕ) :
    ‖deletedModulusDiscrepancy atom ell‖ ≤ psiDivisorProgression atom ell +
      9 * atom.scale / (ell.totient : ℝ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hα, _, hβ, _⟩ := hA
  have hαcard : (atom.alphaCarrier.card : ℝ) ≤ 3 * atom.U :=
    (by exact_mod_cast card_le_card (show atom.alphaCarrier ⊆ factorCarrier atom.U
      from filter_subset _ _)).trans (factorCarrier_card_le_three hA.1)
  have hβcard : (atom.betaCarrier.card : ℝ) ≤ 3 * atom.V :=
    factorCarrier_card_le_three hA.2.1
  have hcard : (atom.alphaCarrier.card : ℝ) * atom.betaCarrier.card ≤ 9 * atom.scale := by
    calc
      _ ≤ (3 * atom.U) * (3 * atom.V) :=
        mul_le_mul hαcard hβcard (Nat.cast_nonneg _) (by linarith [hA.1])
      _ = _ := by unfold MediumAtom.scale; ring
  calc
    _ ≤ ∑ n ∈ atom.alphaCarrier, ∑ m ∈ atom.betaCarrier,
        ‖atom.alpha n * atom.beta m * physicalDeletedKernel atom n ((ell, 1, 1), m)‖ := by
      apply (norm_sum_le _ _).trans
      exact sum_le_sum (fun n hn => norm_sum_le _ _)
    _ ≤ ∑ n ∈ atom.alphaCarrier, ∑ m ∈ atom.betaCarrier,
        ((if Int.ModEq ell (((n * m : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0) +
          1 / (ell.totient : ℝ)) := by
      apply sum_le_sum
      intro n hn
      apply sum_le_sum
      intro m hm
      have hb : ‖atom.beta m‖ ≤ 1 := by simpa only [pow_zero] using hβ m hm
      have hab : ‖atom.alpha n‖ * ‖atom.beta m‖ ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (hα n hn) hb (norm_nonneg _) zero_le_one
      rw [norm_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_right hab (norm_nonneg _)).trans
        (by simpa only [one_mul] using physicalDeletedKernel_norm_le_count_add_mean atom ell n m)
    _ = (∑ nm ∈ originalMNCarrier atom,
        if Int.ModEq ell (((nm.1 * nm.2 : ℕ) : ℤ)) atom.residue then (1 : ℝ) else 0) +
          ((atom.alphaCarrier.card : ℝ) * atom.betaCarrier.card) / (ell.totient : ℝ) := by
      simp only [originalMNCarrier, sum_product, sum_add_distrib, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := add_le_add (original_product_count_le_psiDivisorProgression atom hA ell)
      (div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _))

def linearDiscardLogFactor
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (atom : MediumAtom) : ℝ :=
  ((15 / 2 : ℝ) * hShiu.A * uniformEulerConstant 1) * Real.log (8 * atom.scale) + 9

theorem linearDiscardLogFactor_nonneg
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (atom : MediumAtom) (hx : 1 ≤ atom.scale) : 0 ≤ linearDiscardLogFactor hShiu atom := by
  have hA := hShiu.A_pos.le
  have hE := (uniformEulerConstant_pos 1).le
  have hlog : 0 ≤ Real.log (8 * atom.scale) := Real.log_nonneg (by linarith)
  unfold linearDiscardLogFactor
  positivity

theorem original_deletedModulusDiscrepancy_primitive_return
    {σ κ c0 : ℝ} (atom : MediumAtom) (hA : MediumAdmissible 0 σ κ c0 atom)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ atom.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < atom.scale)
    (hthreshold : 3 * hShiu.X0 ≤ atom.scale)
    (ell : ℕ) (hell : 0 < ell) (hcop : ell.Coprime atom.residue.natAbs)
    (hmod : ell ≤ Nat.floor (atom.scale ^ ((4 : ℝ) / 5))) :
    ‖deletedModulusDiscrepancy atom ell‖ ≤
      (linearDiscardLogFactor hShiu atom * atom.scale) *
        ((ell.divisors.card : ℝ) / (ell : ℝ)) := by
  have hX0 : hShiu.X0 ≤ (firstWindowScale atom : ℝ) := by
    have hK := (firstWindowScale_bounds atom hx).1
    linarith
  have hmodR : (ell : ℝ) ≤ atom.scale ^ ((4 : ℝ) / 5) :=
    (show (ell : ℝ) ≤ (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)) : ℝ) by exact_mod_cast hmod).trans
      (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ atom.scale) _))
  have hp := psiDivisorProgression_le_logBudget hA hx hShiu ell hell hcop hX0
    (physical_modulus_shiu_margin atom hx hlarge ell hmodR)
  have hphi : (0 : ℝ) < ell.totient := by exact_mod_cast Nat.totient_pos.mpr hell
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hratio := totient_ratio_le_divisor_count ell hell
  have hrec : (1 : ℝ) / ell.totient ≤ (ell.divisors.card : ℝ) / ell := by
    apply (div_le_div_iff₀ hphi hellR).mpr
    simpa only [one_mul] using (div_le_iff₀ hphi).mp hratio
  calc
    _ ≤ psiDivisorProgression atom ell + 9 * atom.scale / (ell.totient : ℝ) :=
      original_deletedModulusDiscrepancy_le_count_add_mean atom hA ell
    _ ≤ progressionLogBudget hShiu atom ell +
        (9 * atom.scale) * ((ell.divisors.card : ℝ) / ell) := by
      apply add_le_add hp
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrec (by linarith : 0 ≤ 9 * atom.scale)
    _ = _ := by unfold progressionLogBudget linearDiscardLogFactor; ring

/-- Actual count-plus-mean payment reaches the existing original (8)
tail, preserving its full modulus and the ordered gamma multiplicity. -/
theorem original_linear_discard_le_collapsed_arithmetic
    {σ κ c0 : ℝ} (atom : MediumAtom) (hA : MediumAdmissible 0 σ κ c0 atom)
    (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ atom.scale) (hlarge : (3 : ℝ) ^ (9 : ℕ) < atom.scale)
    (hthreshold : 3 * hShiu.X0 ≤ atom.scale)
    (hphysical : (10 : ℝ) ^ (10 : ℕ) ≤ atom.scale) (z : ℝ) (hz : 0 ≤ z) :
    ‖discardedSource atom (strictReceiverCutoff z) (roughY atom.scale)‖ ≤
      (linearDiscardLogFactor hShiu atom * atom.scale) *
        collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5))) atom.scale z := by
  let γ := discardedFactorGamma atom (strictReceiverCutoff z) (roughY atom.scale)
  let S := atom.physicalFactorModuli.filter (fun ell => γ ell ≠ 0)
  let T := (Icc 1 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))).filter
    (fun ell => roughY atom.scale < (zSmoothPart z ell : ℝ))
  have hsub : S ⊆ T := by
    intro ell hell
    exact actual_linear_discard_modulus_mem_collapsed_filter atom hA hσ hc0 hphysical z hz
      (mem_filter.mp hell).1 (mem_filter.mp hell).2
  have hscale : 0 ≤ linearDiscardLogFactor hShiu atom * atom.scale :=
    mul_nonneg (linearDiscardLogFactor_nonneg hShiu atom (by linarith)) (by linarith)
  rw [discardedSource_eq_actual_modulus_fibres]
  calc
    _ ≤ ∑ ell ∈ atom.physicalFactorModuli, ‖γ ell‖ * ‖deletedModulusDiscrepancy atom ell‖ := by
      simpa only [norm_mul] using norm_sum_le
        (s := atom.physicalFactorModuli) (f := fun ell => γ ell * deletedModulusDiscrepancy atom ell)
    _ = ∑ ell ∈ S, ‖γ ell‖ * ‖deletedModulusDiscrepancy atom ell‖ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro ell hell
      by_cases hγ : γ ell = 0 <;> simp [hγ]
    _ ≤ ∑ ell ∈ S, (linearDiscardLogFactor hShiu atom * atom.scale) *
        ((ell.divisors.card : ℝ) ^ 4 / (ell : ℝ)) := by
      apply sum_le_sum
      intro ell hell
      have hT := mem_Icc.mp (mem_filter.mp (hsub hell)).1
      have hcop := discardedFactorGamma_support_primitive atom hA _ _ ell (mem_filter.mp hell).2
      have hg := discardedFactorGamma_norm_le_tau_cube atom hA _ _ ell hT.1
      have hd := original_deletedModulusDiscrepancy_primitive_return atom hA hShiu hx hlarge
        hthreshold ell hT.1 hcop hT.2
      calc
        _ ≤ (ell.divisors.card : ℝ) ^ 3 *
            ((linearDiscardLogFactor hShiu atom * atom.scale) * ((ell.divisors.card : ℝ) / ell)) :=
          mul_le_mul hg hd (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (linearDiscardLogFactor hShiu atom * atom.scale) *
        ∑ ell ∈ S, (ell.divisors.card : ℝ) ^ 4 / (ell : ℝ) := by rw [mul_sum]
    _ ≤ (linearDiscardLogFactor hShiu atom * atom.scale) *
        ∑ ell ∈ T, (ell.divisors.card : ℝ) ^ 4 / (ell : ℝ) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)) hscale
    _ = _ := rfl

def linearDiscardConstant
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ)) : ℝ :=
  8 * ((15 / 2 : ℝ) * hShiu.A * uniformEulerConstant 1) + 9

/-- One threshold BEFORE all atoms and moving residues pays the genuine
preliminary linear discard in the original one-bounded-beta branch. -/
theorem original_one_bounded_linear_discard_log_payment
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 < X ∧
      ∀ (σ κ c0 : ℝ) (atom : MediumAtom), MediumAdmissible 0 σ κ c0 atom →
        0 ≤ σ → 0 < c0 → X ≤ atom.scale →
          ‖discardedSource atom (strictReceiverCutoff (roughZ atom.scale)) (roughY atom.scale)‖ ≤
            C * atom.scale / Real.log atom.scale ^ A := by
  obtain ⟨Xp, hXp, hpay⟩ := exists_collapsed_smooth_tail_arbitrary_log 4 (A + 1) (by linarith)
  let C := linearDiscardConstant hShiu
  have hC : 0 < C := by
    have := hShiu.A_pos
    have := uniformEulerConstant_pos 1
    dsimp [C, linearDiscardConstant]
    positivity
  let X := max Xp (max (3 * hShiu.X0)
    (max ((3 : ℝ) ^ (9 : ℕ) + 1) (max ((10 : ℝ) ^ (10 : ℕ)) (Real.exp 1 + 1))))
  have hXp1 : 1 < Xp := (Real.one_lt_exp.mpr (Real.exp_pos 1)).trans hXp
  refine ⟨C, hC, X, hXp1.trans_le (le_max_left _ _), ?_⟩
  intro σ κ c0 atom hadm hσ hc0 hx
  have hxp : Xp ≤ atom.scale := (le_max_left _ _).trans hx
  have hrest := (le_max_right _ _).trans hx
  have hthreshold : 3 * hShiu.X0 ≤ atom.scale := (le_max_left _ _).trans hrest
  have hlarge0 : (3 : ℝ) ^ (9 : ℕ) + 1 ≤ atom.scale :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hphysical : (10 : ℝ) ^ (10 : ℕ) ≤ atom.scale :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hexp : Real.exp 1 + 1 ≤ atom.scale :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hrest))
  have hx6 : 6 ≤ atom.scale := by norm_num at hlarge0; linarith
  have hxpos : 0 < atom.scale := by linarith
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ atom.scale by linarith)
  have hlogpos : 0 < Real.log atom.scale := by linarith
  have h8 : Real.log (8 * atom.scale) ≤ 8 * Real.log atom.scale := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hxpos.ne']
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hfactor : linearDiscardLogFactor hShiu atom ≤ C * Real.log atom.scale := by
    have hcount : 0 ≤ (15 / 2 : ℝ) * hShiu.A * uniformEulerConstant 1 :=
      mul_nonneg (mul_nonneg (by norm_num) hShiu.A_pos.le) (uniformEulerConstant_pos 1).le
    have h := mul_le_mul_of_nonneg_left h8 hcount
    dsimp [linearDiscardLogFactor, C, linearDiscardConstant]
    nlinarith
  have htail := hpay atom.scale hxp
  have htail0 : 0 ≤ collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))
      atom.scale (roughZ atom.scale) := by
    unfold collapsedSmoothTail
    exact sum_nonneg (fun _ _ => by positivity)
  have hpow : Real.log atom.scale * Real.log atom.scale ^ (-(A + 1)) =
      1 / Real.log atom.scale ^ A := by
    calc
      _ = Real.log atom.scale ^ (1 : ℝ) * Real.log atom.scale ^ (-(A + 1)) := by
        rw [Real.rpow_one]
      _ = Real.log atom.scale ^ (-A) := by
        rw [← Real.rpow_add hlogpos]
        congr 1
        ring
      _ = _ := by rw [Real.rpow_neg hlogpos.le, one_div]
  calc
    _ ≤ (linearDiscardLogFactor hShiu atom * atom.scale) *
        collapsedSmoothTail 4 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))
          atom.scale (roughZ atom.scale) :=
      original_linear_discard_le_collapsed_arithmetic atom hadm hσ hc0 hShiu hx6
        (by linarith) hthreshold hphysical _ (Real.rpow_nonneg hxpos.le _)
    _ ≤ (C * Real.log atom.scale * atom.scale) * Real.log atom.scale ^ (-(A + 1)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hfactor hxpos.le) htail htail0 (by positivity)
    _ = _ := by
      calc
        _ = (C * atom.scale) *
            (Real.log atom.scale * Real.log atom.scale ^ (-(A + 1))) := by ring
        _ = _ := by rw [hpow]; ring

end
end ImbalancedChen.Part3.OriginalLinearDiscardCountPayment20261102
