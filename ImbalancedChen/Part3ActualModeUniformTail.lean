import ImbalancedChen.Part3ActualFamilyScaleBudget
import ImbalancedChen.Part3ActualModeSmoothMassTail

/-!
# Uniform power saving for the original actual-mode common-m tail

The genuine physical scales and the choice Z = x^eta are substituted into
the accepted six-piece tail. The polynomial label budget is proved from
MediumAdmissible, not assumed. A single derivative order and positive constant
are chosen before every varying atom, block label and Fourier mode.

This is a bound for each actual mode with its actual block cutoff. It does not
sum the outer Fourier coefficients or reconstruct the original supported row.
The physical y=0 source and the completed m=0 lane keep their separate roles.
-/

namespace ImbalancedChen.Part3.ActualModeUniformTail20261127

noncomputable section
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualCompletedHardTailMass20261026b
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualModeBetaPositiveCountSourceOnly
open ActualModeCommonPoissonLanes20261126 ActualSmoothMassTruncation20261127
open ActualModeSmoothMassTail20261127 ActualFamilyScaleBudget20261127

/-- The order is chosen using only the fixed exponents, before the atom or mode. -/
theorem exists_fixed_tail_order {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (eta L : ℝ) :
    ∃ r : ℕ, 2 ≤ r ∧ 19 + 2 * eta + L ≤ epsilon * ((r - 1 : ℕ) : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) ((19 + 2 * eta + L) / epsilon))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hnNat : 1 ≤ n := by exact_mod_cast hn1.le
  have hnq : (19 + 2 * eta + L) / epsilon < n := (le_max_right _ _).trans_lt hn
  refine ⟨n + 1, by omega, ?_⟩
  simp only [Nat.add_sub_cancel]
  have hmul := (div_lt_iff₀ hepsilon).mp hnq
  linarith

/-- A chosen order pays the actual polynomial budget in every positive block.
All analytic constants precede the varying admissible atom and mode. -/
theorem actualMode_sixSmoothMass_actualScale_power_tail
    (epsilon eta L : ℝ) (heta : 0 < eta) (r : ℕ) (hr : 2 ≤ r)
    (horder : 19 + 2 * eta + L ≤ epsilon * ((r - 1 : ℕ) : ℝ)) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
        0 < sigma → MediumAdmissible b sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g * l)],
        0 < D → 0 < delta → 0 < g → 0 < l →
      ∀ (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)),
        let B := scaleB e delta l
        let C := scaleC e D g l
        let Z := e.scale ^ eta
        let lam := actualModeLambda e D delta g l mode negative u k
        let om := actualModeOmega e D g l Z tag mode negative k
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue negative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lam om) : ℂ) -
          actualTruncatedSix e D delta g l Z negative lam om
            (Nat.ceil ((C / B) * e.scale ^ epsilon)) B C‖ ≤
          K * e.scale ^ (-L) := by
  obtain ⟨A, hA, htail⟩ := actualMode_sixSmoothMass_common_hard_tail_xepsilon r hr
  let K : ℝ := 6 * A * 10 ^ (r - 1) * 202800
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro b sigma kappa c0 e hsigma he D delta g l inst hD hdelta hg hl tag mode negative u k
  let : NeZero (g * l) := inst
  have hx : 1 ≤ e.scale := TransposedPrimitiveUPayment.one_le_scale he
  have hxpos : 0 < e.scale := zero_lt_one.trans_le hx
  have hB : 0 < scaleB e delta l := scaleB_pos he hl hdelta
  have hC : 0 < scaleC e D g l := scaleC_pos he hD hg hl
  have h := htail (scaleB e delta l) hB (scaleC e D g l) hC
    e.scale hxpos epsilon b sigma kappa c0 e he D delta g l (e.scale ^ eta)
    tag mode negative u k
  have hbudget := actual_scaleC_sq_rawLabelBudget_le he hsigma D delta g l eta heta
  dsimp only at h ⊢
  have hcoef : 0 ≤ (6 * A * 10 ^ (r - 1) : ℝ) := by positivity
  have hpower : 0 ≤ e.scale ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) :=
    (Real.rpow_pos_of_pos hxpos _).le
  calc
    _ ≤ (6 * A * 10 ^ (r - 1) * scaleC e D g l ^ 2) *
          rawLabelBudget (baseCarrier e (D / delta))
            (e.sharedSmoothFrequencyBound (e.scale ^ eta) D) (scaleF e D g) *
          e.scale ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) := h
    _ = (6 * A * 10 ^ (r - 1)) *
          (scaleC e D g l ^ 2 * rawLabelBudget (baseCarrier e (D / delta))
            (e.sharedSmoothFrequencyBound (e.scale ^ eta) D) (scaleF e D g)) *
          e.scale ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) := by ring
    _ ≤ (6 * A * 10 ^ (r - 1)) * (202800 * e.scale ^ (19 + 2 * eta)) *
          e.scale ^ (-(epsilon * ((r - 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hcoef) hpower
    _ = K * e.scale ^ ((19 + 2 * eta) - epsilon * ((r - 1 : ℕ) : ℝ)) := by
      rw [sub_eq_add_neg,
        Real.rpow_add hxpos (19 + 2 * eta) (-(epsilon * ((r - 1 : ℕ) : ℝ)))]
      dsimp [K]
      ring
    _ ≤ K * e.scale ^ (-L) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      exact Real.rpow_le_rpow_of_exponent_le hx (by linarith [horder])

/-- Every prescribed power saving has one order and constant valid for all
admissible atoms, actual positive blocks, finite labels and individual modes. -/
theorem actualMode_sixSmoothMass_uniform_power_tail
    (epsilon eta L : ℝ) (hepsilon : 0 < epsilon) (heta : 0 < eta) :
    ∃ r : ℕ, 2 ≤ r ∧ 19 + 2 * eta + L ≤ epsilon * ((r - 1 : ℕ) : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
      ∀ (b : ℕ) (sigma kappa c0 : ℝ) (e : MediumAtom),
        0 < sigma → MediumAdmissible b sigma kappa c0 e →
      ∀ (D delta g l : ℕ) [NeZero (g * l)],
        0 < D → 0 < delta → 0 < g → 0 < l →
      ∀ (tag : ℕ × Bool) (mode : ℤ × ℤ) (negative : Bool)
        (u : (ZMod (g * l))ˣ) (k : ZMod (g * l)),
        let B := scaleB e delta l
        let C := scaleC e D g l
        let Z := e.scale ^ eta
        let lam := actualModeLambda e D delta g l mode negative u k
        let om := actualModeOmega e D g l Z tag mode negative k
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue negative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lam om) : ℂ) -
          actualTruncatedSix e D delta g l Z negative lam om
            (Nat.ceil ((C / B) * e.scale ^ epsilon)) B C‖ ≤
          K * e.scale ^ (-L) := by
  obtain ⟨r, hr, horder⟩ := exists_fixed_tail_order hepsilon eta L
  exact ⟨r, hr, horder,
    actualMode_sixSmoothMass_actualScale_power_tail epsilon eta L heta r hr horder⟩

end

end ImbalancedChen.Part3.ActualModeUniformTail20261127
