import ImbalancedChen.Part3ActualSpectralMonomialMargins
import ImbalancedChen.Part3TransposedPrimitiveUPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
One uniform threshold supplies the ACTUAL short-frequency counting
geometry and zero-Poisson absorption gate. The original smooth trim,
preliminary D and log^5 loss are paid from their proved definitions.
No coefficient-norm, spectral-return or bare estimate is assumed.
-/

namespace ImbalancedChen.Part3.ActualSpectralUniformGeometry20261028
noncomputable section
open Classical Filter Topology
open MediumGlobalDyadicOwnership20261028 MediumReceiverCutoffArithmetic20261028
open ActualMediumVarianceAtomBindingSourceOnly OriginalSamePsiS1OwnedAtlas
open OriginalLambdaTrimPoissonFamily20261028 ActualOriginalSpectralScales20261028
open ActualSpectralMonomialMargins20261028

/-- This is the manuscript's original occupied-source short H/S and
Bspec^2<x regime, with constants fixed before all atoms and receivers. -/
theorem exists_actual_spectral_geometry_threshold (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
        D0 atom k < 1 ∧ (spectralB atom k)^2 < atom.scale ∧
          keyRealH atom k/roughS k ≤ atom.scale^(-8*sigma) ∧
            1+keyRealH atom k/roughS k ≤ 2 := by
  obtain ⟨x1,hx1,hmargin⟩ := exists_actual_margin_threshold hsigma
  obtain ⟨x2,hpay⟩ := eventually_atTop.mp
    (TransposedPrimitiveUPayment.eventually_const_log_rpow_le_rpow 128 5
      (by norm_num) (by linarith : 0 < sigma/2))
  refine ⟨max x1 x2,hx1.trans_le (le_max_left _ _),?_⟩
  intro B kappa c0 atom hA hx z k hk
  have hx1' : x1 ≤ atom.scale := (le_max_left _ _).trans hx
  have hx2' : x2 ≤ atom.scale := (le_max_right _ _).trans hx
  obtain ⟨hX,hll,h8⟩ := hmargin atom.scale hx1'
  have hx0 : 0 < atom.scale := zero_lt_one.trans_le hX
  have hN : 0 < atom.U := lt_of_lt_of_le zero_lt_one hA.1
  have hD0 : 0 ≤ keyD k := by dsimp [keyD]; positivity
  have hlog0 : 0 ≤ (Real.log atom.scale)^5 := pow_nonneg (Real.log_nonneg hX) _
  have hlogpay : 128*(Real.log atom.scale)^5 ≤ atom.scale^(sigma/2) := by
    simpa only [Real.rpow_natCast] using hpay atom.scale hx2'
  have hD : keyD k ≤ atom.scale^(sigma/2) :=
    (occupied_keyD_le_trim_square (Real.rpow_nonneg hx0.le _) hk).trans
      (originalTrim_square_le hX hsigma hll)
  have hDlog : 128*keyD k*(Real.log atom.scale)^5 ≤ atom.scale^sigma := by
    calc
      _ = keyD k*(128*(Real.log atom.scale)^5) := by ring
      _ ≤ atom.scale^(sigma/2)*atom.scale^(sigma/2) :=
        mul_le_mul hD hlogpay (by positivity) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
  obtain ⟨hg0,hg1,hg2⟩ := actual_D0_D1_D2_margins hA
    (strictReceiverCutoff z) (originalSmoothTrim atom) k hk
  have h8big : 8 ≤ atom.scale^(8*sigma) := h8.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by linarith))
  have hmul8 : 8*atom.scale^(-8*sigma) ≤ 1 := by
    calc
      _ ≤ atom.scale^(8*sigma)*atom.scale^(-8*sigma) :=
        mul_le_mul_of_nonneg_right h8big (Real.rpow_nonneg hx0.le _)
      _ = 1 := by
        rw [← Real.rpow_add hx0,show (8*sigma)+(-8*sigma) = 0 by ring,
          Real.rpow_zero]
  have hB := actual_spectralB_sq_margin hA
    (strictReceiverCutoff z) (originalSmoothTrim atom) k hk
  have hBfull : (spectralB atom k)^2 < atom.scale := by
    refine hB.trans_le ?_
    calc
      _ ≤ atom.scale^(8*sigma)*atom.scale^(1-8*sigma) :=
        mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ atom.scale^(8*sigma))
          (Real.rpow_nonneg hx0.le _)
      _ = atom.scale := by
        rw [← Real.rpow_add hx0,show (8*sigma)+(1-8*sigma) = 1 by ring,
          Real.rpow_one]
  have hQ : 0 ≤ atom.Q1/atom.U := div_nonneg (zero_le_one.trans hA.2.2.1) hN.le
  have hQcap : atom.Q1/atom.U ≤ atom.scale^(-sigma) := by
    apply (div_le_iff₀ hN).mpr
    convert hA.2.2.2.2.2.2.2.2.1.le using 1 <;> ring
  have hshort := actual_keyH_short_ratio hA
    (strictReceiverCutoff z) (originalSmoothTrim atom) k hk
  have hD0nonneg : 0 ≤ D0 atom k := by dsimp [D0]; positivity
  have hH : keyRealH atom k/roughS k ≤ atom.scale^(-8*sigma) := by
    calc
      _ ≤ (16*keyD k*(Real.log atom.scale)^5)*(atom.Q1/atom.U)*D0 atom k := hshort
      _ ≤ (16*keyD k*(Real.log atom.scale)^5)*atom.scale^(-sigma)*
          (8*atom.scale^(-8*sigma)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQcap (by positivity)) hg0.le
          hD0nonneg (by positivity)
      _ = (128*keyD k*(Real.log atom.scale)^5)*
          (atom.scale^(-sigma)*atom.scale^(-8*sigma)) := by ring
      _ = (128*keyD k*(Real.log atom.scale)^5)*atom.scale^(-9*sigma) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      _ ≤ atom.scale^sigma*atom.scale^(-9*sigma) :=
        mul_le_mul_of_nonneg_right hDlog (Real.rpow_nonneg hx0.le _)
      _ = atom.scale^(-8*sigma) := by rw [← Real.rpow_add hx0]; congr 1; ring
  have hneg : atom.scale^(-8*sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hX
      (show -8*sigma ≤ 0 by linarith)
  exact ⟨hg0.trans_le hmul8,hBfull,hH,by linarith [hH.trans hneg]⟩

end
end ImbalancedChen.Part3.ActualSpectralUniformGeometry20261028
