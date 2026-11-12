import ImbalancedChen.Part3OriginalHeckeCosetRows
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

namespace ImbalancedChen.Part3.OriginalHeckeRowSlash20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane ModularForm ModularGroup
open Gamma0ParabolicBottomRow20261025a Gamma0ParabolicCosetRows20261025a
open Gamma0ParabolicEffectiveDecomposition20261025a GammaInfinityTranslationStrip20261025a
open OriginalHeckeStripPairing20261112 OriginalHolomorphicPoincare20261112
open OriginalHeckeCosetRows20261112

theorem seed_translation (r m : ℕ) (s : ℝ) (l : ℤ) :
    (heckeSeed m s ∣[2*(r:ℤ)] (ModularGroup.T^l))=heckeSeed m s := by
  funext w
  rw [ModularForm.SL_slash_apply,ModularGroup.modular_T_zpow_smul,← translate_eq_vadd]
  have h : (translate l w).im=w.im := by rw [translate_eq_vadd];rfl
  simp [heckeSeed,q_translate,h,ModularGroup.denom_apply,ModularGroup.coe_T_zpow]

theorem seed_signed (r m : ℕ) (s : ℝ) (M : SL(2,ℤ)) :
    (heckeSeed m s ∣[2*(r:ℤ)] (-M))=(heckeSeed m s ∣[2*(r:ℤ)] M) := by
  funext w
  have hd : denom (-M) w= -(denom M w) := by
    simp only [ModularGroup.denom_apply];push_cast;simp [neg_mul]
  have he : (2*(r:ℤ))=((2*r:ℕ):ℤ) := by push_cast;rfl
  rw [ModularForm.SL_slash_apply,ModularForm.SL_slash_apply,UpperHalfPlane.SL_neg_smul,hd,he]
  simp only [zpow_neg,zpow_natCast,pow_mul,neg_sq]

theorem seed_same_row (r m : ℕ) (s : ℝ) {A B : SL(2,ℤ)}
    (h : bottomRow A=bottomRow B ∨ bottomRow A= -bottomRow B) :
    (heckeSeed m s ∣[2*(r:ℤ)] A)=(heckeSeed m s ∣[2*(r:ℤ)] B) := by
  obtain ⟨l,H|H⟩ := (signed_bottomRow_iff_left_signed_translation B A).mp h
  · rw [H,SlashAction.slash_mul,seed_translation]
  · rw [H,seed_signed,SlashAction.slash_mul,seed_translation]

theorem seed_actual_row {N : ℕ} (r m : ℕ) (s : ℝ) (g : SL(2,ℤ)) (v : Row N g) :
    (heckeSeed m s ∣[2*(r:ℤ)] ((parabolicRepresentative N (rowEquiv N g v):SL(2,ℤ))*g)) =
      (heckeSeed m s ∣[2*(r:ℤ)] matrix v) := by
  have H := (covariant_relation g (parabolicRepresentative N (rowEquiv N g v)) (gamma v)).mp
    (parabolicRepresentative_class N (rowEquiv N g v))
  rw [gamma_frame] at H
  exact seed_same_row r m s H

/-- The ungrouped series is exactly the actual Poincaré sum slashed to this cusp. -/
theorem heckeP_rows (N r m : ℕ) (s : ℝ) (g : SL(2,ℤ)) (w : ℍ) :
    (heckeP N r m s ∣[2*(r:ℤ)] g) w =
      ∑' v : Row N g, (heckeSeed m s ∣[2*(r:ℤ)] matrix v) w := by
  let k : ℤ := 2*(r:ℤ)
  have H (Q : GammaInfinityCosets N) :
      (heckeSeed m s ∣[k] (parabolicRepresentative N Q:SL(2,ℤ))) (g • w) *
          denom g w^(-k) = (heckeSeed m s ∣[k] ((parabolicRepresentative N Q:SL(2,ℤ))*g)) w := by
    symm
    rw [SlashAction.slash_mul,ModularForm.SL_slash_apply]
  rw [ModularForm.SL_slash_apply,heckeP,← tsum_mul_right]
  change (∑' Q, _ * denom g w^(-k)) = _
  simp_rw [H]
  rw [← (rowEquiv N g).tsum_eq]
  exact tsum_congr fun v => congrFun (seed_actual_row r m s g v) w

theorem norm_seed_term (r m : ℕ) (s : ℝ) (M : SL(2,ℤ)) (w : ℍ) :
    ‖(heckeSeed m s ∣[2*(r:ℤ)] M) w‖ ≤
      w.im^s * ‖denom M w‖^(-(2*(r:ℝ)+2*s)) := by
  have hd : 0<‖denom M w‖ := norm_pos_iff.mpr (denom_ne_zero _ w)
  have hE : Real.exp (-(2*Real.pi*m*(M • w).im))≤1 := Real.exp_le_one_iff.mpr (by positivity)
  rw [ModularForm.SL_slash_apply,heckeSeed,norm_mul,norm_mul,q_norm,
    Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg (M • w).im_pos.le _),
    norm_zpow,← Real.rpow_intCast,ModularGroup.im_smul_eq_div_normSq,
    Complex.normSq_eq_norm_sq,Real.div_rpow w.im_pos.le (sq_nonneg _)]
  have h : (‖denom M w‖^2)^s=‖denom M w‖^(2*s) := by
    rw [← Real.rpow_two,← Real.rpow_mul hd.le]
  rw [h]
  push_cast
  calc
    _ ≤ (w.im^s / ‖denom M w‖^(2*s))*1*‖denom M w‖^(-(2*(r:ℝ))) := by gcongr
    _ = _ := by
      rw [div_eq_mul_inv,← Real.rpow_neg hd.le,mul_one,mul_assoc,← Real.rpow_add hd]
      congr 2;ring

/-- The true s>0 ungrouped series can be regrouped through arbitrary residues even for r=1. -/
theorem rows_norm_summable (N r m : ℕ) (hr : 0<r) {s : ℝ} (hs : 0<s)
    (g : SL(2,ℤ)) (w : ℍ) :
    Summable fun v : Row N g => ‖(heckeSeed m s ∣[2*(r:ℤ)] matrix v) w‖ := by
  let k : ℝ := 2*(r:ℝ)+2*s
  have hk : 2<k := by have h : 1≤(r:ℝ) := by exact_mod_cast hr;dsimp [k];linarith
  let S := EisensteinSeries.summable_one_div_norm_rpow hk
  apply ((S.subtype _).mul_left (w.im^s*EisensteinSeries.r w^(-k))).of_nonneg_of_le
    (fun _ => norm_nonneg _) _
  intro v
  have E := EisensteinSeries.summand_bound w (by linarith : 0≤k) v.val
  have H : denom (matrix v) w = (v.val 0:ℂ)*w+v.val 1 := by
    change (bottomRow (matrix v) 0:ℂ)*w+(bottomRow (matrix v) 1:ℂ)=_
    rw [row_matrix]
  exact (norm_seed_term r m s (matrix v) w).trans (by rw [H,mul_assoc];exact
    mul_le_mul_of_nonneg_left E (Real.rpow_nonneg w.im_pos.le _))

theorem heckeP_row_hasSum (N r m : ℕ) (hr : 0<r) {s : ℝ} (hs : 0<s)
    (g : SL(2,ℤ)) (w : ℍ) :
    HasSum (fun v : Row N g => (heckeSeed m s ∣[2*(r:ℤ)] matrix v) w)
      ((heckeP N r m s ∣[2*(r:ℤ)] g) w) := by
  rw [heckeP_rows]
  exact (rows_norm_summable N r m hr hs g w).of_norm.hasSum

private theorem same_level {N : ℕ} {g : SL(2,ℤ)} (hg : g∈CongruenceSubgroup.Gamma0 N)
    (v : Fin 2→ℤ) :
    (IsCoprime (v 0) (v 1) ∧ (N:ℤ)∣v 0*g 1 1-v 1*g 1 0 ∧ positive v) ↔
    (IsCoprime (v 0) (v 1) ∧ (N:ℤ)∣v 0*(1:SL(2,ℤ)) 1 1-v 1*(1:SL(2,ℤ)) 1 0 ∧ positive v) := by
  by_cases hp : IsCoprime (v 0) (v 1)
  · let M : SL(2,ℤ) := ⟨!![hp.choose_spec.choose,-hp.choose;v 0,v 1],by
      simp [Matrix.det_fin_two_of];linear_combination hp.choose_spec.choose_spec⟩
    change (_ ∧ (N:ℤ)∣M 1 0*g 1 1-M 1 1*g 1 0 ∧ _) ↔
      (_ ∧ (N:ℤ)∣M 1 0*(1:SL(2,ℤ)) 1 1-M 1 1*(1:SL(2,ℤ)) 1 0 ∧ _)
    rw [← OriginalHolomorphicCuspFilter20261112.integral_cusp_gate,
      ← OriginalHolomorphicCuspFilter20261112.integral_cusp_gate,inv_one,mul_one,
      (CongruenceSubgroup.Gamma0 N).mul_mem_cancel_right (inv_mem hg)]
  · simp [hp]

theorem heckeP_automorphic (N r m : ℕ) (s : ℝ) (g : CongruenceSubgroup.Gamma0 N) :
    (heckeP N r m s ∣[2*(r:ℤ)] (g : SL(2,ℤ)))=heckeP N r m s := by
  funext w
  let E : Row N (g:SL(2,ℤ)) ≃ Row N 1 := Equiv.subtypeEquivRight (same_level g.property)
  calc
    _ = ∑' v : Row N (g:SL(2,ℤ)), (heckeSeed m s ∣[2*(r:ℤ)] matrix v) w :=
      heckeP_rows N r m s g w
    _ = ∑' v : Row N 1, (heckeSeed m s ∣[2*(r:ℤ)] matrix v) w :=
      E.tsum_eq (fun v => (heckeSeed m s ∣[2*(r:ℤ)] matrix v) w)
    _ = _ := by rw [← heckeP_rows];simp

theorem zero_seed {N r m : ℕ} {g : SL(2,ℤ)} (s : ℝ) (v : Row N g) (hv : v.val 0=0) :
    (heckeSeed m s ∣[2*(r:ℤ)] matrix v)=heckeSeed m s := by
  have h : bottomRow (matrix v)=bottomRow (1:SL(2,ℤ)) := by
    rw [row_matrix];funext j;fin_cases j
    · simpa [bottomRow] using hv
    · simpa [bottomRow] using (zero_row v hv).1
  simpa using seed_same_row r m s (Or.inl h)

end
end ImbalancedChen.Part3.OriginalHeckeRowSlash20261112
