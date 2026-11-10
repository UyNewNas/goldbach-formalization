import ImbalancedChen.P4AOriginalFiniteFallbackPayment

namespace ImbalancedChen.P4AOriginalFiniteFallbackPhysicalRange
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AFull87UnionCompilerPayment (top)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackRange (raw_range Bounded)

private theorem rough_range (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0 < delta) (n : ℕ) (D : OriginalData) (he : 0 ≤ D.e)
    (tags : ℕ → List Bool) (N cap : ℕ) (hN : 2 ≤ N) (omega z tau : ℝ)
    (hw : 0 < omega) (ht : 0 < tau) {d : ℕ}
    (hc : coefficient (F T delta n D omega N) tags N cap ((N : ℝ)^omega) z tau d ≠ 0) :
    (d : ℝ) < (N : ℝ)^(top + tau*(J0 omega : ℝ)) := by
  obtain ⟨f,hraw,hcell,_,_⟩ := active_has_raw_witness _ _ _ _ _ _ _ hc
  obtain ⟨hr,hf⟩ := raw_range T hT delta hd n D he omega N cap hN omega z hw hraw
  have hr' : (d.primeFactorsList.length : ℝ) ≤ (J0 omega : ℝ) := by
    rw [← cell_rank_preserved _ _ _ _ _ _ hcell]
    exact_mod_cast hr.le
  have hm : d ∈ universe N cap ((N : ℝ)^omega) z := by
    by_contra h
    exact hc (by simp only [coefficient,if_neg h])
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    _ ≤ _ := same_cell_product_le _ N cap hN _ z tau ht hm hcell
    _ < (N : ℝ)^(tau*(d.primeFactorsList.length : ℝ)) * (N : ℝ)^top :=
      mul_lt_mul_of_pos_left hf (Real.rpow_pos_of_pos hn0 _)
    _ = (N : ℝ)^(top+tau*(d.primeFactorsList.length : ℝ)) := by
      rw [Real.rpow_add hn0]
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn.le
      (add_le_add_left (mul_le_mul_of_nonneg_left hr' ht.le) _)

/-- The nonzero *same tagged physical rho* has the manuscript's strict
599/1000 support, with both small-beta slopes and actual eighth fallback.
The common width restriction can be intersected with the compiler mesh. -/
theorem data_physical_range (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0 < delta) (n : ℕ) (D : OriginalData) (he : 0 ≤ D.e)
    (omega ell : ℝ) (hw : 0 < omega) (hl : ell < 1/1000) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
    ell + tau*(J0 omega : ℝ) < 1/1000 ∧
    ∀ (N cap : ℕ), 2 ≤ N → ∀ (z : ℝ) (tags : ℕ → List Bool) (q : ℕ),
    P4AUpperTaggedBetaAttachment.rho (F T delta n D omega N) tags N cap ((N : ℝ)^omega) z tau
      ((N : ℝ)^ell) q ≠ 0 → (q : ℝ) < (N : ℝ)^(599/1000 : ℝ) := by
  let J := (J0 omega : ℝ)
  let tau0 := (1/1000-ell)/(2*(J+1))
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hden : 0 < 2*(J+1) := by positivity
  have hbudget := div_mul_cancel₀ (1/1000-ell) hden.ne'
  refine ⟨tau0,div_pos (sub_pos.mpr hl) hden,?_⟩
  intro tau ht hsmall
  have htime : ell+tau*J < 1/1000 := by
    have hh := mul_le_mul_of_nonneg_right hsmall hJ
    have heq : tau0*(2*(J+1)) = 1/1000-ell := hbudget
    nlinarith [show 0 < tau0 from ht.trans_le hsmall, mul_nonneg (ht.trans_le hsmall).le hJ]
  refine ⟨htime,?_⟩
  intro N cap hN z tags q hq
  let w := (N : ℝ)^omega
  let L := (N : ℝ)^ell
  have hm : q ∈ P4AUpperTaggedBetaAttachment.support N cap w z := by
    by_contra hx
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hx)
  obtain ⟨⟨a,d⟩,had,hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨ha,hh⟩ := Finset.mem_product.mp had
  have hv := P4AUpperTaggedBetaAttachment.rho_at_product (F T delta n D omega N) tags N cap w z tau L ha hh
  have hpair : coefficient (F T delta n D omega N) tags N cap w z tau d *
      (if 0 ≤ coefficient (F T delta n D omega N) tags N cap w z tau d then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 := by rw [← hv,hprod]; exact hq
  obtain ⟨hc,hb⟩ := mul_ne_zero_iff.mp hpair
  have haL : (a : ℝ) < L := by
    split_ifs at hb
    · exact (actualSmallRosserPlus_active hb).2.1
    · exact (actualSmallRosserMinus_active hb).2.1
  have hrough := rough_range T hT delta hd n D he tags N cap hN omega z tau hw ht hc
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 := zero_lt_one.trans hn
  calc
    (q : ℝ) = (a : ℝ)*(d : ℝ) := by rw [← hprod,Nat.cast_mul]
    _ ≤ L*(d : ℝ) := mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg d)
    _ < L*(N : ℝ)^(top+tau*J) :=
      mul_lt_mul_of_pos_left hrough (Real.rpow_pos_of_pos hn0 ell)
    _ = (N : ℝ)^(ell+(top+tau*J)) := (Real.rpow_add hn0 _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hn.le
      dsimp only [top]
      linarith


end
end ImbalancedChen.P4AOriginalFiniteFallbackPhysicalRange
