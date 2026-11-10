import ImbalancedChen.Part3ActualCriticalScatteringEntry
import ImbalancedChen.Part3Gamma0ParabolicBottomRow
import ImbalancedChen.Part3Gamma0EffectiveActionKernel

/-! Reciprocity of the native scattering residues. Signed inversion swaps
the two frames at fixed positive lower-left entry. The two different
residue moduli come from the actual stabilizer widths on opposite sides. -/
namespace ImbalancedChen.Part3.ActualScatteringResidueReciprocity20261110

noncomputable section
open Matrix Matrix.SpecialLinearGroup Set Complex
open scoped MatrixGroups BigOperators
open Gamma0ParabolicBottomRow20261025a Gamma0GeneralCuspWidth20261025a
open Gamma0EffectiveActionKernel20261024z NativeCuspScatteringRowArithmetic20261027
open NativeCuspScatteringDirichlet20261027 ActualNativeScatteringConstant20261110

abbrev Residues (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ+) := ↥(residueBlock N g h c)

private def admissible (N : ℕ) (g h A : SL(2,ℤ)) : Prop :=
  g*A*h⁻¹ ∈ CongruenceSubgroup.Gamma0 N

private theorem matrix_exists (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ+) (d : Residues N g h c) :
    ∃ A : SL(2,ℤ), admissible N g h A ∧ A 1 0 = (c : ℤ) ∧ A 1 1 = (d.val : ℤ) := by
  obtain ⟨γ,H⟩ := ((mem_residueBlock N g h c d.val).mp d.property).2
  let A := g⁻¹*(γ : SL(2,ℤ))*h
  refine ⟨A,?_,congrFun H 0,congrFun H 1⟩
  change g*(g⁻¹*(γ : SL(2,ℤ))*h)*h⁻¹ ∈ _
  rw [show g*(g⁻¹*(γ : SL(2,ℤ))*h)*h⁻¹ = (γ : SL(2,ℤ)) by group]
  exact γ.property

private theorem framed_of_matrix (N : ℕ) (g h A : SL(2,ℤ)) (H : admissible N g h A)
    (c d : ℤ) (hc : A 1 0 = c) (hd : A 1 1 = d) : framedRow N g h c d := by
  let γ : CongruenceSubgroup.Gamma0 N := ⟨g*A*h⁻¹,H⟩
  refine ⟨γ,?_⟩
  change bottomRow (g⁻¹*(g*A*h⁻¹)*h) = _
  rw [show g⁻¹*(g*A*h⁻¹)*h = A by group]
  ext i
  fin_cases i
  · exact hc
  · exact hd

private theorem reverse_matrix (N : ℕ) (hN : 0 < N) (g h A : SL(2,ℤ)) (H : admissible N g h A)
    (c d r k : ℤ) (hc : A 1 0 = c) (hd : A 1 1 = d)
    (hr : r = -(A 0 0)+c*(cuspWidth N g : ℤ)*k) :
    ∃ B : SL(2,ℤ), admissible N h g B ∧ B 1 0 = c ∧ B 1 1 = r ∧ B 0 0 = -d := by
  let j := (cuspWidth N g : ℤ)*k
  let B := (-A⁻¹)*ModularGroup.T^j
  have hneg : h*(-A⁻¹)*g⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    have hh := (CongruenceSubgroup.Gamma0 N).mul_mem (neg_one_mem_gamma0 N)
      ((CongruenceSubgroup.Gamma0 N).inv_mem H)
    simpa [admissible,neg_one_mul,mul_neg,neg_mul,mul_inv_rev,mul_assoc] using hh
  have he : h*B*g⁻¹ = (h*(-A⁻¹)*g⁻¹)*(g*ModularGroup.T^j*g⁻¹) := by dsimp [B]; group
  refine ⟨B,?_,?_,?_,?_⟩
  · unfold admissible
    rw [he]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem hneg (width_multiple_mem_gamma0 N hN g k)
  · simp [B,coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow,SL2_inv_expl,hc]
  · simp [B,j,coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow,SL2_inv_expl,hc,hr] <;> ring
  · simp [B,coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow,SL2_inv_expl,hd]

private def Dual (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ+)
    (d : Residues N g h c) (r : Residues N h g c) : Prop :=
  ∃ A : SL(2,ℤ), admissible N g h A ∧ A 1 0 = (c : ℤ) ∧ A 1 1 = (d.val : ℤ) ∧
    ∃ k : ℤ, (r.val : ℤ) = -(A 0 0)+(c : ℤ)*(cuspWidth N g : ℤ)*k

private theorem dual_exists (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ+)
    (d : Residues N g h c) : ∃ r : Residues N h g c, Dual N g h c d r := by
  obtain ⟨A,HA,hc,hd⟩ := matrix_exists N g h c d
  let m : ℤ := (c : ℤ)*(cuspWidth N g : ℤ)
  have hm : 0 < m := by exact_mod_cast Nat.mul_pos c.2 (cuspWidth_pos N hN g)
  let a := -(A 0 0)
  let r := (a%m).toNat
  have hr : (r : ℤ) = a%m := Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')
  have hlt : r < (c : ℕ)*cuspWidth N g := by
    have hrlt := Int.emod_lt_of_pos a hm
    rw [← hr] at hrlt
    exact_mod_cast hrlt
  let k := -(a/m)
  have he : (r : ℤ) = -(A 0 0)+(c : ℤ)*(cuspWidth N g : ℤ)*k := by
    change (r : ℤ) = a+m*(-(a/m))
    rw [hr,mul_neg]
    linarith [Int.emod_add_mul_ediv a m]
  obtain ⟨B,HB,hc',hr',_⟩ := reverse_matrix N hN g h A HA c d.val r k hc hd he
  have hmem := (mem_residueBlock N h g c r).mpr ⟨hlt,framed_of_matrix N h g B HB _ _ hc' hr'⟩
  exact ⟨⟨r,hmem⟩,A,HA,hc,hd,k,he⟩

private theorem dual_symm (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ+)
    (d : Residues N g h c) (r : Residues N h g c) (H : Dual N g h c d r) :
    Dual N h g c r d := by
  obtain ⟨A,HA,hc,hd,k,hk⟩ := H
  obtain ⟨B,HB,hc',hr',ha'⟩ := reverse_matrix N hN g h A HA c d.val r.val k hc hd hk
  exact ⟨B,HB,hc',hr',0,by simp [ha']⟩

private theorem dual_unique (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ+)
    (d : Residues N g h c) {r v : Residues N h g c}
    (Hr : Dual N g h c d r) (Hv : Dual N g h c d v) : r = v := by
  obtain ⟨A,HA,hc,hd,k,hk⟩ := Hr
  obtain ⟨B,HB,hc',hd',l,hl⟩ := Hv
  have hrow : bottomRow B = bottomRow A := by
    ext i
    fin_cases i <;> simp [bottomRow,hc,hc',hd,hd']
  obtain ⟨j,hj⟩ := (bottomRow_eq_iff_left_translation A B).mp hrow
  have hΓ : g*ModularGroup.T^j*g⁻¹ ∈ CongruenceSubgroup.Gamma0 N := by
    have HE : (g*B*h⁻¹)*(g*A*h⁻¹)⁻¹ = g*ModularGroup.T^j*g⁻¹ := by rw [hj]; group
    rw [← HE]
    exact (CongruenceSubgroup.Gamma0 N).mul_mem HB ((CongruenceSubgroup.Gamma0 N).inv_mem HA)
  obtain ⟨u,hu⟩ := (conjugated_translation_mem_iff_width_dvd N hN g j).mp hΓ
  have hBA : B 0 0 = A 0 0+j*(c : ℤ) := by
    simp [hj,coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow,hc]
  let m : ℤ := (c : ℤ)*(cuspWidth N g : ℤ)
  have hdiff : (v.val : ℤ) = (r.val : ℤ)+m*(l-k-u) := by
    rw [hl,hk,hBA,hu]
    dsimp [m]
    ring
  have hb (w : Residues N h g c) : (w.val : ℤ) < m := by
    exact_mod_cast ((mem_residueBlock N h g c w.val).mp w.property).1
  have hres (w : Residues N h g c) : (w.val : ℤ)%m = (w.val : ℤ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (hb w)
  have hmod := congrArg (fun n : ℤ => n%m) hdiff
  change (v.val : ℤ)%m = ((r.val : ℤ)+m*(l-k-u))%m at hmod
  simp only [Int.add_mul_emod_self_left,Int.add_mul_emod_self_right,hres] at hmod
  exact Subtype.ext (by exact_mod_cast hmod.symm)

/-- The literal finite residues in the two opposite frames are in bijection.
The map sends the canonical lower-right residue to the class of minus
the upper-left entry of its actual determinant-one matrix. -/
def reciprocalResidues (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ+) :
    Residues N g h c ≃ Residues N h g c where
  toFun d := Classical.choose (dual_exists N hN g h c d)
  invFun r := Classical.choose (dual_exists N hN h g c r)
  left_inv d := dual_unique N hN h g c _ (Classical.choose_spec (dual_exists N hN h g c _))
    (dual_symm N hN g h c d _ (Classical.choose_spec (dual_exists N hN g h c d)))
  right_inv r := dual_unique N hN g h c _ (Classical.choose_spec (dual_exists N hN g h c _))
    (dual_symm N hN h g c r _ (Classical.choose_spec (dual_exists N hN h g c r)))

theorem scattering_count_reciprocal (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ) :
    scatteringDirichletCoeff N g h c = scatteringDirichletCoeff N h g c := by
  by_cases hc : c = 0
  · simp [hc]
  · simpa only [Residues,Fintype.card_coe,scatteringDirichletCoeff] using
      Fintype.card_congr (reciprocalResidues N hN g h ⟨c,Nat.pos_of_ne_zero hc⟩)

theorem initial_entry_symmetric (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ) :
    scatteringEntry N g h s = scatteringEntry N h g s := by
  have HW : scatteringWidthFactor N g h s = scatteringWidthFactor N h g s := by
    unfold scatteringWidthFactor
    rw [add_comm (Real.log (cuspWidth N g : ℝ)) _]
  have HC : scatteringCoeffComplex N g h = scatteringCoeffComplex N h g := by
    funext c
    exact congrArg (fun n : ℕ => (n : ℂ)) (scattering_count_reciprocal N hN g h c)
  rw [scatteringEntry,scatteringEntry,scatteringDirichletSeries,scatteringDirichletSeries,HW,HC]

end
end ImbalancedChen.Part3.ActualScatteringResidueReciprocity20261110
