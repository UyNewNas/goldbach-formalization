import ImbalancedChen.Part3OriginalCuspSlopePacking
import ImbalancedChen.Part3ActualContinuousPoincarePairing
import ImbalancedChen.Part3Gamma0GeneralCuspUnitPeriod
import ImbalancedChen.Part3Gamma0EffectiveFiniteUnfolding
import ImbalancedChen.Part3ActualCuspStripCutoff

/-! Count effective copies of the high unit strip at each of the two original
frames. The relative lower-left entry lies in Nℤ in either normalized frame. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalCuspHitPacking20261112
open Matrix Matrix.SpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane
open OriginalCuspSlopePacking20261112 ActualContinuousPoincarePairing20261110
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0ActualCuspsSourceOnly Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0EffectiveActionKernel20261024z ActualCuspStripCutoff20261025a

private def vector (G : SL(2,ℝ)) (w : ℍ) : ℝ×ℝ :=
  ((G 1 0*w.re+G 1 1)/Real.sqrt w.im,G 1 0*Real.sqrt w.im)

private theorem length_sq (G : SL(2,ℝ)) (w : ℍ) :
    (vector G w).1^2+(vector G w).2^2 = 1/(G • w).im := by
  let M := SpecialLinearGroup.mapGL ℝ G
  have h : (G • w).im=w.im/Complex.normSq (UpperHalfPlane.denom M w) := by
    change (M • w).im=_
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp [M,det_mapGL]
  have D : Complex.normSq (UpperHalfPlane.denom M w)=
      (G 1 0*w.re+G 1 1)^2+(G 1 0*w.im)^2 := by
    simp [M,UpperHalfPlane.denom,mapGL_coe_matrix,Complex.normSq_apply,
      Complex.mul_re,Complex.mul_im,pow_two] <;> ring
  rw [h,D,one_div_div]
  dsimp only [vector]
  rw [div_pow,mul_pow,Real.sq_sqrt w.im_pos.le]
  field_simp [w.im_ne_zero] <;> ring

private theorem relative_wedge (G J : SL(2,ℝ)) (w : ℍ) :
    wedge (vector G w) (vector J w)=(J*G⁻¹) 1 0 := by
  simp [wedge,vector,SL2_inv_expl,coe_mul,Matrix.mul_fin_two]
  <;>field_simp [(Real.sqrt_pos.mpr w.im_pos).ne'] <;>ring

private theorem conjugate_c (N : ℕ) (hN : 0<N) (g η : SL(2,ℤ)) :
    ((normalizedScaling N hN g)⁻¹*integralReal η*normalizedScaling N hN g) 1 0 =
      (cuspWidth N g:ℝ)*(((g⁻¹*η*g) 1 0:ℤ):ℝ) := by
  let W := cuspWidth N g
  have hW : 0<(W:ℝ) := by exact_mod_cast cuspWidth_pos N hN g
  have h : (normalizedScaling N hN g)⁻¹*integralReal η*normalizedScaling N hN g =
      (widthDiagonal W (cuspWidth_pos N hN g))⁻¹*
        integralReal (g⁻¹*η*g)*widthDiagonal W (cuspWidth_pos N hN g) := by
    simp only [normalizedScaling,integralReal,map_mul,map_inv]
    dsimp only [W]; group
  rw [h]
  change _=(W:ℝ)*_
  simp [widthDiagonal,SL2_inv_expl,coe_mul,Matrix.mul_fin_two,integralReal,map_apply_coe]
  <;> nlinarith [Real.sq_sqrt hW.le,
    congrArg (fun x : ℝ => x*(((g⁻¹*η*g) 1 0:ℤ):ℝ)) (Real.sq_sqrt hW.le)]

private theorem original_lattice (N : ℕ) (hN : 0<N) (one : Bool) (η : CongruenceSubgroup.Gamma0 N) :
    ∃ k : ℤ, (cuspWidth N (originalFrame one):ℤ)*
      (((originalFrame one)⁻¹*(η:SL(2,ℤ))*originalFrame one) 1 0)=(N:ℤ)*k := by
  cases one
  · obtain ⟨k,hk⟩ := (gamma0_mem_iff_level_dvd_c N (η:SL(2,ℤ))).mp η.2
    exact ⟨k,by simpa [originalFrame,cuspWidth_infinity N hN] using hk⟩
  · exact ⟨(cuspOneMatrix⁻¹*(η:SL(2,ℤ))*cuspOneMatrix) 1 0,
      by simp [originalFrame,cuspWidth_cuspOne]⟩

private def frameMatrix (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) (i : effectiveGamma0 N) : SL(2,ℝ) :=
  (normalizedScaling N hN g)⁻¹*integralReal (effectiveRepresentative N i : SL(2,ℤ))

theorem frame_action (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) (i : effectiveGamma0 N) (w : ℍ) :
    frameMatrix N hN g i • w=(normalizedScaling N hN g)⁻¹ • effectiveMatrixAction N i w := by
  simpa only [frameMatrix,mul_smul,integralReal_smul,effectiveMatrixAction]

private theorem same_label (N : ℕ) (hN : 0<N) (g : SL(2,ℤ)) (w : ℍ)
    (i j : effectiveGamma0 N)
    (xi : (frameMatrix N hN g i • w).re∈Ico (0:ℝ) 1)
    (xj : (frameMatrix N hN g j • w).re∈Ico (0:ℝ) 1)
    (hfix : FixesIntegralCusp g ((effectiveRepresentative N j*(effectiveRepresentative N i)⁻¹:
      CongruenceSubgroup.Gamma0 N):SL(2,ℤ))) : i=j := by
  let a := effectiveRepresentative N i
  let b := effectiveRepresentative N j
  let σ := normalizedScaling N hN g
  obtain ⟨k,hk⟩ := normalized_stabilizer_real_action N hN g (b*a⁻¹) hfix
  have move (u : ℍ) : frameMatrix N hN g j • u=(k:ℝ)+ᵥ(frameMatrix N hN g i • u) := by
    have H := hk (frameMatrix N hN g i • u)
    change (b*a⁻¹) • (σ • (frameMatrix N hN g i • u)) =
      σ • ((k:ℝ)+ᵥ(frameMatrix N hN g i • u)) at H
    have hi : σ • (frameMatrix N hN g i • u) = a • u := by
      simpa only [σ,frame_action,smul_inv_smul,effectiveMatrixAction,a]
    rw [hi,mul_smul,inv_smul_smul] at H
    rw [frame_action]
    change σ⁻¹ • (b • u)=_
    rw [H,inv_smul_smul]
  have R := congrArg UpperHalfPlane.re (move w)
  rw [real_vadd_re] at R
  have k0 : k=0 := by
    have kl : (-1:ℝ)<k := by linarith [xi.2,xj.1]
    have kr : (k:ℝ)<1 := by linarith [xi.1,xj.2]
    have l : (-1:ℤ)<k := by exact_mod_cast kl
    have r : k<(1:ℤ) := by exact_mod_cast kr
    omega
  have eqact (u : ℍ) : b • u=a • u := by
    have H := congrArg (fun z : ℍ => σ • z) (move u)
    simpa [frame_action,k0,σ,effectiveMatrixAction,a,b] using H
  have hkern : a⁻¹*b∈gamma0ActionKernel N := by
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro u
    change (a⁻¹*b) • u=u
    rw [mul_smul,eqact,inv_smul_smul]
  exact (effectiveRepresentative_class N i).symm.trans
    ((QuotientGroup.eq.mpr hkern).trans (effectiveRepresentative_class N j))

def hits (N : ℕ) (hN : 0<N) (one : Bool) (Y : ℝ) (w : ℍ) : Set (effectiveGamma0 N) :=
  {i | (normalizedScaling N hN (originalFrame one))⁻¹ • effectiveMatrixAction N i w∈highWidthStrip 1 Y}

theorem count_hits (N : ℕ) (hN : 0<N) (one : Bool) {Y : ℝ} (hY : 0<Y) (w : ℍ)
    (s : Finset (effectiveGamma0 N)) (hs : (↑s:Set _)⊆hits N hN one Y w) :
    (s.card:ℝ)≤2+4/((N:ℝ)*Y) := by
  let g := originalFrame one
  let M := frameMatrix N hN g
  have hit (i) (hi : i∈s) : (M i • w).re∈Ico (0:ℝ) 1 ∧ Y≤(M i • w).im := by
    simpa only [M,frame_action,g] using hs hi
  apply count_lines s (fun i => vector (M i) w) (by exact_mod_cast hN) hY
  · intro i hi
    rw [length_sq]
    exact ⟨one_div_pos.mpr (M i • w).im_pos,one_div_le_one_div_of_le hY (hit i hi).2⟩
  · intro i hi j hj neq
    let η := effectiveRepresentative N j*(effectiveRepresentative N i)⁻¹
    have rel : M j*(M i)⁻¹=(normalizedScaling N hN g)⁻¹*integralReal (η:SL(2,ℤ))*normalizedScaling N hN g := by
      simp only [M,frameMatrix,η,Subgroup.coe_mul,Subgroup.coe_inv,integralReal,map_mul,map_inv]
      group
    rw [relative_wedge,rel,conjugate_c]
    obtain ⟨k,hk⟩ := original_lattice N hN one η
    have K : k≠0 := by
      intro z
      have zero : (g⁻¹*(η:SL(2,ℤ))*g) 1 0=0 :=
        (mul_eq_zero.mp (by simpa [g,z] using hk)).resolve_left
          (by exact_mod_cast (cuspWidth_pos N hN g).ne')
      exact neq (same_label N hN g w i j (hit i hi).1 (hit j hj).1 zero)
    have E : (cuspWidth N g:ℝ)*(((g⁻¹*(η:SL(2,ℤ))*g) 1 0:ℤ):ℝ)=(N:ℝ)*(k:ℝ) := by
      exact_mod_cast hk
    have K1 : (1:ℝ)≤|(k:ℝ)| := by exact_mod_cast Int.one_le_abs K
    rw [E,abs_mul,abs_of_nonneg (Nat.cast_nonneg N)]
    simpa using mul_le_mul_of_nonneg_left K1 (Nat.cast_nonneg N)

theorem hits_finite (N : ℕ) (hN : 0<N) (one : Bool) {Y : ℝ} (hY : 0<Y) (w : ℍ) :
    (hits N hN one Y w).Finite := by
  classical
  by_contra H
  obtain ⟨n,hn⟩ := exists_nat_gt (2+4/((N:ℝ)*Y))
  obtain ⟨s,hs,hc⟩ := Set.Infinite.exists_subset_card_eq H n
  have bd := count_hits N hN one hY w s hs
  rw [hc] at bd
  exact hn.not_ge bd

end ImbalancedChen.Part3.OriginalCuspHitPacking20261112
end
