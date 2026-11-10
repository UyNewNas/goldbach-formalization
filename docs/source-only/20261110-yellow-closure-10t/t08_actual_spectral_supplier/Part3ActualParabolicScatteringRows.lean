import ImbalancedChen.Part3ActualParabolicIncoming
import ImbalancedChen.Part3ActualCharacterPoissonRows
import ImbalancedChen.Part3NativeCuspScatteringDirichlet
import Mathlib.Logic.Equiv.Fin.Basic

/-! In the two actual normalized frames, group the native primitive
parabolic Eisenstein series into its diagonal and the finite residue
classes of each positive denominator. -/
namespace ImbalancedChen.Part3.ActualParabolicScatteringRows20261110

noncomputable section
open Complex Set Matrix Matrix.SpecialLinearGroup EisensteinSeries UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators Classical
open ActualCharacterLatticeCompletion20261110 ActualCharacterPoissonRows20261110
open NativeCuspComplexPowerFourier20261027 NativeCuspComplexPeriodization20261027
open ActualEisensteinFourierInterchange20261025a CharacterEisensteinSeries
open PrimitiveEisensteinParameterAnalytic PrimitiveEisensteinParameterAutomorphy
open PrimitiveRealEisensteinAutomorphy RealEisensteinSeedConvergence
open CharacterMiddleZeroFirstPairs20261026b ActualParabolicIncoming20261110
open ActualCharacterCuspExpansion20261110 Gamma0GeneralCuspWidth20261025a
open Gamma0ParabolicBottomRow20261025a Gamma0EffectiveActionKernel20261024z
open Gamma0GeneralCuspUnitPeriod20261025a NativeAllCuspEisenstein20261026b
open Gamma0CuspLeftWidthCovariance20261026b NativeAllCuspFrameCovariance20261026b
open NativeCuspScatteringRowArithmetic20261027 NativeCuspScatteringDirichlet20261027

local instance (N : ℕ) : DecidableEq (NativeCusps N) := Classical.decEq _

private def selected (N : ℕ) (g h : SL(2,ℤ)) (z : ℍ) (s : ℂ) (v : Vec) : ℂ := by
  classical
  exact if framedRow N g h (v 0) (v 1) then latticeSeed z s v else 0

private theorem primitive_selected (N : ℕ) (g h : SL(2,ℤ)) (z : ℍ) (s : ℂ)
    (v : PrimitivePair) :
    selected N g h z s v.val = inClass N g h v * complexSeed z v s := by
  classical
  have hf : framedRow N g h (v.val 0) (v.val 1) ↔
      allowedRow N g ((primitivePairEquiv h).symm v) := by
    simpa only [Equiv.apply_symm_apply] using
      framedRow_primitive_action_iff N g h ((primitivePairEquiv h).symm v)
  have hv : v.val ≠ 0 := by
    intro h0
    have H := (gammaSet_one_mem_iff _).mp v.property
    simp [h0] at H
  by_cases H : framedRow N g h (v.val 0) (v.val 1)
  · simp [selected,inClass,H,hf.mp H,latticeSeed,hv,latticeBase,complexSeed,positiveBase]
  · simp [selected,inClass,H,fun hallowed => H (hf.mpr hallowed)]

private def pairVec := (piFinTwoEquiv (fun _ : Fin 2 => ℤ)).symm

private theorem pairVec_apply (c d : ℤ) : pairVec (c,d) = ![c,d] := by
  ext i
  fin_cases i <;> rfl

private theorem selected_summable (N : ℕ) (g h : SL(2,ℤ)) (z : ℍ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : ℤ × ℤ => selected N g h z s ![p.1,p.2]) := by
  classical
  have hv : Summable (fun v : Vec => ‖selected N g h z s v‖) := by
    apply (seed_summable s.re hs z).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro v
    by_cases H : framedRow N g h (v 0) (v 1)
    · simp [selected,H,norm_latticeSeed z s hs]
    · simpa [selected,H,← norm_latticeSeed z s hs] using norm_nonneg (latticeSeed z s v)
  exact (pairVec.summable_iff.mpr hv.of_norm).congr
    (fun ⟨c,d⟩ => congrArg (selected N g h z s) (pairVec_apply c d))

private def integerRow (N : ℕ) (g h : SL(2,ℤ)) (z : ℍ) (s : ℂ) (c : ℤ) :=
  ∑' d : ℤ, selected N g h z s ![c,d]

private theorem framed_neg (N : ℕ) (g h : SL(2,ℤ)) (c d : ℤ) :
    framedRow N g h (-c) (-d) ↔ framedRow N g h c d := by
  have H (a b : ℤ) (hr : framedRow N g h a b) : framedRow N g h (-a) (-b) := by
    obtain ⟨γ,hγ⟩ := hr
    refine ⟨gamma0NegOne N * γ,?_⟩
    change bottomRow (g⁻¹ * ((-1 : SL(2,ℤ)) * (γ : SL(2,ℤ))) * h) = _
    rw [neg_one_mul,mul_neg,neg_mul]
    have he : bottomRow (-(g⁻¹ * (γ : SL(2,ℤ)) * h)) =
        -bottomRow (g⁻¹ * (γ : SL(2,ℤ)) * h) := rfl
    rw [he,hγ]
    ext i
    fin_cases i <;> rfl
  exact ⟨fun hr => by simpa using H (-c) (-d) hr,H c d⟩

private theorem integerRow_even (N : ℕ) (g h : SL(2,ℤ)) (z : ℍ) (s : ℂ) :
    Function.Even (integerRow N g h z s) := by
  classical
  intro c
  unfold integerRow
  rw [← (Equiv.neg ℤ).tsum_eq (fun d : ℤ => selected N g h z s ![-c,d])]
  apply tsum_congr
  intro d
  change selected N g h z s ![-c,-d] = selected N g h z s ![c,d]
  have hv : (![-c,-d] : Vec) = -![c,d] := by ext i; fin_cases i <;> rfl
  have hb : latticeBase z ![-c,-d] = latticeBase z ![c,d] := by
    simp [latticeBase,neg_mul,← neg_add]
  simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,framed_neg,latticeSeed,hb,hv,neg_eq_zero]

private theorem all_integer_rows (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ)
    (hs : 1 < s.re) (z : ℍ) :
    let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) z
    cuspEisenstein N g s (normalizedScaling N hN h • z) =
      (1/2 : ℂ)*widthFactor N g s * ∑' c : ℤ, integerRow N g h Z s c := by
  classical
  let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) z
  rw [parabolic_reindex]
  congr 1
  change (∑' v : PrimitivePair, inClass N g h v * complexSeed Z v s) = _
  simp_rw [← primitive_selected N g h Z s]
  have hsupp : Function.support (selected N g h Z s) ⊆ gammaSet 1 1 0 := by
    intro v hv
    by_cases H : framedRow N g h (v 0) (v 1)
    · exact (mem_gammaSet_one v).mpr (framedRow_bezout N g h _ _ H)
    · exact False.elim (hv (by simp [selected,H]))
  rw [tsum_subtype_eq_of_support_subset hsupp,← pairVec.tsum_eq (selected N g h Z s)]
  change (∑' p : ℤ × ℤ, selected N g h Z s (pairVec p)) = _
  have He : (fun p : ℤ × ℤ => selected N g h Z s (pairVec p)) =
      fun p : ℤ × ℤ => selected N g h Z s ![p.1,p.2] :=
    funext (fun ⟨c,d⟩ => congrArg (selected N g h Z s) (pairVec_apply c d))
  rw [He]
  exact (selected_summable N g h Z s hs).tsum_prod

def incoming (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (s : ℂ) (y : ℝ) : ℂ :=
  if nativeFrameOrbit N h = nativeFrameOrbit N g then (y : ℂ)^s else 0

private theorem axis (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) (horizontalPoint y hy x)
    (1/2 : ℂ)*widthFactor N g s*integerRow N g h Z s 0 = incoming N g h s y := by
  classical
  let w := cuspWidth N h
  have hw : 0 < (w : ℝ) := by exact_mod_cast cuspWidth_pos N hN h
  let Z := scaledPoint w (cuspWidth_pos N hN h) (horizontalPoint y hy x)
  have ha : integerRow N g h Z s 0 =
      selected N g h Z s zeroFirstPlus.1 + selected N g h Z s zeroFirstMinus.1 := by
    unfold integerRow
    rw [tsum_eq_sum (s := ({1,-1} : Finset ℤ))]
    · simp [zeroFirstPlus,zeroFirstMinus]
    · intro d hd
      have H : ¬ framedRow N g h 0 d := by
        intro hrow
        exact hd (by rcases framedRow_zero_unit N g h d hrow with rfl | rfl <;> simp)
      simp [selected,H]
  have hx : complexSeed Z zeroFirstPlus s = Complex.exp (s*(Real.log ((w : ℝ)*y) : ℂ)) ∧
      complexSeed Z zeroFirstMinus s = Complex.exp (s*(Real.log ((w : ℝ)*y) : ℂ)) := by
    simp [complexSeed,positiveBase,zeroFirstPlus,zeroFirstMinus,Z,scaledPoint_im,horizontalPoint]
  change (1/2 : ℂ)*widthFactor N g s*integerRow N g h Z s 0 = incoming N g h s y
  rw [ha,primitive_selected,primitive_selected,hx.1,hx.2,
    (class_zero_rows N g h).1,(class_zero_rows N g h).2]
  unfold incoming
  rw [nativeFrameOrbit_eq_iff]
  split_ifs with ha
  · obtain ⟨γ,k,hk⟩ := (frames_same_class_iff N g h).mp ha.symm
    have hwg : cuspWidth N h = cuspWidth N g := by
      rw [hk,cuspWidth_right_translation,cuspWidth_left_mul N _ _ γ.property]
    simp only [one_mul,← two_mul]
    rw [widthFactor,← hwg,← show w = cuspWidth N h from rfl,Real.log_mul hw.ne' hy.ne',
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),Complex.ofReal_add,
      ← Complex.ofReal_log hy.le]
    calc
      _ = Complex.exp (-s*(Real.log (w : ℝ) : ℂ)) *
          Complex.exp (s*((Real.log (w : ℝ) : ℂ)+(Real.log y : ℂ))) := by ring
      _ = _ := by rw [← Complex.exp_add]; congr 1; ring
  · simp

def residueShift (N : ℕ) (h : SL(2,ℤ)) (c d : ℕ) : ℝ :=
  (d : ℝ) / ((c : ℝ)*(cuspWidth N h : ℝ))

def denominatorWeight (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ) (s : ℂ) : ℂ :=
  scatteringWidthFactor N g h s * (c : ℂ)^(-(2*s))

def outgoingRow (N : ℕ) (g h : SL(2,ℤ)) (c : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  denominatorWeight N g h c s *
    ∑ d ∈ residueBlock N g h c, periodizedComplexPowerSeed y s (x + residueShift N h c d)

private theorem single_seed (w c : ℕ) (hw : 0 < w) (hc : 0 < c) (s : ℂ) (d : ℤ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    latticeSeed (scaledPoint w hw (horizontalPoint y hy x)) s ![(c : ℤ),d] =
      rowScale c w s * complexPowerSeed y s (x + (d : ℝ)/((c : ℝ)*w)) := by
  let z := scaledPoint w hw (horizontalPoint y hy x)
  let u := x + (d : ℝ)/((c : ℝ)*w)
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hv : (![(c : ℤ),d] : Vec) ≠ 0 := by
    intro h
    exact hc.ne' (by exact_mod_cast congrFun h 0 : c = 0)
  have hlin : (c : ℂ)*((w : ℂ)*(horizontalPoint y hy x : ℂ))+(d : ℂ) =
      ((c : ℂ)*w)*(horizontalPoint y hy u : ℂ) := by
    apply Complex.ext <;> simp [horizontalPoint,u,Complex.mul_re,Complex.mul_im] <;>
      field_simp [hcR.ne',hwR.ne'] <;> ring
  have hnorm : ‖(horizontalPoint y hy u : ℂ)‖^2 = u^2+y^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply,horizontalPoint,pow_two]
  have hbase : latticeBase z ![(c : ℤ),d] = powerBase y u / ((c : ℝ)^2*w) := by
    unfold latticeBase powerBase
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Int.cast_natCast,z,scaledPoint_im,
      scaledPoint_coe,hlin,norm_mul,Complex.norm_natCast,mul_pow,hnorm]
    change (w : ℝ)*y / ((c^2*w^2 : ℝ)*(u^2+y^2)) =
      y/(u^2+y^2)/((c : ℝ)^2*w)
    field_simp [hcR.ne',hwR.ne',show u^2+y^2 ≠ 0 by positivity] <;> ring
  have hcw := (Complex.ofReal_log hcR.le).symm
  have hww := (Complex.ofReal_log hwR.le).symm
  rw [latticeSeed,if_neg hv,hbase,Real.log_div (powerBase_pos hy u).ne' (by positivity),
    Real.log_mul (pow_ne_zero _ hcR.ne') hwR.ne',Real.log_pow,rowScale,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hc.ne' : (c : ℂ) ≠ 0),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hw.ne' : (w : ℂ) ≠ 0),complexPowerSeed,
    ← Complex.exp_add,← Complex.exp_add]
  simp only [Complex.ofReal_natCast] at hcw hww
  rw [hcw,hww]
  congr 1
  dsimp only [u]
  push_cast
  ring

private theorem widths (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ)) (c : ℕ) (s : ℂ) :
    widthFactor N g s * rowScale c (cuspWidth N h) s = denominatorWeight N g h c s := by
  have hw : 0 < (cuspWidth N h : ℝ) := by exact_mod_cast cuspWidth_pos N hN h
  have hlog : Complex.log (cuspWidth N h : ℂ) = (Real.log (cuspWidth N h : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log hw.le).symm
  unfold widthFactor rowScale denominatorWeight scatteringWidthFactor
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hw.ne' : (cuspWidth N h : ℂ) ≠ 0),hlog]
  rw [show -s*((Real.log (cuspWidth N g : ℝ)+Real.log (cuspWidth N h : ℝ) : ℝ) : ℂ) =
      -s*(Real.log (cuspWidth N g : ℝ) : ℂ)+(Real.log (cuspWidth N h : ℝ) : ℂ)*(-s) by
    push_cast; ring,Complex.exp_add]
  ring

theorem positive_denominator (N : ℕ) (hN : 0 < N) (g h : SL(2,ℤ))
    (c : ℕ+) (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) (horizontalPoint y hy x)
    widthFactor N g s * (∑' d : ℤ,
      if framedRow N g h (c : ℤ) d then latticeSeed Z s ![(c : ℤ),d] else 0) =
      outgoingRow N g h c s y x := by
  classical
  let w := cuspWidth N h
  let m := (c : ℕ)*w
  have hw : 0 < w := cuspWidth_pos N hN h
  have hm : 0 < m := Nat.mul_pos c.2 hw
  letI : NeZero m := ⟨hm.ne'⟩
  let Z := scaledPoint w hw (horizontalPoint y hy x)
  let e : Fin m × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv m).symm
  have hrep (r : Fin m) (k : ℤ) : e (r,k) = (r.val : ℤ)+(c : ℤ)*(w : ℤ)*k := by
    change k*(m : ℤ)+(r.val : ℤ) = _
    dsimp only [m]
    push_cast
    ring
  have hstep (r : Fin m) (k : ℤ) :
      selected N g h Z s ![(c : ℤ),e (r,k)] =
        (if framedRow N g h (c : ℤ) (r.val : ℤ) then rowScale c w s *
          complexPowerSeed y s ((x+residueShift N h c r.val)+(k : ℝ)) else 0) := by
    simp only [selected,Matrix.cons_val_zero,Matrix.cons_val_one,hrep,framedRow_shift_iff N hN]
    split_ifs
    · rw [single_seed w c hw c.2]
      congr 2
      unfold residueShift
      change x + (((r.val : ℤ)+(c : ℤ)*(w : ℤ)*k : ℤ) : ℝ)/((c : ℝ)*(w : ℝ)) =
        (x+(r.val : ℝ)/((c : ℝ)*(w : ℝ)))+k
      push_cast
      field_simp [show (c : ℝ) ≠ 0 by positivity,show (w : ℝ) ≠ 0 by exact_mod_cast hw.ne'] <;> ring
    · rfl
  have hsum := (selected_summable N g h Z s hs).prod_factor (c : ℤ)
  change widthFactor N g s * (∑' d : ℤ, selected N g h Z s ![(c : ℤ),d]) = _
  rw [← e.tsum_eq,(e.summable_iff.mpr hsum).tsum_prod,tsum_fintype]
  have hk (r : Fin m) : (∑' k : ℤ, selected N g h Z s ![(c : ℤ),e (r,k)]) =
      if framedRow N g h (c : ℤ) (r.val : ℤ) then
        rowScale c w s * periodizedComplexPowerSeed y s (x+residueShift N h c r.val) else 0 := by
    simp_rw [hstep]
    split_ifs <;> simp [periodizedComplexPowerSeed,tsum_mul_left]
  simp_rw [hk]
  rw [Fin.sum_univ_eq_sum_range (fun d : ℕ => if framedRow N g h (c : ℤ) (d : ℤ) then
    rowScale c w s * periodizedComplexPowerSeed y s (x+residueShift N h c d) else 0),
    ← Finset.sum_filter,← Finset.mul_sum,← mul_assoc,widths]
  rfl

/-- Physical cusp-pair expansion for every horizontal point. Its positive
denominators carry the old native admissibility predicate in the exact
observing-frame residue block. -/
theorem parabolic_residue_expansion (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    cuspEisenstein N g s (normalizedScaling N hN h • horizontalPoint y hy x) =
      incoming N g h s y + ∑' c : ℕ+, outgoingRow N g h c s y x := by
  classical
  let Z := scaledPoint (cuspWidth N h) (cuspWidth_pos N hN h) (horizontalPoint y hy x)
  have hp (c : ℕ+) : widthFactor N g s * integerRow N g h Z s (c : ℤ) =
      outgoingRow N g h c s y x := positive_denominator N hN g h c s hs y hy x
  rw [all_integer_rows N hN g h s hs,tsum_int_eq_zero_add_two_mul_tsum_pnat
    (integerRow_even N g h Z s) (selected_summable N g h Z s hs).prod,nsmul_eq_mul]
  change (1/2 : ℂ)*widthFactor N g s*(integerRow N g h Z s 0 +
    2*(∑' c : ℕ+,integerRow N g h Z s (c : ℤ))) = _
  rw [← axis N hN g h s y hy x,← tsum_congr hp,tsum_mul_left]
  ring

end
end ImbalancedChen.Part3.ActualParabolicScatteringRows20261110
