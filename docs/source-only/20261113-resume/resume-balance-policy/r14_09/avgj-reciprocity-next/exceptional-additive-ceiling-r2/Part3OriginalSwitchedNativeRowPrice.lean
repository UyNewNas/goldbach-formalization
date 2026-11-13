import ImbalancedChen.Part3OriginalSwitchedAdditiveWeight

/-! Apply the additive Bessel ceiling under the original reflected
Mellin integral. Both half-frequency rows share the literal additive phase. -/
namespace ImbalancedChen.Part3.OriginalSwitchedNativeRowPrice20261113
noncomputable section
open Set MeasureTheory Complex Finset
open scoped BigOperators
open OriginalSwitchedMellinRows20261113
open OriginalSwitchedExceptionalTransform20261113 (switchedTest native_weighted_row)
open OriginalSwitchedAdditiveWeight20261113 (native_additive)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau mem_exceptional)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open CommonSmoothCutoff (dyadicCutoff)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open ActualPositiveNativeDiagonal20261112 (complementaryHeight complementary_range nativeWeight)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

theorem native_row_price {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ Q : ℝ,0<Q → ∀ (z : ℕ+) (i : ↥(exceptional z)),
      tau z i.val≤T → ∀ (j : ℕ) (ω : ℝ),
      let S := dyadicWindow j
      let v := nativeRow z i.val ω
      let a := complementaryHeight z.val i.val
      ‖(∑ m ∈ S,∑ n ∈ S,star (v m)*v n*exceptionalWeight
        (switchedTest Y ((z.val:ℝ)*Q) m n) a)/(Real.cos (Real.pi*a):ℂ)‖≤
      C*(Y^(tau z i.val)+Y^ε)*
        ∫ t : ℝ,‖density t‖*(‖twistedRow S v (-(t/2))‖^2+‖twistedRow S v (t/2)‖^2) := by
  obtain ⟨K,X,kp,x1,H⟩ := native_additive tp t1 ep
  let P := (2*Real.pi)⁻¹
  have pp : 0<P := by dsimp only [P];positivity
  refine ⟨P*K/2,X,by positivity,x1,fun Y hy Q qp z i st j ω => ?_⟩
  have yp := zero_lt_one.trans_le (x1.trans hy)
  have ex := ((mem_exceptional z i.val).mp i.property).2
  let S := dyadicWindow j
  let v := nativeRow z i.val ω
  let a := complementaryHeight z.val i.val
  let D := Real.cos (Real.pi*a)
  let W := K*(Y^(tau z i.val)+Y^ε)
  let u := fun t => twistedRow S v (-(t/2))
  let w := fun t => twistedRow S v (t/2)
  let L := ∑ m ∈ S,‖v m‖
  let J := fun t => exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) a
  let phase := fun t => wave (4*Real.pi/((z.val:ℝ)*Q)) t
  let F := fun t => (density t*phase t*(star (u t)*w t))*J t
  let G := fun t => ‖density t‖*(‖u t‖^2+‖w t‖^2)
  have dp : 0<D := (complementary_range z.val ex).2.2
  have wp : 0≤W := by dsimp only [W];positivity
  have lp : 0≤L := sum_nonneg (fun _ _ => norm_nonneg _)
  have cont : Continuous u ∧ Continuous w := by unfold u w twistedRow wave;constructor <;> fun_prop
  have I : Integrable G := by
    apply density_integrable.norm.mul_bdd (c:=2*L^2)
      ((cont.1.norm.pow 2).add (cont.2.norm.pow 2)).aestronglyMeasurable
    filter_upwards [] with t
    have m := pow_le_pow_left₀ (norm_nonneg (u t)) (row_norm_le S v (-(t/2))) 2
    have n := pow_le_pow_left₀ (norm_nonneg (w t)) (row_norm_le S v (t/2)) 2
    rw [Real.norm_of_nonneg (by positivity : 0≤‖u t‖^2+‖w t‖^2)]
    change ‖u t‖^2≤L^2 at m
    change ‖w t‖^2≤L^2 at n
    linarith
  have budget (t : ℝ) : ‖F t/(D:ℂ)‖≤(W/2)*G t := by
    have Jp := H Y hy z i st t
    simp only [nativeWeight,if_pos ex,norm_div,Complex.norm_real,Real.norm_of_nonneg dp.le] at Jp
    change ‖J t‖/D≤W at Jp
    have prod := (by nlinarith only [sq_nonneg (‖u t‖-‖w t‖)] :
      ‖u t‖*‖w t‖≤(‖u t‖^2+‖w t‖^2)/2)
    have raw := mul_le_mul_of_nonneg_left (mul_le_mul prod Jp (div_nonneg (norm_nonneg _) dp.le)
      (by positivity)) (norm_nonneg (density t))
    simp only [F,G,phase,norm_div,norm_mul,norm_star,wave_norm,mul_one,Complex.norm_real,Real.norm_of_nonneg dp.le]
    convert raw using 1 <;> ring
  have bound := norm_integral_le_of_norm_le (I.const_mul (W/2)) (ae_of_all _ budget)
  rw [integral_const_mul] at bound
  change ‖(∑ m ∈ S,∑ n ∈ S,star (v m)*v n*exceptionalWeight
    (switchedTest Y ((z.val:ℝ)*Q) m n) a)/(D:ℂ)‖≤_
  rw [native_weighted_row z i j ω yp qp]
  change ‖(P • ∫ t,F t)/(D:ℂ)‖≤_
  rw [Complex.real_smul,mul_div_assoc,←integral_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg pp.le]
  apply (mul_le_mul_of_nonneg_left bound pp.le).trans_eq
  dsimp only [G,W,S,v,u,w];ring

end
end ImbalancedChen.Part3.OriginalSwitchedNativeRowPrice20261113
