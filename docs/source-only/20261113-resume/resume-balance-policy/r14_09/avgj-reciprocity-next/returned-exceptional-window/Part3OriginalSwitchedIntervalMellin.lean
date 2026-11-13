import ImbalancedChen.Part3OriginalSwitchedExceptionalTransform

/-! Opening the reflected complementary weight on any finite set of
positive native marks, including the shorter intervals in the recursion. -/
namespace ImbalancedChen.Part3.OriginalSwitchedIntervalMellin20261113
noncomputable section
open Finset Set MeasureTheory Complex
open scoped BigOperators
open OriginalSwitchedMellinRows20261113
open OriginalSwitchedExceptionalTransform20261113 (switchedTest native_exceptional_weight_switch)
open private kernelDensity kernel_integrable from ImbalancedChen.Part3OriginalSwitchedExceptionalTransform
open CommonSmoothCutoff (dyadicCutoff)
open ActualPrescribedPositiveJ20261112 (exceptionalWeight)
open ActualPositiveNativeDiagonal20261112 (complementaryHeight complementary_range nativeWeight)
open OriginalExceptionalJNativeCompletion20261110 (exceptional mem_exceptional)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

def tested (z : ℕ+) (i : ↥(exceptional z)) (Y t : ℝ) :=
  nativeWeight z.val (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) i.val

private theorem bounded_test (z : ℕ+) (i : ↥(exceptional z)) {Y : ℝ} (yp : 0<Y) :
    Continuous (tested z i Y) ∧ ∃ L : ℝ,∀ t : ℝ,‖tested z i Y t‖≤L := by
  let a := complementaryHeight z.val i.val
  let μ := (volume:Measure ℝ).restrict (Ioi 0)
  let K := kernelDensity Y a
  let J := fun t : ℝ => ∫ x,K x*wave x (-t) ∂μ
  let D : ℂ := Real.cos (Real.pi*a)
  have hx := ((mem_exceptional z i.val).mp i.property).2
  have ar := complementary_range z.val hx
  have k : Integrable K μ := kernel_integrable yp ar.1 ar.2.1
  have cont : Continuous J := by
    apply continuous_of_dominated (bound:=fun x => ‖K x‖)
    · intro t
      exact k.aestronglyMeasurable.mul (show Measurable (fun x : ℝ => wave x (-t)) from by
        unfold wave;fun_prop).aestronglyMeasurable
    · intro t
      exact ae_of_all μ (fun x => by simp only [norm_mul,wave_norm,mul_one,le_refl])
    · exact k.norm
    · exact ae_of_all μ (fun x => by unfold wave;fun_prop)
  have same : tested z i Y=fun t => J t/D := by
    funext t
    simp only [tested,nativeWeight,if_pos hx]
    congr 1
    apply integral_congr_ae
    exact ae_of_all μ (fun x => by dsimp only [kernelDensity,K];ring)
  rw [same]
  refine ⟨cont.div_const _,(∫ x,‖K x‖ ∂μ)/‖D‖,fun t => ?_⟩
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg D)
  exact norm_integral_le_of_norm_le k.norm (ae_of_all μ (fun x => by simp only [norm_mul,wave_norm,mul_one,le_refl]))

def carrier (z : ℕ+) (i : ↥(exceptional z)) (Y Q t : ℝ) :=
  density t*(wave (4*Real.pi/((z.val:ℝ)*Q)) t*tested z i Y t)

private theorem carrier_integrable (z : ℕ+) (i : ↥(exceptional z)) {Y : ℝ} (yp : 0<Y) (Q : ℝ) :
    Integrable (carrier z i Y Q) := by
  obtain ⟨h,L,b⟩ := bounded_test z i yp
  apply density_integrable.mul_bdd (c:=L)
  · exact ((show Continuous (wave (4*Real.pi/((z.val:ℝ)*Q))) from by unfold wave;fun_prop).mul h).aestronglyMeasurable
  · exact ae_of_all _ (fun t => by simpa only [norm_mul,wave_norm,one_mul] using b t)

def marked (z : ℕ+) (i : ↥(exceptional z)) (Y Q ω : ℝ) (S : Finset ℕ) :=
  let v := nativeRow z i.val ω
  ∑ m ∈ S,∑ n ∈ S,star (v m)*v n*nativeWeight z.val (switchedTest Y ((z.val:ℝ)*Q) m n) i.val

/-- Complex equality, with the cosine already in the native spectral
weight. There is no restriction on the exceptional order in this identity. -/
theorem interval_mellin (z : ℕ+) (i : ↥(exceptional z)) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q)
    (ω : ℝ) (S : Finset ℕ) (pos : ∀ m∈S,0<m) :
    marked z i Y Q ω S=((2*Real.pi)⁻¹:ℝ) • ∫ t : ℝ,carrier z i Y Q t*
      (star (twistedRow S (nativeRow z i.val ω) (-(t/2)))*twistedRow S (nativeRow z i.val ω) (t/2)) := by
  let v := nativeRow z i.val ω
  let P := (2*Real.pi)⁻¹
  let F (m n : ℕ) (t : ℝ) := carrier z i Y Q t*
    ((star (v m)*wave (m:ℝ) (t/2))*(v n*wave (n:ℝ) (t/2)))
  have fi (m n : ℕ) : Integrable (F m n) := by
    apply (carrier_integrable z i yp Q).mul_bdd (c:=‖v m‖*‖v n‖)
    · unfold wave;fun_prop
    · exact ae_of_all _ (fun t => by simp only [norm_mul,norm_star,wave_norm,mul_one,le_refl])
  have hx := ((mem_exceptional z i.val).mp i.property).2
  have term (m : ℕ) (hm : m∈S) (n : ℕ) (hn : n∈S) :
      star (v m)*v n*nativeWeight z.val (switchedTest Y ((z.val:ℝ)*Q) m n) i.val=P • ∫ t,F m n t := by
    let a := complementaryHeight z.val i.val
    let D : ℂ := Real.cos (Real.pi*a)
    have H := native_exceptional_weight_switch z i yp qp (pos m hm) (pos n hn)
    simp only [nativeWeight,if_pos hx,H,Complex.real_smul]
    let b := star (v m)*v n
    let J := fun t => exceptionalWeight (fun x => (dyadicCutoff (Y*x):ℂ)*wave x (-t)) a
    let G := fun t => density t*wave (4*Real.pi/((z.val:ℝ)*Q)) t*wave (m:ℝ) (t/2)*wave (n:ℝ) (t/2)*J t
    change b*((P:ℂ)*(∫ t,G t)/D)=(P:ℂ)*(∫ t,F m n t)
    rw [show b*((P:ℂ)*(∫ t,G t)/D)=(P:ℂ)*((b/D)*(∫ t,G t)) by ring,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by simp only [G,F,b,J,carrier,tested,nativeWeight,if_pos hx,D,a];ring)
  have finite (m : ℕ) : (∫ t,∑ n∈S,F m n t)=∑ n∈S,∫ t,F m n t :=
    integral_finsetSum S (fun n _ => fi m n)
  calc
    _ = ∑ m ∈ S,∑ n ∈ S,P • ∫ t,F m n t := sum_congr rfl (fun m hm => sum_congr rfl (term m hm))
    _ = P • ∫ t,∑ m ∈ S,∑ n ∈ S,F m n t := by
      rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => fi m n))]
      simp_rw [finite,Finset.smul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [twistedRow,star_sum,star_mul',star_wave,neg_neg]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply sum_congr rfl
      intro m _
      apply sum_congr rfl
      intro n _
      dsimp only [F,v]
      ring

end
end ImbalancedChen.Part3.OriginalSwitchedIntervalMellin20261113
