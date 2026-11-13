import ImbalancedChen.Part3OriginalSwitchedReturnedWindow
import ImbalancedChen.Part3OriginalSwitchedInitialTraceGeometry
import ImbalancedChen.Part3OriginalExceptionalNativeEnvelope

/-! Identify the retained native band on both complete cutoff traces.
The four in the marked identity is the literal ρᴷ = 2R on each leg. -/
namespace ImbalancedChen.Part3.OriginalSwitchedIntervalTraceSlots20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical MatrixGroups
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open OriginalSwitchedReturnedWindow20261113 (prefixMax prefix_return)
open OriginalSwitchedIntervalReturn20261113 (retained bill)
open OriginalSwitchedIntervalMellin20261113 (marked)
open OriginalSwitchedMellinRows20261113 (nativeRow twistedRow wave_zero)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSwitchedLevelIdentity20261113 (single)
open OriginalSameInfinityTensorSpectrum20261113 (disc)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR_eq_half_native)
open ActualPositiveNativeDiagonal20261112 (nativeWeight)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels)
open OriginalExceptionalNativeEnvelope20261113 (native_band)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

def slot (q : ℕ+) (i : ↥(exceptional q)) {a : ℕ} (ap : 0<a) (b : ℕ) (ω : ℝ) (W : ℕ→ℕ→ℂ) :=
  ∑ m : ↥(Ico a b),∑ n : ↥(Ico a b),star (phaseAt ω m.val)*phaseAt ω n.val*
    (W m.val n.val*disc q (mark a ap m) (mark a ap n) i.val)

private theorem native_slot (q : ℕ+) (i : ↥(exceptional q)) {a : ℕ} (ap : 0<a) (b : ℕ) (ω : ℝ) (W : ℕ→ℕ→ℂ) :
    4*slot q i ap b ω W=∑ m∈Ico a b,∑ n∈Ico a b,star (nativeRow q i.val ω m)*nativeRow q i.val ω n*W m n := by
  have each (m n : ↥(Ico a b)) :
      4*(star (phaseAt ω m.val)*phaseAt ω n.val*(W m.val n.val*disc q (mark a ap m) (mark a ap n) i.val))=
      star (nativeRow q i.val ω m.val)*nativeRow q i.val ω n.val*W m.val n.val := by
    have mn : (m.val:ℤ)≠0 := by exact_mod_cast (mark a ap m).property.ne'
    have nn : (n.val:ℤ)≠0 := by exact_mod_cast (mark a ap n).property.ne'
    simp only [disc,mark,nativeRow,basisR_eq_half_native q.val q.property i.val 1 mn,
      basisR_eq_half_native q.val q.property i.val 1 nn,star_mul',star_div₀,star_ofNat]
    ring
  simp only [slot,Finset.mul_sum]
  simp_rw [each]
  simp only [Finset.univ_eq_attach,Finset.sum_attach]

def input (z : ℕ+) (i : ↥(exceptional z)) {a : ℕ} (ap : 0<a) (b : ℕ) (Y ω : ℝ) :=
  slot z i ap b ω (fun _ _ => nativeWeight z.val (single Y) i.val)

def output (z : ℕ+) (i : ↥(exceptional z)) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :=
  slot z i ap b ω (fun m n => nativeWeight z.val (switchedTest Y ((z.val:ℝ)*Q) m n) i.val)

private theorem input_value (z : ℕ+) (i : ↥(exceptional z)) {a : ℕ} (ap : 0<a) (b : ℕ) (Y ω : ℝ) :
    4*(input z i ap b Y ω).re=(nativeWeight z.val (single Y) i.val).re*
      ‖twistedRow (Ico a b) (nativeRow z i.val ω) 0‖^2 := by
  let S := Ico a b
  let v := nativeRow z i.val ω
  let W := nativeWeight z.val (single Y) i.val
  have H := native_slot z i ap b ω (fun _ _ => W)
  have sum : (∑ m∈S,∑ n∈S,star (v m)*v n*W)=(star (∑ m∈S,v m)*(∑ n∈S,v n))*W := by
    simp only [star_sum,Finset.sum_mul]
    simp only [Finset.mul_sum,Finset.sum_mul]
  change 4*input z i ap b Y ω=∑ m∈S,∑ n∈S,star (v m)*v n*W at H
  rw [sum,Complex.star_def,←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq] at H
  have E := congrArg Complex.re H
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.ofNat_re,Complex.ofNat_im,
    zero_mul,sub_zero] at E
  rw [E]
  simp only [twistedRow,wave_zero,mul_one,S,v,W] <;> ring

/-- At entry, a fixed band of retained slots gives a positive floor
with its constant fixed before all level sets and all intervals. -/
theorem input_floor {T : ℝ} (tp : 0≤T) (t1 : T<1) :
    ∃ c Y₀ : ℝ,0<c ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (L : Finset ℕ+) (ω : ℝ) (a b : ℕ) (ap : 0<a),
      c*(∑ z∈L,∑ i∈retained T z,Y^(tau z i.val)*‖twistedRow (Ico a b) (nativeRow z i.val ω) 0‖^2)
        ≤4*∑ z∈L,∑ i∈retained T z,(input z i ap b Y ω).re := by
  obtain ⟨c,_,X,cp,_,x1,H⟩ := native_band tp t1
  refine ⟨c,X,cp,x1,fun Y hy L ω a b ap => ?_⟩
  simp only [Finset.mul_sum]
  apply sum_le_sum
  intro z _
  apply sum_le_sum
  intro i hi
  rw [input_value,←mul_assoc]
  exact mul_le_mul_of_nonneg_right (H Y hy z i (Finset.mem_filter.mp hi).2).1 (sq_nonneg _)

/-- At return the finite density bill is the original marked trace
restricted only by τ ≤ T. The two bounded half-frequency costs have
already been paid inside the prefix price. -/
theorem output_bound {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ C Y₀ : ℝ,0<C ∧ 1≤Y₀ ∧ ∀ Y≥Y₀,∀ (Q B : ℝ),0<Q → 0<B → ∀ (ω : ℝ) (j a b : ℕ)
      (lo : 2^j≤a) (ab : a≤b), b≤2^(j+1) →
      let M := classicalMScale j
      let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
      (4*∑ z∈classicalLevels B,∑ i∈retained T z,‖output z i ap b Y Q ω‖)≤
        C*(prefixMax (classicalLevels B) Y ω a b ab+Y^ε*(B+M)*M) := by
  obtain ⟨C,X,cp,x1,H⟩ := prefix_return tp t1 ep
  refine ⟨C,X,cp,x1,fun Y hy Q B qp bp ω j a b lo ab hi => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have ident (z : ℕ+) (i : ↥(exceptional z)) : 4*‖output z i ap b Y Q ω‖=‖marked z i Y Q ω (Ico a b)‖ := by
    have h := native_slot z i ap b ω (fun m n => nativeWeight z.val (switchedTest Y ((z.val:ℝ)*Q) m n) i.val)
    simpa only [output,marked,norm_mul,Complex.norm_ofNat] using congrArg norm h
  change (4*∑ z∈classicalLevels B,∑ i∈retained T z,‖output z i ap b Y Q ω‖)≤_
  simp only [Finset.mul_sum,ident]
  exact H Y hy Q B qp bp ω j a b lo ab hi

end
end ImbalancedChen.Part3.OriginalSwitchedIntervalTraceSlots20261113
