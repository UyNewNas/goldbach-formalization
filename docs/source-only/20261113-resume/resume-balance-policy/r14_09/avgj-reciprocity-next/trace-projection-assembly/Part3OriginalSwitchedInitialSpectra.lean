import ImbalancedChen.Part3OriginalSwitchedProjectionMask

/-! The initial arithmetic bound and the complete positive-weight
error paid together. Exactly the two principal measures and the
complementary tail beyond the fixed order remain on the right. -/
namespace ImbalancedChen.Part3.OriginalSwitchedInitialSpectra20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedInitialProjection20261113 (outsideSlot remainder bandEnergy initial_projection)
open OriginalSwitchedProjectionMask20261113 (hol_price)
open OriginalSwitchedTraceProjection20261113 (R C H)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedIntervalReturn20261113 (retained)
open OriginalSwitchedMellinRows20261113 (nativeRow twistedRow)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels exceptional tau)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

def residual (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (T Y Q ω : ℝ) :=
  ‖outsideSlot q ap b T Y ω‖+‖R false q ap b Y Q ω‖+‖C false q ap b Y Q ω‖

theorem paid_initial {T ε : ℝ} (tp : 0≤T) (t1 : T<1) (ep : 0<ε) :
    ∃ c D Y₀ : ℝ,0<c ∧ 0<D ∧ 1≤Y₀ ∧ ∀ (j a b : ℕ) (lo : 2^j≤a),a≤b → b≤2^(j+1) →
      ∀ (Y Q ω : ℝ),Y₀≤Y → 0<Q →
      let M := classicalMScale j
      let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
      c*bandEnergy (classicalLevels Q) T Y ω a b≤
        D*(((1+M)*(1+Y))^ε*(M+Y)*M+(Q+M^(1+ε))*M)+
          4*∑ q∈classicalLevels Q,residual q ap b T Y Q ω := by
  obtain ⟨c,A,X,cp,ap,x1,g⟩ := initial_projection tp t1 ep
  obtain ⟨B,bp,h⟩ := hol_price ep
  refine ⟨c,4*(A+B),X,cp,mul_pos (by norm_num) (add_pos_of_pos_of_nonneg ap bp),x1,
    fun j a b lo ab hi Y Q ω hy qp => ?_⟩
  let M := classicalMScale j
  let L := classicalLevels Q
  let hp := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let G := ((1+M)*(1+Y))^ε*(M+Y)*M
  let V := (Q+M^(1+ε))*M
  let U := ∑ q∈L,residual q hp b T Y Q ω
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have yp := zero_lt_one.trans_le (x1.trans hy)
  have gp : 0≤G := by dsimp only [G];positivity
  have vp : 0≤V := by dsimp only [V];positivity
  have sep : (∑ q∈L,remainder q hp b T Y Q ω)=U+∑ q∈L,‖H false q hp b Y Q ω‖ :=
    Finset.sum_add_distrib
  have z := g j a b lo ab hi Y Q ω hy qp
  rw [sep] at z
  have w := h false j a b lo hi Y Q Q ω (x1.trans hy) qp qp
  change (∑ q∈L,‖H false q hp b Y Q ω‖)≤B*V at w
  apply z.trans
  change 4*(A*((1+M)*(1+Y))^ε*(M+Y)*M+(U+∑ q∈L,‖H false q hp b Y Q ω‖))≤
    (4*(A+B))*(G+V)+4*U
  nlinarith only [w,mul_nonneg ap.le vp,mul_nonneg bp gp,
    show A*((1+M)*(1+Y))^ε*(M+Y)*M=A*G by dsimp only [G];ring]

/-- A local theorem on the indicated finite set: the actual native
gap, when available on those slots, makes this the full native energy.
No family-level bound is introduced by either projection estimate. -/
theorem all_slots_at_cap (L : Finset ℕ+) (T Y ω : ℝ) (a b : ℕ) (ap : 0<a)
    (cap : ∀ q∈L,∀ i : ↥(exceptional q),tau q i.val≤T) :
    bandEnergy L T Y ω a b=intervalEnergy L Y ω a b 0 ∧
    ∀ q∈L,outsideSlot q ap b T Y ω=0 := by
  classical
  constructor
  · apply sum_congr rfl
    intro q hq
    simp only [retained,Finset.sum_filter]
    exact sum_congr rfl (fun i _ => if_pos (cap q hq i))
  · intro q hq
    exact sum_eq_zero (fun i _ => if_neg (not_lt.mpr (cap q hq i)))

end
end ImbalancedChen.Part3.OriginalSwitchedInitialSpectra20261113
