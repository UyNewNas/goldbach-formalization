import ImbalancedChen.Part3OriginalSwitchedLevelIdentity

/-! The double-trace identity on the actual common positive Fourier
block. Marks are positive by membership, including the endpoint one. -/
namespace ImbalancedChen.Part3.OriginalSwitchedNativeBilinearTrace20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical MatrixGroups
open OriginalSwitchedLevelIdentity20261113 (spectral single levelWeight level_switch)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSwitchedMellinRows20261113 (nativeRow)
open OriginalExceptionalJNativeCompletion20261110 (exceptional)
open OriginalSameInfinityTensorSpectrum20261113 (disc)
open ActualCuspBasisWhittakerCoefficients20261102 (basisR_eq_half_native)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)

private def mark {j : ℕ} (m : ↥(dyadicWindow j)) : ℕ+ :=
  ⟨m.val,(pow_pos (by norm_num : 0<(2:ℕ)) j).trans_le (Finset.mem_Ico.mp m.property).1⟩

private def amplitude {j : ℕ} (ω : ℝ) (m n : ↥(dyadicWindow j)) :=
  star (phaseAt ω m.val)*phaseAt ω n.val

def singleBlock (q : ℕ+) (Y : ℝ) (j : ℕ) (ω : ℝ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
    amplitude ω m n*spectral q (mark m) (mark n) (single Y)

def reflectedBlock (d : ℕ+) (Y Q : ℝ) (j : ℕ) (ω : ℝ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
    amplitude ω m n*spectral d (mark m) (mark n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)

/-- The entire Maass, incoming Eisenstein and holomorphic totals
on both quotients. The finite double sum uses a single ω across levels. -/
theorem block_trace (j : ℕ) (ω : ℝ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) :
    Summable (fun q : ℕ+ => levelWeight Q q*singleBlock q Y j ω) ∧
    Summable (fun d : ℕ+ => reflectedBlock d Y Q j ω) ∧
    (∑' q : ℕ+,levelWeight Q q*singleBlock q Y j ω)=∑' d : ℕ+,reflectedBlock d Y Q j ω := by
  let I := ↥(dyadicWindow j)
  let A := fun (m n : I) (q : ℕ+) => levelWeight Q q*spectral q (mark m) (mark n) (single Y)
  let B := fun (m n : I) (d : ℕ+) => spectral d (mark m) (mark n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)
  have per (m n : I) :
      Summable (A m n) ∧ Summable (B m n) ∧ (∑' q,A m n q)=∑' d,B m n d := by
    obtain ⟨C,H⟩ := level_switch (mark m) (mark n) yp
    obtain ⟨outside,E⟩ := H Q qp
    let S := Finset.Icc (1:ℕ+) C
    have ha : HasSum (A m n) (∑ q ∈ S,A m n q) := hasSum_sum_of_ne_finset_zero (fun q h => by
      dsimp only [A];rw [(outside q h).1,mul_zero])
    have hb : HasSum (B m n) (∑ d ∈ S,B m n d) := hasSum_sum_of_ne_finset_zero (fun d h => (outside d h).2)
    exact ⟨ha.summable,hb.summable,E⟩
  let T := ∑ m : I,∑ n : I,amplitude ω m n*(∑' d,B m n d)
  have LH : HasSum (fun q : ℕ+ => levelWeight Q q*singleBlock q Y j ω) T := by
    have H := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
      (fun n (_ : n∈(univ:Finset I)) => ((per m n).2.2 ▸ (per m n).1.hasSum).mul_left (amplitude ω m n)))
    apply H.congr_fun
    intro q
    simp only [singleBlock,Finset.mul_sum,A]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    ring
  have RH : HasSum (fun d : ℕ+ => reflectedBlock d Y Q j ω) T :=
    hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
      (fun n (_ : n∈(univ:Finset I)) => (per m n).2.1.hasSum.mul_left (amplitude ω m n)))
  exact ⟨LH.summable,RH.summable,LH.tsum_eq.trans RH.tsum_eq.symm⟩

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

/-- At a fixed actual complementary slot the same normalization
applies to an arbitrary mark-dependent switch weight. -/
theorem marked_slot (q : ℕ+) (i : ↥(exceptional q)) (j : ℕ) (ω : ℝ) (W : ℕ→ℕ→ℂ) :
    4*(∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),
      amplitude ω m n*disc q (mark m) (mark n) i.val*W m.val n.val)=
    ∑ m ∈ dyadicWindow j,∑ n ∈ dyadicWindow j,
      star (nativeRow q i.val ω m)*nativeRow q i.val ω n*W m n := by
  simp only [Finset.mul_sum]
  have p (m n : ↥(dyadicWindow j)) :
      4*(amplitude ω m n*disc q (mark m) (mark n) i.val*W m.val n.val)=
        star (nativeRow q i.val ω m.val)*nativeRow q i.val ω n.val*W m.val n.val := by
    have h₁ : (m.val:ℤ)≠0 := by exact_mod_cast (mark m).property.ne'
    have h₂ : (n.val:ℤ)≠0 := by exact_mod_cast (mark n).property.ne'
    dsimp only [amplitude,disc,mark,nativeRow]
    rw [basisR_eq_half_native q.val q.property i.val 1 h₁,basisR_eq_half_native q.val q.property i.val 1 h₂]
    simp only [star_mul',star_div₀,star_ofNat]
    ring
  simp_rw [p]
  simp only [Finset.univ_eq_attach,Finset.sum_attach]

end
end ImbalancedChen.Part3.OriginalSwitchedNativeBilinearTrace20261113
