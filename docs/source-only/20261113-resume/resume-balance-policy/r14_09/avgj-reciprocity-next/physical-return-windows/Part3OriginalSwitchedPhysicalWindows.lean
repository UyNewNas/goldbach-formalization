import ImbalancedChen.Part3OriginalSwitchedLevelIdentity

/-! The actual support constants and the finite level windows in the
same-infinity return. All covers have fixed cardinality. -/
namespace ImbalancedChen.Part3.OriginalSwitchedPhysicalWindows20261113
noncomputable section
open Set Finset Complex
open OriginalExceptionalJNativeCompletion20261110 (mem_full_classical_block classicalLevels mem_classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open CommonSmoothCutoff (dyadicCutoff dyadicCutoff_eq_one dyadicCutoff_nonneg)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSwitchedCutoffFamily20261113 (profile parameter_support)
open private cut_eq from ImbalancedChen.Part3OriginalSwitchedLevelIdentity

def returnScale (j : ℕ) (Y Q : ℝ) := Real.pi*classicalMScale j*Y/Q

theorem switched_level_window {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) {x : ℝ}
    (nz : switchedTest Y ((d.val:ℝ)*Q) m n x≠0) :
    16*returnScale j Y Q/25≤(d.val:ℝ) ∧ (d.val:ℝ)≤32*returnScale j Y Q := by
  let M := classicalMScale j
  let R := Real.sqrt ((m:ℝ)*(n:ℝ))
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have a := (mem_full_classical_block j m).mp hm
  have b := (mem_full_classical_block j n).mp hn
  have mpos : 0<m := by exact_mod_cast mp.trans a.1
  have npos : 0<n := by exact_mod_cast mp.trans b.1
  have e := congrFun (cut_eq (⟨m,mpos⟩ : ℕ+) (⟨n,npos⟩ : ℕ+) d yp qp) x
  have L := parameter_support (fun h => nz (e.symm.trans h))
  change (1:ℝ)/4 ≤ Y*(4*Real.pi*R)/((d.val:ℝ)*Q) ∧
    Y*(4*Real.pi*R)/((d.val:ℝ)*Q) ≤ 25/4 at L
  have dp : 0<(d.val:ℝ) := by exact_mod_cast d.property
  have rl : M≤R := by
    rw [show M=Real.sqrt (M*M) by rw [←sq,Real.sqrt_sq mp.le]]
    exact Real.sqrt_le_sqrt (mul_le_mul a.1.le b.1.le mp.le (by exact_mod_cast mpos.le))
  have ru : R≤2*M := by
    rw [show 2*M=Real.sqrt ((2*M)*(2*M)) by rw [←sq,Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (mul_le_mul a.2 b.2 (by exact_mod_cast npos.le) (by positivity))
  have l := (div_le_iff₀ (mul_pos dp qp)).mp L.2
  have u := (le_div_iff₀ (mul_pos dp qp)).mp L.1
  have lo := mul_le_mul_of_nonneg_left rl (mul_nonneg yp.le Real.pi_pos.le)
  have hi := mul_le_mul_of_nonneg_left ru (mul_nonneg yp.le Real.pi_pos.le)
  change 16*(Real.pi*M*Y/Q)/25≤(d.val:ℝ) ∧ (d.val:ℝ)≤32*(Real.pi*M*Y/Q)
  constructor
  · rw [show 16*(Real.pi*M*Y/Q)/25=(16*Real.pi*M*Y/25)/Q by ring,div_le_iff₀ qp]
    nlinarith only [l,lo]
  · rw [show 32*(Real.pi*M*Y/Q)=(32*Real.pi*M*Y)/Q by ring,le_div_iff₀ qp]
    nlinarith only [u,hi]

/-- Six positive dyadic return windows suffice, with starting scales
C/2,C,2C,4C,8C,16C. This includes a possible d=32C. -/
theorem six_return {j m n : ℕ} (hm : m∈dyadicWindow j) (hn : n∈dyadicWindow j)
    {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (d : ℕ+) {x : ℝ}
    (nz : switchedTest Y ((d.val:ℝ)*Q) m n x≠0) :
    ∃ b : ℕ,b<6 ∧ d∈classicalLevels ((2:ℝ)^b*returnScale j Y Q/2) := by
  let C := returnScale j Y Q
  have p : 0<C := div_pos (mul_pos (mul_pos Real.pi_pos
      ((by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1)) yp) qp
  have a := switched_level_window hm hn yp qp d nz
  change 16*C/25≤(d.val:ℝ) ∧ (d.val:ℝ)≤32*C at a
  have lo : C/2<(d.val:ℝ) := by linarith only [a.1,p]
  change ∃ b : ℕ,b<6 ∧ d∈classicalLevels ((2:ℝ)^b*C/2)
  by_cases h0 : (d.val:ℝ)≤C
  · exact ⟨0,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith⟩⟩
  by_cases h1 : (d.val:ℝ)≤2*C
  · exact ⟨1,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith⟩⟩
  by_cases h2 : (d.val:ℝ)≤4*C
  · exact ⟨2,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith⟩⟩
  by_cases h3 : (d.val:ℝ)≤8*C
  · exact ⟨3,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith⟩⟩
  by_cases h4 : (d.val:ℝ)≤16*C
  · exact ⟨4,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith⟩⟩
  exact ⟨5,by decide,(mem_classicalLevels _ _).mpr ⟨by norm_num <;> linarith,by norm_num <;> linarith [a.2]⟩⟩

/-- Use all four plateaux to dominate every level in (Q,16Q].
The same positive weights work throughout the exceptional spectrum. -/
theorem four_input {Q : ℝ} (qp : 0<Q) (q : ℕ+) (lo : Q<(q.val:ℝ)) (hi : (q.val:ℝ)≤16*Q) :
    1≤∑ b ∈ Finset.range 4,dyadicCutoff ((q.val:ℝ)/((2:ℝ)^b*Q)) := by
  have one {b : ℕ} (hb : b<4) (h : (2:ℝ)^b*Q≤(q.val:ℝ)) (h' : (q.val:ℝ)≤2*((2:ℝ)^b*Q)) :
      1≤∑ k ∈ Finset.range 4,dyadicCutoff ((q.val:ℝ)/((2:ℝ)^k*Q)) := by
    have p : 0<(2:ℝ)^b*Q := by positivity
    have v : (q.val:ℝ)/((2:ℝ)^b*Q)∈Set.Icc 1 2 :=
      ⟨(le_div_iff₀ p).mpr (by simpa only [one_mul] using h),(div_le_iff₀ p).mpr h'⟩
    have r := Finset.single_le_sum (f:=fun k : ℕ => dyadicCutoff ((q.val:ℝ)/((2:ℝ)^k*Q)))
      (fun _ _ => dyadicCutoff_nonneg _) (Finset.mem_range.mpr hb)
    simpa only [dyadicCutoff_eq_one v] using r
  by_cases h : (q.val:ℝ)≤2*Q
  · apply one (b:=0) (by decide) <;> norm_num <;> linarith
  by_cases h' : (q.val:ℝ)≤4*Q
  · apply one (b:=1) (by decide) <;> norm_num <;> linarith
  by_cases h'' : (q.val:ℝ)≤8*Q
  · apply one (b:=2) (by decide) <;> norm_num <;> linarith
  apply one (b:=3) (by decide) <;> norm_num <;> linarith

end
end ImbalancedChen.Part3.OriginalSwitchedPhysicalWindows20261113
