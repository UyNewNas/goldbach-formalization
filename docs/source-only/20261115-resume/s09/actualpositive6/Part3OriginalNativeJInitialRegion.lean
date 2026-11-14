import ImbalancedChen.Part3OriginalFullPositiveInitialMean

/-! Apply the complete initial estimate directly to T08's pascadiJ in
the original scales for which the initial term pays the critical weight. -/
namespace ImbalancedChen.Part3.OriginalNativeJInitialRegion20261113
noncomputable section
open Finset
open scoped Classical BigOperators
open OriginalFullPositiveInitialMean20261113 (initial_mean)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy full_window)
open OriginalSwitchedTwistedBaseline20261113 (zero_frequency)
open OriginalExceptionalJNativeCompletion20261110 (pascadiJ classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)

theorem initial_region {ε : ℝ} (ep : 0<ε) (A : ℝ) (ap : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset ℕ+) (j : ℕ) (Q X ω : ℝ),0<Q → 0<X →
      S⊆classicalLevels Q → X≤A*(Q+classicalMScale j) →
      pascadiJ S X j ω≤C*((1+Q)*(1+classicalMScale j))^ε*(Q+classicalMScale j)*classicalMScale j := by
  let δ := ε/2
  have dp : 0<δ := half_pos ep
  obtain ⟨K,kp,H⟩ := initial_mean dp
  let c := 1+A
  have c1 : 1≤c := le_add_of_nonneg_right ap
  have cp : 0<c := zero_lt_one.trans_le c1
  refine ⟨K*c^δ*c,by positivity,fun S j Q X ω qp xp sub range => ?_⟩
  let M := classicalMScale j
  let U := (1+Q)*(1+M)
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have order : (2:ℕ)^j≤2^(j+1) := by rw [pow_succ];omega
  have base := H j (2^j) (2^(j+1)) le_rfl order le_rfl Q X ω qp xp
  rw [full_window,zero_frequency] at base
  have posLevel (z : ℕ+) : 0≤∑ i : ↥(OriginalExceptionalJNativeCompletion20261110.exceptional z),
      X^(OriginalExceptionalJNativeCompletion20261110.tau z i.val)*‖∑ m∈MediumGlobalDyadicOwnership20261028.dyadicWindow j,
      OriginalSwitchedMellinRows20261113.nativeRow z i.val ω m‖^2 :=
    sum_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg xp.le _) (sq_nonneg _)
  have mono : pascadiJ S X j ω≤pascadiJ (classicalLevels Q) X j ω :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun z _ _ => posLevel z)
  have up : 0<U := by dsimp [U];positivity
  have um : 1+M≤U := by dsimp [U];nlinarith only [qp.le,mul_nonneg qp.le mp.le]
  have uq : 1+Q+M≤U := by dsimp [U];nlinarith only [mul_nonneg qp.le mp.le]
  have ux : 1+X≤c*U := by
    have u1 : 1≤U := (by linarith only [mp.le] : 1≤1+M).trans um
    have ua : A*(Q+M)≤A*U := mul_le_mul_of_nonneg_left (by linarith only [uq]) ap
    dsimp only [c]
    nlinarith only [range,ua,u1]
  have raw := mul_le_mul um ux (by linarith only [xp] : 0≤1+X) up.le
  have pw := Real.rpow_le_rpow (by positivity : 0≤(1+M)*(1+X)) raw dp.le
  have right : (U*(c*U))^δ=c^δ*U^ε := by
    rw [show U*(c*U)=c*(U*U) by ring,Real.mul_rpow cp.le (mul_nonneg up.le up.le),
      Real.mul_rpow up.le up.le,←Real.rpow_add up,show δ+δ=ε by dsimp [δ];ring]
  rw [right] at pw
  have size : Q+M+X≤c*(Q+M) := by dsimp only [c];linarith only [range]
  have paid := mul_le_mul pw size (by linarith only [qp,mp,xp] : 0≤Q+M+X)
    (mul_nonneg (Real.rpow_nonneg cp.le _) (Real.rpow_nonneg up.le _))
  apply mono.trans (base.trans ?_)
  change K*((1+M)*(1+X))^δ*(Q+M+X)*M≤(K*c^δ*c)*U^ε*(Q+M)*M
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left paid kp.le) mp.le]

/-- In a bounded level-to-length ratio the initial region pays every
weight in the original allowed interval, with the same subset and phase. -/
theorem bounded_ratio {ε : ℝ} (ep : 0<ε) (A B : ℝ) (ap : 0≤A) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset ℕ+) (j : ℕ) (Q X ω : ℝ),0<Q → 0<X →
      S⊆classicalLevels Q → Q≤B*classicalMScale j →
      X≤A*max (classicalMScale j) (Q^2/classicalMScale j) →
      pascadiJ S X j ω≤C*((1+Q)*(1+classicalMScale j))^ε*(Q+classicalMScale j)*classicalMScale j := by
  let K := max 1 B
  have k1 : 1≤K := le_max_left _ _
  have kn := zero_le_one.trans k1
  obtain ⟨C,cp,F⟩ := initial_region ep (A*K) (mul_nonneg ap kn)
  refine ⟨C,cp,fun S j Q X ω qp xp sub low head => F S j Q X ω qp xp sub ?_⟩
  let M := classicalMScale j
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have qm : 0≤Q+M := add_nonneg qp.le mp.le
  have one : Q+M≤K*(Q+M) := by simpa only [one_mul] using mul_le_mul_of_nonneg_right k1 qm
  have low' : Q^2/M≤B*Q := (div_le_iff₀ mp).mpr (by nlinarith only [mul_le_mul_of_nonneg_right low qp.le])
  have qk : Q^2/M≤K*(Q+M) := low'.trans (mul_le_mul (le_max_right 1 B)
    (by linarith only [mp] : Q≤Q+M) qp.le kn)
  have size : max M (Q^2/M)≤K*(Q+M) := max_le ((by linarith only [qp] : M≤Q+M).trans one) qk
  exact head.trans ((mul_le_mul_of_nonneg_left size ap).trans_eq (by ring))

end
end ImbalancedChen.Part3.OriginalNativeJInitialRegion20261113
