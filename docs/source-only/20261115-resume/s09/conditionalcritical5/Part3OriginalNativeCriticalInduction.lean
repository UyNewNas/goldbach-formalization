import ImbalancedChen.Part3OriginalNativeCriticalChild
import ImbalancedChen.Part3OriginalNativeSixWindowMean
import ImbalancedChen.Part3OriginalFullPositiveInitialMean

/-! Critical-weight induction on real level scales. Its sole external
mathematical premise is the positive half-order coefficient support. -/
namespace ImbalancedChen.Part3.OriginalNativeCriticalInduction20261113
noncomputable section
open Finset Real
open scoped Classical BigOperators
open OriginalNativeCriticalPrices20261113 (height benchmark normPrice)
open OriginalNativeCriticalTransport20261113 (positiveHalfSupport transport prefix_child)
open OriginalNativeCriticalChild20261113 (child)
open OriginalNativeSixWindowMean20261113 (six_window_mean)
open OriginalFullPositiveInitialMean20261113 (initial_mean)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalSwitchedActiveLevels20261113 (outScale)
open OriginalSwitchedScaleContraction20261113 (kappa lambda endpoint actual_scales recursive_band choose_damping)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)

theorem critical (coeff : positiveHalfSupport) {ε : ℝ} (ep : 0<ε) :
    ∃ P : ℝ,0<P ∧ ∀ (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b), b≤2^(j+1) →
    ∀ (Q ω : ℝ),0<Q → let M := classicalMScale j
    intervalEnergy (classicalLevels Q) (benchmark M Q) ω a b 0≤P*normPrice M Q ε := by
  let δ := ε/2
  have dp : 0<δ := half_pos ep
  obtain ⟨A,E,X,ap,epos,x1,R⟩ := six_window_mean dp
  obtain ⟨K,kp,I⟩ := initial_mean dp
  let A₀ := max 1 (6*A)
  obtain ⟨D,dpos,d1,d2,damp⟩ := choose_damping A₀ (le_max_left _ _) ep
  have k1 : 1≤kappa := by dsimp only [kappa];linarith only [Real.pi_gt_three]
  have d : 1≤D := (by nlinarith only [k1,sq_nonneg (kappa-1)] : 1≤kappa^2).trans d1
  have lp : 0<lambda := div_pos Real.pi_pos (by norm_num)
  let T := max 1 (max (D/lambda) (Real.sqrt (D*X)))
  have t1 : 1≤T := le_max_left _ _
  have t2 : D/lambda≤T := (le_max_left _ _).trans (le_max_right _ _)
  have t3 : Real.sqrt (D*X)≤T := (le_max_right _ _).trans (le_max_right _ _)
  let c := 1+2*T^2
  let U := K*((2*(1+c))^δ*(1+2*c))
  let V := Real.sqrt D*E*(2*(6:ℝ)^δ)
  let P := max U (2*V)
  have cp : 0<c := by dsimp only [c];positivity
  have up : 0<U := by dsimp only [U];positivity
  have pp := up.trans_le (show U≤P from le_max_left _ _)
  have bd : 2*(6*A)*(kappa/D)^ε≤1/2 := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_max_right 1 (6*A)) (by norm_num : (0:ℝ)≤2))
    (Real.rpow_nonneg (div_nonneg (zero_le_one.trans k1) dpos.le) _)).trans damp
  refine ⟨P,pp,fun j => ?_⟩
  let M := classicalMScale j
  let H := height M
  have hm : 1/2≤M := (classicalMScale_bounds j).1
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le hm
  have h1 : 1≤H := le_max_left _ _
  have mh : M≤H := le_max_right _ _
  have hp := zero_lt_one.trans_le h1
  let good (Q : ℝ) := ∀ (a b : ℕ),2^j≤a → a≤b → b≤2^(j+1) → ∀ ω : ℝ,
    intervalEnergy (classicalLevels Q) (benchmark M Q) ω a b 0≤P*normPrice M Q ε
  have go (n : ℕ) : ∀ Q : ℝ,0<Q → Q≤(2:ℝ)^n*(T*H) → good Q := by
    induction n with
    | zero =>
      intro Q qp low a b lo ab hi ω
      rw [pow_zero,one_mul] at low
      have wp : 0<benchmark M Q := hp.trans_le (le_max_left _ _)
      have N : 0≤normPrice M Q ε := by dsimp only [normPrice];positivity
      have z := I j a b lo ab hi Q (benchmark M Q) ω qp wp
      have cost := OriginalNativeCriticalPrices20261113.base hm qp ep low
      apply z.trans ((mul_le_mul_of_nonneg_left cost kp.le).trans ?_)
      exact (show K*((2*(1+c))^δ*(1+2*c)*normPrice M Q ε)=U*normPrice M Q ε by dsimp only [U];ring).le.trans
        (mul_le_mul_of_nonneg_right (le_max_left U (2*V)) N)
    | succ n ih =>
      intro Q qp low
      by_cases prev : Q≤(2:ℝ)^n*(T*H)
      · exact ih Q qp prev
      have two : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
      have unit : T*H≤(2:ℝ)^n*(T*H) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right two (mul_nonneg (zero_le_one.trans t1) hp.le)
      have band : T*H<Q := unit.trans_lt (lt_of_not_ge prev)
      have hq : H≤Q := (by simpa only [one_mul] using mul_le_mul_of_nonneg_right t1 hp.le).trans band.le
      have q1 := h1.trans hq
      have sq : H≤Q^2/M := (le_div_iff₀ mp).mpr (by nlinarith only [mul_le_mul hq (mh.trans hq) mp.le qp.le])
      have wq : benchmark M Q=Q^2/M := max_eq_right sq
      let Z := Q^2/(D*M)
      let W := Q^2/M
      let O := outScale j Z Q
      have wz : W/Z=D := by dsimp only [W,Z];field_simp [qp.ne',mp.ne',dpos.ne'] <;> ring
      have zp : 0<Z := by dsimp only [Z];positivity
      have ord : Z≤W := by
        have rel : (1:ℝ)≤W/Z := d.trans wz.ge
        simpa only [one_mul] using (le_div_iff₀ zp).mp rel
      have cap (l : ℕ) (hl : l∈range 6) :
          X≤Z ∧ H≤O l ∧ O l≤Q/2 ∧ (O l)^2/M≤Z ∧ O l≤kappa*(Q/D) := by
        let i : Fin 6 := ⟨l,mem_range.mp hl⟩
        have u := actual_scales j qp dpos (0:Fin 4) i
        have id : endpoint j Z Q 0 i=O l := by simp only [endpoint,Fin.val_zero,pow_zero,one_mul,outScale,O,i]
        change lambda*(Q/D)≤endpoint j Z Q 0 i ∧ endpoint j Z Q 0 i≤kappa*(Q/D) at u
        rw [id] at u
        have r := recursive_band mp x1 dpos d1 d2 t1 t2 t3 band u.1 u.2
        exact ⟨r.1,r.2.1,r.2.2.1,r.2.2.2,u.2⟩
      have xz := (cap 0 (by decide)).1
      intro a b lo ab hi ω
      let ap₀ := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
      let f (l : ℕ) := prefixMax (classicalLevels (O l)) Z ω a b ab
      let N := normPrice M Q ε
      have nn : 0≤N := by dsimp only [N,normPrice];positivity
      have fcap (l : ℕ) (hl : l∈range 6) : Real.sqrt D*A*f l≤P*N/12 := by
        have e := cap l hl
        have bpos := hp.trans_le e.2.1
        have bound : O l≤(2:ℝ)^n*(T*H) := e.2.2.1.trans (by rw [pow_succ] at low;nlinarith only [low])
        have p := prefix_child coeff j a b lo ab e.2.1 e.2.2.2.1 ω
          (p:=P) (ε:=ε) (fun u au ub => ih (O l) bpos bound a u lo au (ub.trans hi) ω)
        have budget := child ap.le bpos dpos mp qp ep pp.le e.2.1 e.2.2.2.2 q1 bd
        rw [wz] at budget
        exact (mul_le_mul_of_nonneg_left p (mul_nonneg (Real.sqrt_nonneg _) ap.le)).trans budget
      have all := sum_le_sum fcap
      rw [←Finset.mul_sum] at all
      simp only [sum_const,card_range,nsmul_eq_mul,Nat.cast_ofNat] at all
      have first := transport coeff (classicalLevels Q) zp ord ω ap₀ b
      rw [wz] at first
      have raw := R Z xz Q ω qp j a b lo ab hi
      have err := OriginalNativeCriticalPrices20261113.recursive (M:=M) (Q:=Q) (D:=D) hm q1 d ep (x1.trans xz)
      have add := mul_le_mul_of_nonneg_left err (mul_nonneg (Real.sqrt_nonneg _) epos.le)
      have p2 := mul_le_mul_of_nonneg_right (show 2*V≤P from le_max_right _ _) nn
      rw [wq]
      apply first.trans ((mul_le_mul_of_nonneg_left raw (Real.sqrt_nonneg _)).trans ?_)
      change Real.sqrt D*(A*(∑ l∈range 6,f l)+E*((1+M)*(1+Z))^δ*(Q+M+M*Z/Q)*M)≤P*N
      change Real.sqrt D*A*(∑ l∈range 6,f l)≤6*(P*N/12) at all
      change (Real.sqrt D*E)*(((1+M)*(1+Z))^δ*(Q+M+M*Z/Q)*M)≤(Real.sqrt D*E)*(2*6^δ*N) at add
      dsimp only [V] at p2
      nlinarith only [all,add,p2]
  intro a b lo ab hi Q ω qp
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (Q/(T*H)) (by norm_num : (1:ℝ)<2)
  have pos := mul_pos (zero_lt_one.trans_le t1) hp
  exact go n Q qp ((div_lt_iff₀ pos).mp hn).le a b lo ab hi ω

end
end ImbalancedChen.Part3.OriginalNativeCriticalInduction20261113

