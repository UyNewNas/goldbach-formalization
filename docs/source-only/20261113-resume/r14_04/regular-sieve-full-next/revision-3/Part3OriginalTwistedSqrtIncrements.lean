import OAI.NumberTheory.EgyptianFractions.DiscreteFirstDerivative
import Mathlib

/-! Consecutive phase increments in the Gram matrix of the actual
square-root twist of the diagonal-cusp Kloosterman sum (Drappeau 4.21).
The n variable runs over the whole interval M,...,2M, including endpoint
increments used by the discrete first-derivative estimate. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalTwistedSqrtIncrements20261113
open Set Complex
open OAI.Problem337.ExponentialSum (phase first_derivative_sum_bound_either_succ)

def step (x : ℝ) : ℝ := (Real.sqrt (x+1)+Real.sqrt x)⁻¹

theorem sqrt_step {x : ℝ} (hx : 0<x) : Real.sqrt (x+1)-Real.sqrt x=step x := by
  have hp := add_pos (Real.sqrt_pos.mpr (show 0<x+1 by linarith)) (Real.sqrt_pos.mpr hx)
  rw [step,←one_div,eq_div_iff hp.ne']
  nlinarith only [Real.sq_sqrt hx.le,Real.sq_sqrt (show 0≤x+1 by linarith)]

private theorem step_antitone {x y : ℝ} (hx : 0<x) (hxy : x≤y) : step y≤step x := by
  rw [step,step,←one_div,←one_div]
  exact one_div_le_one_div_of_le
    (add_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hx))
    (add_le_add (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt hxy))

private theorem root_range {M a : ℝ} (hM : 0<M) (ha : a≤2*M) :
    Real.sqrt a ≤ (17/12)*Real.sqrt M := by
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith only [ha,Real.sq_sqrt hM.le,hM]

private theorem root_diff {M a b : ℝ} (hM : 0<M) (ha : a∈Icc M (2*M)) (hb : b∈Icc M (2*M)) :
    |Real.sqrt a-Real.sqrt b|≤(5/12)*Real.sqrt M := by
  exact abs_le.mpr ⟨by linarith only [Real.sqrt_le_sqrt ha.1,root_range hM hb.2],
    by linarith only [Real.sqrt_le_sqrt hb.1,root_range hM ha.2]⟩

private theorem step_den_pos {x : ℝ} (hx : 0<x) : 0<Real.sqrt (x+1)+Real.sqrt x :=
  add_pos (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_pos.mpr hx)

/-- The difference in the square-root modulation can shift an additive
residue frequency by at most 5/(6c), uniformly on a full dyadic interval. -/
theorem offset_bound {M a b x θ c : ℝ} (hM : 0<M) (hc : 0<c) (ht : θ∈Icc 0 2)
    (ha : a∈Icc M (2*M)) (hb : b∈Icc M (2*M)) (hx : M≤x) :
    |2*θ/c*(Real.sqrt a-Real.sqrt b)*step x|≤(5/6)/c := by
  have rp := Real.sqrt_pos.mpr hM
  have dp := step_den_pos (hM.trans_le hx)
  have base : 2*Real.sqrt M≤Real.sqrt (x+1)+Real.sqrt x := by
    linarith only [Real.sqrt_le_sqrt hx,Real.sqrt_le_sqrt (show M≤x+1 by linarith)]
  rw [abs_mul,abs_mul,abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) ht.1) hc.le),
    abs_of_nonneg (show 0≤step x from inv_nonneg.mpr dp.le),step]
  let D := Real.sqrt (x+1)+Real.sqrt x
  have E : 2*θ/c*|Real.sqrt a-Real.sqrt b|*D⁻¹=
      (2*θ*|Real.sqrt a-Real.sqrt b|)/(c*D) := by
    simp only [div_eq_mul_inv,mul_inv_rev];ring
  change 2*θ/c*|Real.sqrt a-Real.sqrt b|*D⁻¹≤_
  rw [E,div_le_iff₀ (mul_pos hc dp)]
  have F : (5/6/c)*(c*D)=(5/6)*D := by field_simp [hc.ne'] <;>ring
  rw [F]
  have u := mul_le_mul_of_nonneg_left (root_diff hM ha hb) (show 0≤2*θ by linarith [ht.1])
  have v := mul_le_mul_of_nonneg_right ht.2 (show 0≤(5/6)*Real.sqrt M by positivity)
  dsimp only [D]
  nlinarith only [u,v,base]

private theorem den_upper {M x : ℝ} (hM : 1≤M) (hx : x≤2*M) :
    Real.sqrt (x+1)+Real.sqrt x≤4*Real.sqrt M := by
  have posM : 0≤M := by linarith
  have q (v : ℝ) (hv : v≤4*M) : Real.sqrt v≤2*Real.sqrt M :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [Real.sq_sqrt posM,hv]⟩
  linarith only [q (x+1) (by linarith),q x (by linarith)]

/-- With one fixed residue, distinct c-blocks have frequency separation
proportional to θ times their index separation divided by M. -/
theorem offset_lower {M a b x θ c d : ℝ} (hM : 1≤M) (hc : 0<c) (ht : 0<θ)
    (ha : a∈Icc M (2*M)) (hb : b∈Icc M (2*M)) (hx : x∈Icc M (2*M))
    (hd : 0<d) (sep : a-b=c*d) :
    θ*d/(12*M)≤2*θ/c*(Real.sqrt a-Real.sqrt b)*step x := by
  let A := Real.sqrt a+Real.sqrt b
  let X := Real.sqrt (x+1)+Real.sqrt x
  have mp : 0<M := zero_lt_one.trans_le hM
  have ap : 0<A := add_pos (Real.sqrt_pos.mpr (mp.trans_le ha.1)) (Real.sqrt_pos.mpr (mp.trans_le hb.1))
  have xp : 0<X := step_den_pos (mp.trans_le hx.1)
  have r (v : ℝ) (hv : v≤2*M) : Real.sqrt v≤2*Real.sqrt M := by
    linarith only [root_range mp hv,Real.sqrt_nonneg M]
  have a4 : A≤4*Real.sqrt M := by dsimp [A];linarith only [r a ha.2,r b hb.2]
  have x4 : X≤4*Real.sqrt M := den_upper hM hx.2
  have prod : A*X≤16*M := by
    have := mul_le_mul a4 x4 xp.le (show 0≤4*Real.sqrt M by positivity)
    nlinarith only [this,Real.sq_sqrt mp.le]
  have diff : Real.sqrt a-Real.sqrt b=c*d/A := by
    apply (eq_div_iff ap.ne').mpr
    dsimp only [A]
    nlinarith only [Real.sq_sqrt (mp.trans_le ha.1).le,Real.sq_sqrt (mp.trans_le hb.1).le,sep]
  have E : 2*θ/c*(Real.sqrt a-Real.sqrt b)*step x=(2*(θ*d))/(A*X) := by
    rw [diff]
    change 2*θ/c*(c*d/A)*X⁻¹=_
    field_simp [hc.ne',ap.ne',xp.ne'] <;>ring
  rw [E,div_le_div_iff₀ (by positivity) (mul_pos ap xp)]
  have u := mul_le_mul_of_nonneg_left prod (mul_nonneg ht.le hd.le)
  have v := mul_nonneg (mul_nonneg ht.le hd.le) mp.le
  nlinarith only [u,v]

def angle (c : ℝ) (θ a b d : ℝ) (M i : ℕ) : ℝ :=
  d/c*(M+i:ℕ)+2*θ/c*(Real.sqrt a-Real.sqrt b)*Real.sqrt (M+i:ℕ)

theorem increment {c θ a b d : ℝ} {M : ℕ} (hM : 0<M) (i : ℕ) :
    angle c θ a b d M (i+1)-angle c θ a b d M i =
      d/c+2*θ/c*(Real.sqrt a-Real.sqrt b)*step (M+i:ℕ) := by
  have hp : 0<((M+i:ℕ):ℝ) := by exact_mod_cast (show 0<M+i by omega)
  have sr := sqrt_step hp
  simp only [angle,Nat.cast_add,Nat.cast_one] at sr ⊢
  simp only [←add_assoc (M:ℝ) (i:ℝ) 1]
  linear_combination (2*θ/c*(Real.sqrt a-Real.sqrt b))*sr

theorem monotone_increments {c θ a b d : ℝ} {M : ℕ} (hM : 0<M) :
    Monotone (fun i => angle c θ a b d M (i+1)-angle c θ a b d M i) ∨
    Antitone (fun i => angle c θ a b d M (i+1)-angle c θ a b d M i) := by
  let B := 2*θ/c*(Real.sqrt a-Real.sqrt b)
  have down {i j : ℕ} (hij : i≤j) : step (M+j:ℕ)≤step (M+i:ℕ) := step_antitone
    (by exact_mod_cast (show 0<M+i by omega)) (by exact_mod_cast Nat.add_le_add_left hij M)
  rcases le_total 0 B with h|h
  · right;intro i j hij
    simp only [increment hM]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (down hij) h) _
  · left;intro i j hij
    simp only [increment hM]
    exact add_le_add_right (mul_le_mul_of_nonpos_left (down hij) h) _

def kernel (c θ a b d : ℝ) (M : ℕ) : ℂ :=
  ∑ i∈Finset.range (M+1),phase (angle c θ a b d M i)

private theorem derivative_bound {c θ a b d β : ℝ} {M : ℕ} (hM : 0<M) (hβ : 0<β)
    (bounds : ∀ i≤M, β≤d/c+2*θ/c*(Real.sqrt a-Real.sqrt b)*step (M+i:ℕ) ∧
      d/c+2*θ/c*(Real.sqrt a-Real.sqrt b)*step (M+i:ℕ)≤1-β) :
    ‖kernel c θ a b d M‖≤2/β := by
  apply first_derivative_sum_bound_either_succ (angle c θ a b d M) M β 0 hβ
  · intro i hi
    simpa only [Int.cast_zero,zero_add,increment hM] using (bounds i hi).1
  · intro i hi
    simpa only [Int.cast_zero,zero_add,increment hM] using (bounds i hi).2
  · exact (monotone_increments hM).imp Monotone.monotoneOn Antitone.antitoneOn

/-- Distinct additive residues, with their full cyclic distance to either
end of the additive frequency interval. -/
theorem kernel_residue {M : ℕ} (hM : 0<M) {c θ a b d : ℝ} (hc : 0<c)
    (ht : θ∈Icc 0 2) (ha : a∈Icc (M:ℝ) (2*M)) (hb : b∈Icc (M:ℝ) (2*M))
    (hd : 1≤d) (hd' : 1≤c-d) :
    ‖kernel c θ a b d M‖≤12*c/min d (c-d) := by
  let D := min d (c-d)
  have D1 : 1≤D := le_min hd hd'
  have Dp : 0<D := zero_lt_one.trans_le D1
  have DL : D≤d := min_le_left _ _
  have DR : D≤c-d := min_le_right _ _
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have H := derivative_bound (θ:=θ) (a:=a) (b:=b) (d:=d) hM
    (show 0<D/(6*c) by positivity) (by
      intro i hi
      let u := 2*θ/c*(Real.sqrt a-Real.sqrt b)*step (M+i:ℕ)
      have U := abs_le.mp (offset_bound mp hc ht ha hb
        (show (M:ℝ)≤((M+i:ℕ):ℝ) by exact_mod_cast Nat.le_add_right M i))
      have lo : -(5/6)/c≤u := by simpa only [neg_div] using U.1
      have hi' : u≤(5/6)/c := U.2
      change D/(6*c)≤d/c+u ∧ d/c+u≤1-D/(6*c)
      have low : -(5/6)≤u*c := (div_le_iff₀ hc).mp lo
      have high : u*c≤5/6 := (le_div_iff₀ hc).mp hi'
      constructor
      · apply (div_le_iff₀ (show 0<6*c by positivity)).mpr
        have E : (d/c+u)*(6*c)=6*d+6*(u*c) := by field_simp [hc.ne'] <;>ring
        rw [E]
        linarith only [low,DL,D1]
      · apply (mul_le_mul_iff_left₀ hc).mp
        have E : (d/c+u)*c=d+u*c := by field_simp [hc.ne'] <;>ring
        have F : (1-D/(6*c))*c=c-D/6 := by field_simp [hc.ne'] <;>ring
        rw [E,F]
        nlinarith only [high,DR,D1])
  convert H using 1 <;> field_simp [hc.ne',Dp.ne'] <;>ring

/-- Equal additive residue and distinct c-blocks. The parameter d is the
positive distance of their block indices. -/
theorem kernel_block {M : ℕ} (hM : 0<M) {c θ a b d : ℝ} (hc : 1≤c)
    (ht : 0<θ) (ht' : θ≤2) (ha : a∈Icc (M:ℝ) (2*M))
    (hb : b∈Icc (M:ℝ) (2*M)) (hd : 0<d) (hd' : d≤M) (sep : a-b=c*d) :
    ‖kernel c θ a b 0 M‖≤24*M/(θ*d) := by
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have m1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have cp := zero_lt_one.trans_le hc
  have H := derivative_bound (c:=c) (θ:=θ) (a:=a) (b:=b) (d:=0) hM
    (show 0<θ*d/(12*M) by positivity) (by
      intro i hi
      have hx : ((M+i:ℕ):ℝ)∈Icc (M:ℝ) (2*M) :=
        ⟨by exact_mod_cast Nat.le_add_right M i,by exact_mod_cast (show M+i≤2*M by omega)⟩
      simp only [zero_div,zero_add]
      refine ⟨offset_lower m1 cp ht ha hb hx hd sep,?_⟩
      have U := (abs_le.mp (offset_bound mp cp ⟨ht.le,ht'⟩ ha hb hx.1)).2
      have V : (5/6)/c≤5/6 := (div_le_iff₀ cp).mpr (by linarith only [hc])
      have W : θ*d/(12*M)≤1/6 := (div_le_iff₀ (by positivity)).mpr (by
        have := mul_le_mul_of_nonneg_right ht' hd.le
        linarith only [this,hd'])
      linarith only [U,V,W])
  convert H using 1 <;>field_simp [mp.ne',ht.ne',hd.ne'] <;>ring

end ImbalancedChen.Part3.OriginalTwistedSqrtIncrements20261113
end
