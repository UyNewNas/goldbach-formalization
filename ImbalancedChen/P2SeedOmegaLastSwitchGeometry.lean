import ImbalancedChen.P2SeedOmegaLiteralFunctional
import MathlibNt.Wu2008DoubleSieve.GeoMassOrderedPure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original switched domains20/21, including their distinct quotient-one
surfaces. No unit surface is identified with a null subset of a higher
dimensional integral. Omega's elementary [0,1] envelope is an explicit
primitive input; the prime-count asymptotic licence remains OPEN.
-/

namespace ImbalancedChen.P2SeedOmegaLastSwitchGeometry
noncomputable section
open Set MeasureTheory Classical
open scoped BigOperators
open P2SeedOmegaLiteralFibre (a2 a3 b phi2 phi3 s)

abbrev orderedBand := Wu2008DoubleSieve.SecondFunctionalGeometricMass.orderedDomain
def D20 : Set (Fin 5 → ℝ) :=
  {x | x 0 ∈ Icc a2 a3 ∧ (fun i : Fin 4 => x i.succ) ∈ orderedBand 4 a3 b}
def D21 : Set (Fin 6 → ℝ) := orderedBand 6 a3 b
def total {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i,x i
def reciprocal {n : ℕ} (x : Fin n → ℝ) : ℝ := 1/(∏ i,x i)
def w20 (x : Fin 5 → ℝ) : ℝ := x 3
def w21 (x : Fin 6 → ℝ) : ℝ := x 4
def nonunitKernel {n : ℕ} (ω : ℝ → ℝ) (alpha w : ℝ) (x : Fin n → ℝ) : ℝ :=
  if total x≤alpha-w then ω ((alpha-total x)/w)/(w*(∏ i,x i)) else 0

def eliminated {n : ℕ} (alpha : ℝ) (y : Fin n → ℝ) : ℝ := alpha-total y
def unit20Point (alpha : ℝ) (y : Fin 4 → ℝ) : Fin 5 → ℝ := Fin.cons (eliminated alpha y) y
def unit21Point (alpha : ℝ) (y : Fin 5 → ℝ) : Fin 6 → ℝ := Fin.snoc y (eliminated alpha y)
def unit20Domain (alpha : ℝ) : Set (Fin 4 → ℝ) :=
  {y | y ∈ orderedBand 4 a3 b ∧ eliminated alpha y ∈ Icc a2 a3}
def unit21Domain (alpha : ℝ) : Set (Fin 5 → ℝ) :=
  {y | y ∈ orderedBand 5 a3 b ∧ eliminated alpha y ∈ Icc a3 b ∧
    ∀ i,y i≤eliminated alpha y}
def unitKernel {n : ℕ} (alpha : ℝ) (y : Fin n → ℝ) : ℝ :=
  1/(eliminated alpha y*(∏ i,y i))

theorem D20_coordinate_bounds {x : Fin 5 → ℝ} (hx : x ∈ D20) (i : Fin 5) :
    a2≤x i ∧ x i≤b := by
  rcases hx with ⟨hx0,ht⟩
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨hx0.1,hx0.2.trans (by norm_num [a3,b])⟩
  · exact ⟨(by norm_num [a2,a3] : a2≤a3).trans (ht.1 j).1,(ht.1 j).2⟩

theorem D21_coordinate_bounds {x : Fin 6 → ℝ} (hx : x ∈ D21) (i : Fin 6) :
    a3≤x i ∧ x i≤b := hx.1 i

theorem D20_next_to_last {x : Fin 5 → ℝ} (hx : x ∈ D20) : a3≤w20 x :=
  (hx.2.1 (2 : Fin 4)).1
theorem D21_next_to_last {x : Fin 6 → ℝ} (hx : x ∈ D21) : a3≤w21 x :=
  (hx.1 (4 : Fin 6)).1

theorem reciprocal_pos {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i,0<x i) : 0<reciprocal x :=
  one_div_pos.mpr (Finset.prod_pos (fun i _ => hx i))

/-- The actual rough argument is at least one exactly on the retained
nonunit quotient region. No alpha reset occurs. -/
theorem rough_argument_ge_one {n : ℕ} {alpha w : ℝ} {x : Fin n → ℝ}
    (hw : 0<w) (hx : total x≤alpha-w) : 1≤(alpha-total x)/w := by
  apply (le_div_iff₀ hw).mpr
  linarith only [hx]

theorem nonunitKernel_bounds {n : ℕ} (ω : ℝ → ℝ)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) {alpha w : ℝ} {x : Fin n → ℝ}
    (hx : ∀ i,0<x i) (hw : a3≤w) :
    0≤nonunitKernel ω alpha w x ∧ nonunitKernel ω alpha w x≤phi3*reciprocal x := by
  have hw0 : 0<w := lt_of_lt_of_le (by norm_num [a3]) hw
  have hP : 0<∏ i,x i := Finset.prod_pos (fun i _ => hx i)
  have hr := reciprocal_pos hx
  have hinv : 1/w≤phi3 := by
    have h := one_div_le_one_div_of_le (by norm_num [a3] : 0<a3) hw
    norm_num [a3,phi3] at h ⊢
    exact h
  unfold nonunitKernel
  split_ifs with hcut
  · have hh := hω _ (rough_argument_ge_one hw0 hcut)
    refine ⟨div_nonneg hh.1 (mul_pos hw0 hP).le,?_⟩
    calc
      _ ≤ 1/(w*(∏ i,x i)) := div_le_div_of_nonneg_right hh.2 (mul_pos hw0 hP).le
      _ = (1/w)*reciprocal x := by unfold reciprocal; field_simp; ring
      _ ≤ phi3*reciprocal x := mul_le_mul_of_nonneg_right hinv hr.le
  · exact ⟨le_rfl,mul_nonneg (by norm_num [phi3]) hr.le⟩

theorem nonunit20_bounds (ω : ℝ → ℝ)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ)
    {x : Fin 5 → ℝ} (hx : x ∈ D20) :
    0≤nonunitKernel ω alpha (w20 x) x ∧
      nonunitKernel ω alpha (w20 x) x≤phi3*reciprocal x :=
  nonunitKernel_bounds ω hω (fun i => lt_of_lt_of_le (by norm_num [a2])
    (D20_coordinate_bounds hx i).1) (D20_next_to_last hx)

theorem nonunit21_bounds (ω : ℝ → ℝ)
    (hω : ∀ t,1≤t → 0≤ω t ∧ ω t≤1) (alpha : ℝ)
    {x : Fin 6 → ℝ} (hx : x ∈ D21) :
    0≤nonunitKernel ω alpha (w21 x) x ∧
      nonunitKernel ω alpha (w21 x) x≤phi3*reciprocal x :=
  nonunitKernel_bounds ω hω (fun i => lt_of_lt_of_le (by norm_num [a3])
    (D21_coordinate_bounds hx i).1) (D21_next_to_last hx)

theorem unit20_reconstruct {alpha : ℝ} {y : Fin 4 → ℝ}
    (hy : y ∈ unit20Domain alpha) : unit20Point alpha y ∈ D20 := by
  simpa [unit20Point,D20] using And.intro hy.2 hy.1

theorem unit21_reconstruct {alpha : ℝ} {y : Fin 5 → ℝ}
    (hy : y ∈ unit21Domain alpha) : unit21Point alpha y ∈ D21 := by
  apply (Wu2008DoubleSieve.SecondFunctionalGeometricMass.OrderedPure.mem_orderedDomain_snoc
    a3 b (eliminated alpha y) y).mpr
  exact ⟨hy.2.1,⟨fun i => ⟨(hy.1.1 i).1,hy.2.2 i⟩,hy.1.2⟩⟩

theorem unit20_total (alpha : ℝ) (y : Fin 4 → ℝ) : total (unit20Point alpha y)=alpha := by
  simp [total,unit20Point,eliminated,Fin.sum_univ_succ]

theorem unit21_total (alpha : ℝ) (y : Fin 5 → ℝ) : total (unit21Point alpha y)=alpha := by
  simp [total,unit21Point,eliminated,Fin.sum_univ_castSucc]

theorem unit20_density_identity (alpha : ℝ) (y : Fin 4 → ℝ) :
    reciprocal (unit20Point alpha y)=unitKernel alpha y := by
  simp [reciprocal,unitKernel,unit20Point,Fin.prod_univ_succ]

theorem unit21_density_identity (alpha : ℝ) (y : Fin 5 → ℝ) :
    reciprocal (unit21Point alpha y)=unitKernel alpha y := by
  simp [reciprocal,unitKernel,unit21Point,Fin.prod_univ_castSucc,mul_comm]

theorem unitKernel_bounds {n : ℕ} {alpha lo bound : ℝ} {y : Fin n → ℝ}
    (hy : ∀ i,0<y i) (hlo : 0<lo) (hq : lo≤eliminated alpha y)
    (hbound : 1/lo=bound) :
    0≤unitKernel alpha y ∧ unitKernel alpha y≤bound*reciprocal y := by
  have hq0 := hlo.trans_le hq
  have hP : 0<∏ i,y i := Finset.prod_pos (fun i _ => hy i)
  have hinv : 1/(eliminated alpha y)≤bound := by
    rw [← hbound]
    exact one_div_le_one_div_of_le hlo hq
  refine ⟨(one_div_pos.mpr (mul_pos hq0 hP)).le,?_⟩
  calc
    _ = (1/(eliminated alpha y))*reciprocal y := by unfold unitKernel reciprocal; field_simp; ring
    _ ≤ bound*reciprocal y := mul_le_mul_of_nonneg_right hinv (reciprocal_pos hy).le

theorem unit20_bounds {alpha : ℝ} {y : Fin 4 → ℝ} (hy : y ∈ unit20Domain alpha) :
    0≤unitKernel alpha y ∧ unitKernel alpha y≤phi2*reciprocal y :=
  unitKernel_bounds (fun i => lt_of_lt_of_le (by norm_num [a3]) (hy.1.1 i).1)
    (by norm_num [a2]) hy.2.1 (by norm_num [a2,phi2])

theorem unit21_bounds {alpha : ℝ} {y : Fin 5 → ℝ} (hy : y ∈ unit21Domain alpha) :
    0≤unitKernel alpha y ∧ unitKernel alpha y≤phi3*reciprocal y :=
  unitKernel_bounds (fun i => lt_of_lt_of_le (by norm_num [a3]) (hy.1.1 i).1)
    (by norm_num [a3]) hy.2.1.1 (by norm_num [a3,phi3])

/-- Same-Q exponent conservation and physical ceiling of every retained
prime. The positive quotient condition is retained as its own gate. -/
theorem physical20 {L chi alpha : ℝ} (hL : 0<L) (hchi : L/s<chi)
    {x : Fin 5 → ℝ} (hx : x ∈ D20) :
    L*(alpha-total x)+L*total x=L*alpha ∧
    (∀ i,0<L*x i ∧ L*x i≤L/s ∧ L*x i<chi) ∧
    (total x≤alpha-w20 x → L*w20 x≤L*(alpha-total x)) := by
  refine ⟨by ring,?_,?_⟩
  · intro i
    have h := D20_coordinate_bounds hx i
    have hp : 0<L*x i := mul_pos hL (lt_of_lt_of_le (by norm_num [a2]) h.1)
    have hc : L*x i≤L/s := by
      have hm := mul_le_mul_of_nonneg_left h.2 hL.le
      convert hm using 1 <;> norm_num [b,s] <;> ring
    exact ⟨hp,hc,hc.trans_lt hchi⟩
  · intro h
    exact mul_le_mul_of_nonneg_left (by linarith only [h]) hL.le

theorem physical21 {L chi alpha : ℝ} (hL : 0<L) (hchi : L/s<chi)
    {x : Fin 6 → ℝ} (hx : x ∈ D21) :
    L*(alpha-total x)+L*total x=L*alpha ∧
    (∀ i,0<L*x i ∧ L*x i≤L/s ∧ L*x i<chi) ∧
    (total x≤alpha-w21 x → L*w21 x≤L*(alpha-total x)) := by
  refine ⟨by ring,?_,?_⟩
  · intro i
    have h := D21_coordinate_bounds hx i
    have hp : 0<L*x i := mul_pos hL (lt_of_lt_of_le (by norm_num [a3]) h.1)
    have hc : L*x i≤L/s := by
      have hm := mul_le_mul_of_nonneg_left h.2 hL.le
      convert hm using 1 <;> norm_num [b,s] <;> ring
    exact ⟨hp,hc,hc.trans_lt hchi⟩
  · intro h
    exact mul_le_mul_of_nonneg_left (by linarith only [h]) hL.le

end
end ImbalancedChen.P2SeedOmegaLastSwitchGeometry
