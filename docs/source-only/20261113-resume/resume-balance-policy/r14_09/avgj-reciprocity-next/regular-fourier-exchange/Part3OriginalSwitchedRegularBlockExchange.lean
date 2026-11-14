import ImbalancedChen.Part3OriginalSwitchedRegularRows

/-! Both complete real-parameter sectors of the reflected trace,
including their exact order of summation and the full signed t-axis. -/
namespace ImbalancedChen.Part3.OriginalSwitchedRegularBlockExchange20261113
noncomputable section
open Finset Complex MeasureTheory
open scoped BigOperators Classical
open OriginalSwitchedRegularMarkExchange20261113
open OriginalSwitchedRegularRows20261113 (amplitude D E discrete_rows incoming_rows)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open private mark from ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open ActualFullCuspEigenbasis20261026b
open P3NativePeriod64SamplingSourceOnly (D4)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

def principalBlock (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude u ω m.val n.val*
    principal d (mark m) (mark n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)

def incomingBlock (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (u : ℕ→ℂ) :=
  ∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude u ω m.val n.val*
    incoming d (mark m) (mark n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)

theorem principal_fourier (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (y1 : 1≤Y) (qp : 0<Q) (u : ℕ→ℂ) :
    let Idx := actualCuspBasisIndex d.val (NeZero.pos d.val)
    Summable (fun z : (D4→ℤ)×Idx => ‖D d j Y Q ω u z.1 z.2‖) ∧
    HasSum (fun k => ∑' i,D d j Y Q ω u k i) (principalBlock d j Y Q ω u) := by
  let Idx := actualCuspBasisIndex d.val (NeZero.pos d.val)
  let I := ↥(dyadicWindow j)
  let A := fun (m n : I) => amplitude u ω m.val n.val
  let F := fun (m n : I) => discreteMode d (mark m) (mark n) j Y Q
  have per (m n : I) := discrete_exchange d (mark m) (mark n) m.property n.property y1 qp
  have sf (m n : I) : Summable (Function.uncurry (F m n)) := Summable.of_norm (per m n).1
  have joint := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => ((sf m n).hasSum.mul_left (A m n))))
  have sums : Summable (fun z : (D4→ℤ)×Idx => D d j Y Q ω u z.1 z.2) := by
    apply (joint.congr_fun ?_).summable
    exact fun z => (discrete_rows d j Y Q ω u z.1 z.2).symm
  refine ⟨sums.norm,?_⟩
  have full := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => (per m n).2.mul_left (A m n)))
  apply full.congr_fun
  intro k
  have each (m n : I) : HasSum (fun i => A m n*F m n k i) (A m n*(∑' i,F m n k i)) :=
    ((sf m n).prod_factor k).hasSum.mul_left _
  have h := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => each m n))
  exact (h.congr_fun (fun i => (discrete_rows d j Y Q ω u k i).symm)).tsum_eq

theorem incoming_fourier (d : ℕ+) (j : ℕ) (Y Q ω : ℝ) (y1 : 1≤Y) (qp : 0<Q) (u : ℕ→ℂ) :
    (∀ k,Integrable (E d j Y Q ω u k)) ∧ Summable (fun k => ∫ t : ℝ,‖E d j Y Q ω u k t‖) ∧
    HasSum (fun k => ∫ t : ℝ,E d j Y Q ω u k t) (incomingBlock d j Y Q ω u) := by
  let I := ↥(dyadicWindow j)
  let A := fun (m n : I) => amplitude u ω m.val n.val
  let F := fun (m n : I) => incomingMode d (mark m) (mark n) j Y Q
  have per (m n : I) := continuous_exchange d (mark m) (mark n) m.property n.property y1 qp
  have g (k : D4→ℤ) : E d j Y Q ω u k=fun t => ∑ m : I,∑ n : I,A m n*F m n k t :=
    funext (fun t => (incoming_rows d j Y Q ω u k t).symm)
  have gi (k : D4→ℤ) : Integrable (E d j Y Q ω u k) := by
    rw [g]
    exact integrable_finsetSum univ (fun m _ => integrable_finsetSum univ
      (fun n _ => ((per m n).1 k).const_mul _))
  let M := fun (m n : I) (k : D4→ℤ) (t : ℝ) => ‖A m n‖*‖F m n k t‖
  have mi (m n : I) (k : D4→ℤ) : Integrable (M m n k) := ((per m n).1 k).norm.const_mul _
  have mh (k : D4→ℤ) (t : ℝ) : ‖E d j Y Q ω u k t‖≤∑ m : I,∑ n : I,M m n k t := by
    rw [g]
    exact (norm_sum_le _ _).trans (sum_le_sum (fun m _ => by simpa only [M,norm_mul] using
      norm_sum_le (univ:Finset I) (fun n => A m n*F m n k t)))
  have mval (m : I) (k : D4→ℤ) : (∫ t,∑ n : I,M m n k t)=∑ n : I,∫ t,M m n k t :=
    integral_finsetSum univ (fun n _ => mi m n k)
  have vs (m n : I) : Summable (fun k => ∫ t,M m n k t) := by
    simpa only [M,integral_const_mul] using (per m n).2.1.mul_left ‖A m n‖
  have large := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => (vs m n).hasSum))
  have normSum : Summable (fun k => ∫ t : ℝ,‖E d j Y Q ω u k t‖) := by
    apply large.summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
    intro k
    have big := integrable_finsetSum univ (fun m (_ : m∈(univ:Finset I)) => integrable_finsetSum univ
      (fun n (_ : n∈(univ:Finset I)) => mi m n k))
    have h := integral_mono (gi k).norm big (mh k)
    rw [integral_finsetSum univ (fun m _ => integrable_finsetSum univ (fun n _ => mi m n k))] at h
    simpa only [mval] using h
  refine ⟨gi,normSum,?_⟩
  have total := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
    (fun n (_ : n∈(univ:Finset I)) => (per m n).2.2.mul_left (A m n)))
  apply total.congr_fun
  intro k
  rw [g,integral_finsetSum univ (fun m _ => integrable_finsetSum univ (fun n _ => ((per m n).1 k).const_mul (A m n)))]
  apply sum_congr rfl
  intro m _
  rw [integral_finsetSum univ (fun n _ => ((per m n).1 k).const_mul (A m n))]
  simp only [integral_const_mul]

end
end ImbalancedChen.Part3.OriginalSwitchedRegularBlockExchange20261113
