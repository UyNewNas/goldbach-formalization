import ImbalancedChen.Part3OriginalSwitchedTraceProjection

/-! The equality of the two complete same-infinity traces including
all four native sectors on each side, on the exact same short interval. -/
namespace ImbalancedChen.Part3.OriginalSwitchedIntervalLevelSwitch20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open OriginalSwitchedTraceProjection20261113 (pair all E R C H interval_split)
open OriginalSwitchedLevelIdentity20261113 (spectral single levelWeight level_switch)
open OriginalSwitchedExceptionalTransform20261113 (switchedTest)
open OriginalSwitchedHolTraceError20261113 (test)
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open ActualIntervalGeometricSumSourceOnly (phaseAt)

theorem interval_level_switch {a : ℕ} (ap : 0<a) (b : ℕ) {Y Q : ℝ} (yp : 0<Y) (qp : 0<Q) (ω : ℝ) :
    HasSum (fun d : ℕ+ => all true d ap b Y Q ω) (∑' q : ℕ+,levelWeight Q q*all false q ap b Y Q ω) ∧
    Summable (fun q : ℕ+ => levelWeight Q q*all false q ap b Y Q ω) := by
  let I := ↥(Ico a b)
  let A := fun (m n : I) => star (phaseAt ω m.val)*phaseAt ω n.val
  let F := fun (m n : I) (q : ℕ+) => levelWeight Q q*spectral q (mark a ap m) (mark a ap n) (single Y)
  let G := fun (m n : I) (d : ℕ+) => spectral d (mark a ap m) (mark a ap n) (switchedTest Y ((d.val:ℝ)*Q) m.val n.val)
  have h (m n : I) : HasSum (F m n) (∑' d,G m n d) ∧ Summable (G m n) := by
    obtain ⟨C,HC⟩ := level_switch (mark a ap m) (mark a ap n) yp
    obtain ⟨out,e⟩ := HC Q qp
    let S := Finset.Icc (1:ℕ+) C
    have f : HasSum (F m n) (∑ q∈S,F m n q) := hasSum_sum_of_ne_finset_zero
      (fun q hq => by dsimp only [F];rw [(out q hq).1,mul_zero])
    have g : HasSum (G m n) (∑ d∈S,G m n d) := hasSum_sum_of_ne_finset_zero (fun d hd => (out d hd).2)
    exact ⟨e ▸ f.summable.hasSum,g.summable⟩
  let T := ∑ m : I,∑ n : I,A m n*(∑' d,G m n d)
  have f : HasSum (fun q : ℕ+ => levelWeight Q q*all false q ap b Y Q ω) T := by
    have s := hasSum_sum (s:=univ) (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
      (fun n (_ : n∈(univ:Finset I)) => (h m n).1.mul_left (A m n)))
    apply s.congr_fun
    intro q
    simp only [all,pair,test,Bool.false_eq_true,if_false,Finset.mul_sum]
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro n _
    dsimp only [F,A];ring
  have g : HasSum (fun d : ℕ+ => all true d ap b Y Q ω) T := hasSum_sum (s:=univ)
    (fun m (_ : m∈(univ:Finset I)) => hasSum_sum (s:=univ)
      (fun n (_ : n∈(univ:Finset I)) => (h m n).2.hasSum.mul_left (A m n)))
  rw [f.tsum_eq]
  exact ⟨g,f.summable⟩

theorem four_sectors {a : ℕ} (ap : 0<a) (b : ℕ) {Y Q : ℝ} (y1 : 1≤Y) (qp : 0<Q) (ω : ℝ) :
    let F := fun s q => E s q ap b Y Q ω+R s q ap b Y Q ω+C s q ap b Y Q ω+H s q ap b Y Q ω
    Summable (fun q : ℕ+ => levelWeight Q q*F false q) ∧
    HasSum (fun d : ℕ+ => F true d) (∑' q : ℕ+,levelWeight Q q*F false q) := by
  have X := interval_level_switch ap b (zero_lt_one.trans_le y1) qp ω
  have first (q : ℕ+) := interval_split false q ap b y1 qp ω
  have second (d : ℕ+) := interval_split true d ap b y1 qp ω
  simp_rw [first,second] at X
  exact ⟨X.2,X.1⟩

end
end ImbalancedChen.Part3.OriginalSwitchedIntervalLevelSwitch20261113
