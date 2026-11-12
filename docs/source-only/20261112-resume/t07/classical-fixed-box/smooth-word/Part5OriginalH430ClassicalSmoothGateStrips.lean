import ImbalancedChen.Part5OriginalH430ClassicalSmoothRankCoordinates

/-! Convert the transition of a violated original gate to the paid two-slot
physical prime strip. Slots remain distinct even when their entries agree. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothGateStrips
noncomputable section
open Finset Real Wu2008DoubleSieve
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothWordPhysical (logPoint)
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalProperWallPairs (forms intercept proj near)
open Part5OriginalH430ClassicalProperWallMarkedOutputs (onWall)
open scoped Classical BigOperators

def location {s r : ℕ} (i0 : Fin s) : Gate s r → Fin (rank s r) × Fin (rank s r) × Fin 8
  | .outerLo => (0,qi i0,0)
  | .outerHi => (0,qi i0,1)
  | .primeLo i => (0,qi i,2)
  | .primeHi i => (0,qi i,6)
  | .colourLo i j | .colourHi i j => (0,qi i,⟨3+j.val,by omega⟩)
  | .primeOrder i j => (qi j,qi i,7)
  | .tailOrder i j => (ri j,ri i,7)
  | .penultimate i j => (ri j,qi i,7)

theorem distinct_locations {s r : ℕ} {C : Fin s → ℕ} (i0 : Fin s) (g : Gate s r)
    (hg : active C g) : (location i0 g).1≠(location i0 g).2.1 := by
  intro h
  have he := congrArg Fin.val h
  cases g <;> simp only [active,location,qi,ri,Fin.val_zero,Fin.val_succ,Fin.val_castLE,
    Fin.val_natAdd] at hg he <;> first | omega | exact (ne_of_lt hg) (Fin.ext (by omega))

theorem physical_margin {s r N : ℕ} (i0 : Fin s) (ν : ℝ) (g : Gate s r)
    (t : Fin (rank s r) → Fin (2*N+1)) :
    let f := fun i => (t i).val; let u := location i0 g
    let v := ![f u.1,f u.2.1]
    |forms u.2.2 (actualPrimeTupleLog N v)-intercept ν u.2.2|=
      |margin ν (logPoint N (first f) (qVec f) (rVec f)) g| := by
  cases g
  case colourLo i j =>
    fin_cases j <;> simp [location,forms,intercept,proj,margin,powerMargin,colourPower,
      actualPrimeTupleLog,logPoint,first,qVec,rVec,smul_eq_mul]
  case colourHi i j =>
    fin_cases j <;> simp [location,forms,intercept,proj,margin,powerMargin,colourPower,
      actualPrimeTupleLog,logPoint,first,qVec,rVec,smul_eq_mul]
  all_goals simp [location,forms,intercept,proj,margin,powerMargin,colourPower,
      actualPrimeTupleLog,logPoint,first,qVec,rVec,smul_eq_mul,abs_sub_comm]

theorem paid_strip {s r N : ℕ} (hs : 0<s) (C : Fin s → ℕ) {ν δ : ℝ} (hd : 0<δ)
    (t : Fin (rank s r) → Fin (2*N+1)) :
    let f := fun i => (t i).val; let x := logPoint N (first f) (qVec f) (rVec f)
    ¬accepted C ν x → weight C ν δ x≠0 → onWall ν δ t := by
  intro hbad hW
  obtain ⟨g,hg,hstrip⟩ := failed_positive_strip hd hbad hW
  let i0 : Fin s := ⟨0,hs⟩
  let u := location i0 g
  refine ⟨u.1,u.2.1,distinct_locations i0 g (mem_program.mp hg),u.2.2,?_⟩
  exact (physical_margin i0 ν g t).le.trans hstrip

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothGateStrips

