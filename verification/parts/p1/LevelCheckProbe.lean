import ImbalancedChen.HistoricalPrefixCertificate

/-!
Computation-only probe for the finite level checker.  These small tables
are not manuscript certificate data and assert no box or integral bound.
There is deliberately no `classical` command or native decision procedure.
-/

open ImbalancedChen

namespace P1LevelCheckProbe

def increasing : HistoricalPrefixCapData where
  a := 1 / 10
  b := 1 / 5
  m := 0
  old := 1 / 2
  cells3 := {fun _ : Fin 3 => (0 : Fin 1)}
  cap3 := fun _ => 3 / 5
  cells4 := {fun _ : Fin 4 => (0 : Fin 1)}
  cap4 := fun _ => 5 / 8
  cells5 := {fun _ : Fin 5 => (0 : Fin 1)}
  cap5 := fun _ => 2 / 3

theorem increasing_check : increasing.levelCheck = true := by
  decide

def fallingFourth : HistoricalPrefixCapData :=
  { increasing with cap4 := fun _ => 1 / 2 }

theorem fallingFourth_check : fallingFourth.levelCheck = false := by
  decide

def fallingFifth : HistoricalPrefixCapData :=
  { increasing with cap5 := fun _ => 3 / 5 }

theorem fallingFifth_check : fallingFifth.levelCheck = false := by
  decide

#print axioms increasing_check
#print axioms fallingFourth_check
#print axioms fallingFifth_check

end P1LevelCheckProbe
