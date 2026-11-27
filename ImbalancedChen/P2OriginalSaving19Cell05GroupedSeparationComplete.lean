import ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparationSigns
import ImbalancedChen.P2OriginalSaving19Cell05PhysicalMomentRow
namespace ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparation
noncomputable section
open MeasureTheory
open P2OriginalSaving19GroupedSeparation
open P2OriginalSaving19Cell05AllRowGaps
open P2OriginalSaving19Cell05PhysicalMomentRow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def Rel (r s : Fin 56) : Prop := AEDisjoint volume (physicalSimplex r) (physicalSimplex s)
theorem node000 : leaves000.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[0], [1]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep000_0_1) (by simp only [List.pairwise_singleton]))
theorem node001 : leaves001.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves000, [2]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node000
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep001_0_1) (by simp only [List.pairwise_singleton]))
theorem node002 : leaves002.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves001, [3]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node001
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep002_0_1) (by simp only [List.pairwise_singleton]))
theorem node003 : leaves003.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves002, [4]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node002
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep003_0_1) (by simp only [List.pairwise_singleton]))
theorem node004 : leaves004.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves003, [5]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node003
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep004_0_1) (by simp only [List.pairwise_singleton]))
theorem node005 : leaves005.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves004, [6]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node004
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep005_0_1) (by simp only [List.pairwise_singleton]))
theorem node006 : leaves006.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[7], [8]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep006_0_1) (by simp only [List.pairwise_singleton]))
theorem node007 : leaves007.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves006, [9]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node006
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep007_0_1) (by simp only [List.pairwise_singleton]))
theorem node008 : leaves008.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves007, [10]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node007
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep008_0_1) (by simp only [List.pairwise_singleton]))
theorem node009 : leaves009.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves008, [11]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node008
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep009_0_1) (by simp only [List.pairwise_singleton]))
theorem node010 : leaves010.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves009, [12]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node009
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep010_0_1) (by simp only [List.pairwise_singleton]))
theorem node011 : leaves011.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[13], [14]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep011_0_1) (by simp only [List.pairwise_singleton]))
theorem node012 : leaves012.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves011, [15]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node011
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep012_0_1) (by simp only [List.pairwise_singleton]))
theorem node013 : leaves013.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves012, [16]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node012
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep013_0_1) (by simp only [List.pairwise_singleton]))
theorem node014 : leaves014.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves013, [17]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node013
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep014_0_1) (by simp only [List.pairwise_singleton]))
theorem node015 : leaves015.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[18], [19]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep015_0_1) (by simp only [List.pairwise_singleton]))
theorem node016 : leaves016.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves015, [20]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node015
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep016_0_1) (by simp only [List.pairwise_singleton]))
theorem node017 : leaves017.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves016, [21]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node016
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep017_0_1) (by simp only [List.pairwise_singleton]))
theorem node018 : leaves018.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[22], [23]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep018_0_1) (by simp only [List.pairwise_singleton]))
theorem node019 : leaves019.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves018, [24]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node018
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep019_0_1) (by simp only [List.pairwise_singleton]))
theorem node020 : leaves020.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[25], [26]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep020_0_1) (by simp only [List.pairwise_singleton]))
theorem node021 : leaves021.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[27], [28]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep021_0_1) (by simp only [List.pairwise_singleton]))
theorem node022 : leaves022.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[29], [30]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep022_0_1) (by simp only [List.pairwise_singleton]))
theorem node023 : leaves023.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves020, leaves021, leaves022]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node020
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node021
      · have h := List.mem_singleton.mp hg
        subst group
        exact node022)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep023_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep023_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep023_1_2) (by simp only [List.pairwise_singleton])))
theorem node024 : leaves024.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[32], [33]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep024_0_1) (by simp only [List.pairwise_singleton]))
theorem node025 : leaves025.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[31], leaves024]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node024)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep025_0_1) (by simp only [List.pairwise_singleton]))
theorem node026 : leaves026.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves019, leaves023, leaves025]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node019
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node023
      · have h := List.mem_singleton.mp hg
        subst group
        exact node025)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep026_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep026_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep026_1_2) (by simp only [List.pairwise_singleton])))
theorem node027 : leaves027.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[36], [37]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep027_0_1) (by simp only [List.pairwise_singleton]))
theorem node028 : leaves028.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[35], leaves027]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node027)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep028_0_1) (by simp only [List.pairwise_singleton]))
theorem node029 : leaves029.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[34], leaves028]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node028)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep029_0_1) (by simp only [List.pairwise_singleton]))
theorem node030 : leaves030.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves017, leaves026, leaves029]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node017
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node026
      · have h := List.mem_singleton.mp hg
        subst group
        exact node029)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep030_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep030_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep030_1_2) (by simp only [List.pairwise_singleton])))
theorem node031 : leaves031.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[41], [42]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep031_0_1) (by simp only [List.pairwise_singleton]))
theorem node032 : leaves032.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[40], leaves031]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node031)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep032_0_1) (by simp only [List.pairwise_singleton]))
theorem node033 : leaves033.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[39], leaves032]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node032)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep033_0_1) (by simp only [List.pairwise_singleton]))
theorem node034 : leaves034.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[38], leaves033]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node033)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep034_0_1) (by simp only [List.pairwise_singleton]))
theorem node035 : leaves035.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves014, leaves030, leaves034]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node014
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node030
      · have h := List.mem_singleton.mp hg
        subst group
        exact node034)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep035_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep035_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep035_1_2) (by simp only [List.pairwise_singleton])))
theorem node036 : leaves036.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[47], [48]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep036_0_1) (by simp only [List.pairwise_singleton]))
theorem node037 : leaves037.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[46], leaves036]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node036)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep037_0_1) (by simp only [List.pairwise_singleton]))
theorem node038 : leaves038.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[45], leaves037]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node037)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep038_0_1) (by simp only [List.pairwise_singleton]))
theorem node039 : leaves039.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[44], leaves038]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node038)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep039_0_1) (by simp only [List.pairwise_singleton]))
theorem node040 : leaves040.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[43], leaves039]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node039)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep040_0_1) (by simp only [List.pairwise_singleton]))
theorem node041 : leaves041.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves010, leaves035, leaves040]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node010
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node035
      · have h := List.mem_singleton.mp hg
        subst group
        exact node040)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep041_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep041_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep041_1_2) (by simp only [List.pairwise_singleton])))
theorem node042 : leaves042.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[54], [55]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep042_0_1) (by simp only [List.pairwise_singleton]))
theorem node043 : leaves043.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[53], leaves042]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node042)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep043_0_1) (by simp only [List.pairwise_singleton]))
theorem node044 : leaves044.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[52], leaves043]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node043)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep044_0_1) (by simp only [List.pairwise_singleton]))
theorem node045 : leaves045.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[51], leaves044]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node044)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep045_0_1) (by simp only [List.pairwise_singleton]))
theorem node046 : leaves046.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[50], leaves045]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node045)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep046_0_1) (by simp only [List.pairwise_singleton]))
theorem node047 : leaves047.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [[49], leaves046]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node046)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep047_0_1) (by simp only [List.pairwise_singleton]))
theorem node048 : leaves048.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex05 simplex_vertices [leaves005, leaves041, leaves047]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node005
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node041
      · have h := List.mem_singleton.mp hg
        subst group
        exact node047)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep048_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep048_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep048_1_2) (by simp only [List.pairwise_singleton])))
theorem original_root_cover : ∀ r : Fin 56, r ∈ rootLeaves := by
  decide +kernel
theorem all_original_pairs : Pairwise Rel :=
  pairwise_from_cover (fun r => (row r).linear) (fun r => (row r).base)
    rootLeaves original_root_cover node048
#print axioms all_original_pairs
end
end ImbalancedChen.P2OriginalSaving19Cell05GroupedSeparation
