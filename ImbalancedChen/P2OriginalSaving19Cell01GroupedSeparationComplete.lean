import ImbalancedChen.P2OriginalSaving19Cell01GroupedSeparationSigns
import ImbalancedChen.P2OriginalSaving19Cell01PhysicalMomentRow
namespace ImbalancedChen.P2OriginalSaving19Cell01GroupedSeparation
noncomputable section
open MeasureTheory
open P2OriginalSaving19GroupedSeparation
open P2OriginalSaving19Geometry01BoundedAccess
open P2OriginalSaving19Cell01PhysicalMomentRow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
def Rel (r s : Fin 144) : Prop := AEDisjoint volume (physicalSimplex r) (physicalSimplex s)
theorem node000 : leaves000.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[0], [1]]
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
    boundedRowVertex simplex_vertices [[2], [3]]
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
    exact sep001_0_1) (by simp only [List.pairwise_singleton]))
theorem node002 : leaves002.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[4], [5]]
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
    exact sep002_0_1) (by simp only [List.pairwise_singleton]))
theorem node003 : leaves003.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves000, leaves001, leaves002]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node000
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node001
      · have h := List.mem_singleton.mp hg
        subst group
        exact node002)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep003_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep003_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep003_1_2) (by simp only [List.pairwise_singleton])))
theorem node004 : leaves004.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[6], [7]]
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
    exact sep004_0_1) (by simp only [List.pairwise_singleton]))
theorem node005 : leaves005.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves004, [8]]
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
    boundedRowVertex simplex_vertices [[9], [10]]
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
    boundedRowVertex simplex_vertices [leaves006, [11]]
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
    boundedRowVertex simplex_vertices [leaves003, leaves005, leaves007]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node003
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node005
      · have h := List.mem_singleton.mp hg
        subst group
        exact node007)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep008_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep008_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep008_1_2) (by simp only [List.pairwise_singleton])))
theorem node009 : leaves009.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[12], [13]]
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
    exact sep009_0_1) (by simp only [List.pairwise_singleton]))
theorem node010 : leaves010.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves009, [14]]
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
    boundedRowVertex simplex_vertices [leaves010, [15]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node010
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
    boundedRowVertex simplex_vertices [[16], [17]]
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
    exact sep012_0_1) (by simp only [List.pairwise_singleton]))
theorem node013 : leaves013.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves012, [18]]
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
    boundedRowVertex simplex_vertices [leaves013, [19]]
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
    boundedRowVertex simplex_vertices [leaves008, leaves011, leaves014]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node008
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node011
      · have h := List.mem_singleton.mp hg
        subst group
        exact node014)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep015_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep015_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep015_1_2) (by simp only [List.pairwise_singleton])))
theorem node016 : leaves016.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[20], [21]]
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
    exact sep016_0_1) (by simp only [List.pairwise_singleton]))
theorem node017 : leaves017.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves016, [22]]
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
    boundedRowVertex simplex_vertices [leaves017, [23]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node017
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
    boundedRowVertex simplex_vertices [leaves018, [24]]
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
    boundedRowVertex simplex_vertices [[25], [26]]
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
    boundedRowVertex simplex_vertices [leaves020, [27]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node020
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
    boundedRowVertex simplex_vertices [leaves021, [28]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node021
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
    boundedRowVertex simplex_vertices [leaves022, [29]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node022
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep023_0_1) (by simp only [List.pairwise_singleton]))
theorem node024 : leaves024.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves015, leaves019, leaves023]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node015
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node019
      · have h := List.mem_singleton.mp hg
        subst group
        exact node023)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep024_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep024_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep024_1_2) (by simp only [List.pairwise_singleton])))
theorem node025 : leaves025.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[30], [31]]
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
    exact sep025_0_1) (by simp only [List.pairwise_singleton]))
theorem node026 : leaves026.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves025, [32]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node025
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep026_0_1) (by simp only [List.pairwise_singleton]))
theorem node027 : leaves027.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves026, [33]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node026
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
    boundedRowVertex simplex_vertices [leaves027, [34]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node027
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep028_0_1) (by simp only [List.pairwise_singleton]))
theorem node029 : leaves029.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[35], [36]]
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
    exact sep029_0_1) (by simp only [List.pairwise_singleton]))
theorem node030 : leaves030.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves029, [37]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node029
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep030_0_1) (by simp only [List.pairwise_singleton]))
theorem node031 : leaves031.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves030, [38]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node030
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
    boundedRowVertex simplex_vertices [[39], [40]]
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
    exact sep032_0_1) (by simp only [List.pairwise_singleton]))
theorem node033 : leaves033.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves032, [41]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node032
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep033_0_1) (by simp only [List.pairwise_singleton]))
theorem node034 : leaves034.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[42], [43]]
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
    exact sep034_0_1) (by simp only [List.pairwise_singleton]))
theorem node035 : leaves035.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[44], [45]]
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
    exact sep035_0_1) (by simp only [List.pairwise_singleton]))
theorem node036 : leaves036.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[46], [47]]
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
    boundedRowVertex simplex_vertices [leaves034, leaves035, leaves036]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node034
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node035
      · have h := List.mem_singleton.mp hg
        subst group
        exact node036)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep037_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep037_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep037_1_2) (by simp only [List.pairwise_singleton])))
theorem node038 : leaves038.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[49], [50]]
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
    exact sep038_0_1) (by simp only [List.pairwise_singleton]))
theorem node039 : leaves039.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[48], leaves038]
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
    boundedRowVertex simplex_vertices [leaves033, leaves037, leaves039]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node033
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node037
      · have h := List.mem_singleton.mp hg
        subst group
        exact node039)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep040_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep040_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep040_1_2) (by simp only [List.pairwise_singleton])))
theorem node041 : leaves041.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[53], [54]]
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
    exact sep041_0_1) (by simp only [List.pairwise_singleton]))
theorem node042 : leaves042.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[52], leaves041]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node041)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep042_0_1) (by simp only [List.pairwise_singleton]))
theorem node043 : leaves043.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[51], leaves042]
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
    boundedRowVertex simplex_vertices [leaves031, leaves040, leaves043]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node031
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node040
      · have h := List.mem_singleton.mp hg
        subst group
        exact node043)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep044_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep044_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep044_1_2) (by simp only [List.pairwise_singleton])))
theorem node045 : leaves045.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[58], [59]]
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
    exact sep045_0_1) (by simp only [List.pairwise_singleton]))
theorem node046 : leaves046.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[57], leaves045]
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
    boundedRowVertex simplex_vertices [[56], leaves046]
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
    boundedRowVertex simplex_vertices [[55], leaves047]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node047)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep048_0_1) (by simp only [List.pairwise_singleton]))
theorem node049 : leaves049.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves028, leaves044, leaves048]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node028
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node044
      · have h := List.mem_singleton.mp hg
        subst group
        exact node048)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep049_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep049_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep049_1_2) (by simp only [List.pairwise_singleton])))
theorem node050 : leaves050.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[60], [61]]
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
    exact sep050_0_1) (by simp only [List.pairwise_singleton]))
theorem node051 : leaves051.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves050, [62]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node050
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep051_0_1) (by simp only [List.pairwise_singleton]))
theorem node052 : leaves052.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves051, [63]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node051
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep052_0_1) (by simp only [List.pairwise_singleton]))
theorem node053 : leaves053.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves052, [64]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node052
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep053_0_1) (by simp only [List.pairwise_singleton]))
theorem node054 : leaves054.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[68], [69]]
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
    exact sep054_0_1) (by simp only [List.pairwise_singleton]))
theorem node055 : leaves055.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[67], leaves054]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node054)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep055_0_1) (by simp only [List.pairwise_singleton]))
theorem node056 : leaves056.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[66], leaves055]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node055)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep056_0_1) (by simp only [List.pairwise_singleton]))
theorem node057 : leaves057.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[65], leaves056]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node056)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep057_0_1) (by simp only [List.pairwise_singleton]))
theorem node058 : leaves058.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves053, leaves057, [70]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node053
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node057
      · have h := List.mem_singleton.mp hg
        subst group
        exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep058_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep058_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep058_1_2) (by simp only [List.pairwise_singleton])))
theorem node059 : leaves059.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[72], [73]]
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
    exact sep059_0_1) (by simp only [List.pairwise_singleton]))
theorem node060 : leaves060.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves059, [74]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node059
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep060_0_1) (by simp only [List.pairwise_singleton]))
theorem node061 : leaves061.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[71], leaves060]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node060)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep061_0_1) (by simp only [List.pairwise_singleton]))
theorem node062 : leaves062.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves061, [75]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node061
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep062_0_1) (by simp only [List.pairwise_singleton]))
theorem node063 : leaves063.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves062, [76]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node062
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep063_0_1) (by simp only [List.pairwise_singleton]))
theorem node064 : leaves064.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves024, leaves049, leaves058, leaves063]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node024
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node049
      · rcases List.mem_cons.mp hg with h | hg
        · subst group
          exact node058
        · have h := List.mem_singleton.mp hg
          subst group
          exact node063)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep064_0_1
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact sep064_0_2
      · have h := List.mem_singleton.mp hg
        subst group
        exact sep064_0_3) (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep064_1_2
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep064_1_3) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep064_2_3) (by simp only [List.pairwise_singleton]))))
theorem node065 : leaves065.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[77], [78]]
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
    exact sep065_0_1) (by simp only [List.pairwise_singleton]))
theorem node066 : leaves066.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves065, [79]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node065
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep066_0_1) (by simp only [List.pairwise_singleton]))
theorem node067 : leaves067.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves066, [80]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node066
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep067_0_1) (by simp only [List.pairwise_singleton]))
theorem node068 : leaves068.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves067, [81]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node067
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep068_0_1) (by simp only [List.pairwise_singleton]))
theorem node069 : leaves069.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[82], [83]]
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
    exact sep069_0_1) (by simp only [List.pairwise_singleton]))
theorem node070 : leaves070.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves069, [84]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node069
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep070_0_1) (by simp only [List.pairwise_singleton]))
theorem node071 : leaves071.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves070, [85]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node070
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep071_0_1) (by simp only [List.pairwise_singleton]))
theorem node072 : leaves072.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[86], [87]]
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
    exact sep072_0_1) (by simp only [List.pairwise_singleton]))
theorem node073 : leaves073.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves072, [88]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node072
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep073_0_1) (by simp only [List.pairwise_singleton]))
theorem node074 : leaves074.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[89], [90]]
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
    exact sep074_0_1) (by simp only [List.pairwise_singleton]))
theorem node075 : leaves075.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[91], [92]]
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
    exact sep075_0_1) (by simp only [List.pairwise_singleton]))
theorem node076 : leaves076.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[93], [94]]
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
    exact sep076_0_1) (by simp only [List.pairwise_singleton]))
theorem node077 : leaves077.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves074, leaves075, leaves076]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node074
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node075
      · have h := List.mem_singleton.mp hg
        subst group
        exact node076)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep077_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep077_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep077_1_2) (by simp only [List.pairwise_singleton])))
theorem node078 : leaves078.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[96], [97]]
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
    exact sep078_0_1) (by simp only [List.pairwise_singleton]))
theorem node079 : leaves079.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[95], leaves078]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node078)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep079_0_1) (by simp only [List.pairwise_singleton]))
theorem node080 : leaves080.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves073, leaves077, leaves079]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node073
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node077
      · have h := List.mem_singleton.mp hg
        subst group
        exact node079)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep080_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep080_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep080_1_2) (by simp only [List.pairwise_singleton])))
theorem node081 : leaves081.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[100], [101]]
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
    exact sep081_0_1) (by simp only [List.pairwise_singleton]))
theorem node082 : leaves082.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[99], leaves081]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node081)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep082_0_1) (by simp only [List.pairwise_singleton]))
theorem node083 : leaves083.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[98], leaves082]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node082)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep083_0_1) (by simp only [List.pairwise_singleton]))
theorem node084 : leaves084.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves071, leaves080, leaves083]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node071
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node080
      · have h := List.mem_singleton.mp hg
        subst group
        exact node083)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep084_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep084_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep084_1_2) (by simp only [List.pairwise_singleton])))
theorem node085 : leaves085.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[105], [106]]
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
    exact sep085_0_1) (by simp only [List.pairwise_singleton]))
theorem node086 : leaves086.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[104], leaves085]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node085)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep086_0_1) (by simp only [List.pairwise_singleton]))
theorem node087 : leaves087.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[103], leaves086]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node086)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep087_0_1) (by simp only [List.pairwise_singleton]))
theorem node088 : leaves088.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[102], leaves087]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node087)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep088_0_1) (by simp only [List.pairwise_singleton]))
theorem node089 : leaves089.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves068, leaves084, leaves088]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node068
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node084
      · have h := List.mem_singleton.mp hg
        subst group
        exact node088)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep089_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep089_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep089_1_2) (by simp only [List.pairwise_singleton])))
theorem node090 : leaves090.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[110], [111]]
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
    exact sep090_0_1) (by simp only [List.pairwise_singleton]))
theorem node091 : leaves091.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[109], leaves090]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node090)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep091_0_1) (by simp only [List.pairwise_singleton]))
theorem node092 : leaves092.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[108], leaves091]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node091)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep092_0_1) (by simp only [List.pairwise_singleton]))
theorem node093 : leaves093.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[107], leaves092]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node092)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep093_0_1) (by simp only [List.pairwise_singleton]))
theorem node094 : leaves094.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves093, [112]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node093
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep094_0_1) (by simp only [List.pairwise_singleton]))
theorem node095 : leaves095.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[114], [115]]
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
    exact sep095_0_1) (by simp only [List.pairwise_singleton]))
theorem node096 : leaves096.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves095, [116]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node095
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep096_0_1) (by simp only [List.pairwise_singleton]))
theorem node097 : leaves097.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[113], leaves096]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node096)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep097_0_1) (by simp only [List.pairwise_singleton]))
theorem node098 : leaves098.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves097, [117]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node097
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep098_0_1) (by simp only [List.pairwise_singleton]))
theorem node099 : leaves099.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves098, [118]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node098
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep099_0_1) (by simp only [List.pairwise_singleton]))
theorem node100 : leaves100.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves089, leaves094, leaves099]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node089
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node094
      · have h := List.mem_singleton.mp hg
        subst group
        exact node099)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep100_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep100_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep100_1_2) (by simp only [List.pairwise_singleton])))
theorem node101 : leaves101.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[119], [120]]
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
    exact sep101_0_1) (by simp only [List.pairwise_singleton]))
theorem node102 : leaves102.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves101, [121]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node101
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep102_0_1) (by simp only [List.pairwise_singleton]))
theorem node103 : leaves103.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves102, [122]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node102
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep103_0_1) (by simp only [List.pairwise_singleton]))
theorem node104 : leaves104.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves103, [123]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node103
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep104_0_1) (by simp only [List.pairwise_singleton]))
theorem node105 : leaves105.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[127], [128]]
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
    exact sep105_0_1) (by simp only [List.pairwise_singleton]))
theorem node106 : leaves106.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[126], leaves105]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node105)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep106_0_1) (by simp only [List.pairwise_singleton]))
theorem node107 : leaves107.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[125], leaves106]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node106)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep107_0_1) (by simp only [List.pairwise_singleton]))
theorem node108 : leaves108.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[124], leaves107]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node107)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep108_0_1) (by simp only [List.pairwise_singleton]))
theorem node109 : leaves109.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves104, leaves108, [129]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node104
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node108
      · have h := List.mem_singleton.mp hg
        subst group
        exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep109_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep109_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep109_1_2) (by simp only [List.pairwise_singleton])))
theorem node110 : leaves110.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[133], [134]]
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
    exact sep110_0_1) (by simp only [List.pairwise_singleton]))
theorem node111 : leaves111.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[132], leaves110]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node110)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep111_0_1) (by simp only [List.pairwise_singleton]))
theorem node112 : leaves112.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[131], leaves111]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node111)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep112_0_1) (by simp only [List.pairwise_singleton]))
theorem node113 : leaves113.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[130], leaves112]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node112)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep113_0_1) (by simp only [List.pairwise_singleton]))
theorem node114 : leaves114.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves113, [135]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node113
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep114_0_1) (by simp only [List.pairwise_singleton]))
theorem node115 : leaves115.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves109, leaves114, [136]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node109
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node114
      · have h := List.mem_singleton.mp hg
        subst group
        exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep115_0_1
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep115_0_2) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep115_1_2) (by simp only [List.pairwise_singleton])))
theorem node116 : leaves116.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[138], [139]]
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
    exact sep116_0_1) (by simp only [List.pairwise_singleton]))
theorem node117 : leaves117.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves116, [140]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node116
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep117_0_1) (by simp only [List.pairwise_singleton]))
theorem node118 : leaves118.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [[137], leaves117]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact (by simp only [List.pairwise_singleton])
    · have h := List.mem_singleton.mp hg
      subst group
      exact node117)
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep118_0_1) (by simp only [List.pairwise_singleton]))
theorem node119 : leaves119.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves118, [141]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node118
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep119_0_1) (by simp only [List.pairwise_singleton]))
theorem node120 : leaves120.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves119, [142]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node119
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep120_0_1) (by simp only [List.pairwise_singleton]))
theorem node121 : leaves121.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves120, [143]]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node120
    · have h := List.mem_singleton.mp hg
      subst group
      exact (by simp only [List.pairwise_singleton]))
    (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep121_0_1) (by simp only [List.pairwise_singleton]))
theorem node122 : leaves122.Pairwise Rel := by
  exact grouped_aedisjoint (fun r => (row r).linear) (fun r => (row r).base)
    boundedRowVertex simplex_vertices [leaves064, leaves100, leaves115, leaves121]
    (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact node064
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact node100
      · rcases List.mem_cons.mp hg with h | hg
        · subst group
          exact node115
        · have h := List.mem_singleton.mp hg
          subst group
          exact node121)
    (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep122_0_1
    · rcases List.mem_cons.mp hg with h | hg
      · subst group
        exact sep122_0_2
      · have h := List.mem_singleton.mp hg
        subst group
        exact sep122_0_3) (List.Pairwise.cons (by
    intro group hg
    rcases List.mem_cons.mp hg with h | hg
    · subst group
      exact sep122_1_2
    · have h := List.mem_singleton.mp hg
      subst group
      exact sep122_1_3) (List.Pairwise.cons (by
    intro group hg
    have h := List.mem_singleton.mp hg
    subst group
    exact sep122_2_3) (by simp only [List.pairwise_singleton]))))
theorem original_root_cover : ∀ r : Fin 144, r ∈ rootLeaves := by
  decide +kernel
theorem all_original_pairs : Pairwise Rel :=
  pairwise_from_cover (fun r => (row r).linear) (fun r => (row r).base)
    rootLeaves original_root_cover node122
#print axioms all_original_pairs
end
end ImbalancedChen.P2OriginalSaving19Cell01GroupedSeparation
