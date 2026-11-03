import ImbalancedChen.P2EnhancedNonunitMarkedMass
import ImbalancedChen.P2SeedOmegaFirstThreeLiteralMass
import ImbalancedChen.P2SeedOmegaSwitchedMassFour
import ImbalancedChen.AffinePrimeGates

/-! SOURCE ONLY / UNCOMPILED.
The seven ORIGINAL Gamma9--15 groups are unions of closed colour boxes.
The only overlaps inside one group are coordinate walls at a2 or a3.
These are removed only in the Lebesgue integral; no arithmetic atom is
removed. In particular 112 and 122 remain distinct occurrences in the
different original Gamma groups. -/

namespace ImbalancedChen.P2EnhancedGroupedTripleDictionary
noncomputable section
open Set MeasureTheory Finset Wu2008DoubleSieve
open P2EnhancedNonunitLabelGeometry P2EnhancedNonunitPhysicalQuadrature
open P2EnhancedNonunitWordMass P2EnhancedNonunitMarkedMass
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open scoped Classical BigOperators

abbrev Point := Fin 3 → ℝ

def words (j : Fin 7) : List (List ℕ) := secondFunctionalMotherGammaWords (9+j.val)

def wordDomain (w : List ℕ) : Set Point :=
  {t | ∀ q, (∑ i, rows 2 q i*t i) ≤ wordIntercept 2 w q}

def nativeDomain : Fin 7 → Set Point := ![
  P2SeedOmegaFirstThreeKernel.domain 0,
  P2SeedOmegaFirstThreeKernel.domain 1,
  P2SeedOmegaFirstThreeKernel.domain 2,
  P2SeedOmegaSwitchedKernelFour.domain 0,
  P2SeedOmegaSwitchedKernelFour.domain 1,
  P2SeedOmegaSwitchedKernelFour.domain 2,
  P2SeedOmegaSwitchedKernelFour.domain 3]

def kernel (alpha : ℝ) (t : Point) : ℝ :=
  HighNonunitLegal.G (1 : Fin 3) alpha t * continuousDensity t

def boxMass (w : List ℕ) (alpha : ℝ) : ℝ :=
  ∫ t in continuousCube 3, (wordDomain w).indicator (kernel alpha) t

def groupedMass (j : Fin 7) (alpha : ℝ) : ℝ :=
  ∫ t in nativeDomain j, kernel alpha t

theorem wordDomain_measurable (w : List ℕ) : MeasurableSet (wordDomain w) := by
  unfold wordDomain
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_le (by fun_prop) measurable_const

theorem boxMass_triple (c0 c1 c2 : ℕ) (alpha : ℝ) :
    boxMass [c0,c1,c2] alpha = nonunitIntegral [c0,c1,c2] alpha := by
  unfold boxMass nonunitIntegral wordIntegral closedIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  change (if t ∈ wordDomain [c0,c1,c2] then
    HighNonunitLegal.G (1 : Fin 3) alpha t * continuousDensity t else 0) =
    (if t ∈ wordDomain [c0,c1,c2] then
      HighNonunitLegal.G (1 : Fin 3) alpha t else 0) * continuousDensity t
  split_ifs <;> simp

theorem original_boxMass (j : Fin 7) (alpha : ℝ) :
    ((words j).map (fun w => boxMass w alpha)).sum =
      ((words j).map (fun w => nonunitIntegral w alpha)).sum := by
  fin_cases j <;> simp [words,secondFunctionalMotherGammaWords,boxMass_triple]

theorem nativeDomain_measurable (j : Fin 7) : MeasurableSet (nativeDomain j) := by
  fin_cases j
  all_goals first
    | exact P2SeedOmegaFirstThreeKernel.domain_measurable _
    | exact P2SeedOmegaSwitchedKernelFour.domain_measurable _

theorem nativeDomain_subset_cube (j : Fin 7) : nativeDomain j ⊆ continuousCube 3 := by
  fin_cases j
  all_goals first
    | exact P2SeedOmegaFirstThreeKernel.domain_subset_cube _
    | exact P2SeedOmegaSwitchedKernelFour.domain_subset_cube _

theorem ae_coordinate_ne (i : Fin 3) (c : ℝ) :
    ∀ᵐ t : Point ∂volume, t i ≠ c := by
  have hproj : (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) ≠ 0 := by
    intro hz
    have hh := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) hz
    norm_num at hh
  rw [ae_iff]
  simpa only [not_not] using affinePrimeWall_volume_zero
    (ContinuousLinearMap.proj i : Point →L[ℝ] ℝ) hproj c

/-- This pointwise statement excludes precisely the shared colour walls,
not prime-order diagonals, unit surfaces, or the original source atoms. -/
theorem original_group_indicator (j : Fin 7) (t : Point) (z : ℝ)
    (h02 : t 0 ≠ a2) (h12 : t 1 ≠ a2) (h22 : t 2 ≠ a2)
    (h03 : t 0 ≠ a3) (h13 : t 1 ≠ a3) (h23 : t 2 ≠ a3) :
    ((words j).map (fun w => (wordDomain w).indicator (fun _ => z) t)).sum =
      (nativeDomain j).indicator (fun _ => z) t := by
  have h01 : a0 ≤ a1 := by norm_num [a0,a1]
  have h12a : a1 ≤ a2 := by norm_num [a1,a2]
  have h23a : a2 ≤ a3 := by norm_num [a2,a3]
  have h3b : a3 ≤ b := by norm_num [a3,b]
  fin_cases j
  all_goals
    simp only [words,secondFunctionalMotherGammaWords,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,nativeDomain,Matrix.cons_val_zero,Matrix.cons_val_succ,
      P2SeedOmegaFirstThreeKernel.domain,P2SeedOmegaSwitchedKernelFour.domain,
      P2SeedOmegaSwitchedKernelFour.nativeIndex,Set.indicator_apply,wordDomain,
      Set.mem_setOf_eq,rows_iff,
      SecondFunctionalGeometricMass.OriginalBlocks.ordered_endpoints,
      Fin.monotone_iff_le_succ,Fin.forall_fin_succ,Fin.forall_fin_zero,
      bandLo,bandHi,List.getD_cons_zero,List.getD_cons_succ,
      LowerTripleContinuous.D] at *
    dsimp at *
    split_ifs <;> simp_all only [add_zero,zero_add] <;>
      aesop (add safe tactic (by linarith))

theorem original_group_indicator_ae (j : Fin 7) (alpha : ℝ) :
    (fun t => ((words j).map
      (fun w => (wordDomain w).indicator (kernel alpha) t)).sum) =ᵐ[volume]
      (nativeDomain j).indicator (kernel alpha) := by
  filter_upwards [ae_coordinate_ne 0 a2,ae_coordinate_ne 1 a2,ae_coordinate_ne 2 a2,
    ae_coordinate_ne 0 a3,ae_coordinate_ne 1 a3,ae_coordinate_ne 2 a3]
    with t h02 h12 h22 h03 h13 h23
  exact original_group_indicator j t (kernel alpha t) h02 h12 h22 h03 h13 h23

theorem boxKernel_integrable (w : List ℕ) (alpha : ℝ) :
    IntegrableOn ((wordDomain w).indicator (kernel alpha)) (continuousCube 3) :=
  (HighNonunitLegal.G_weighted_integrable (1 : Fin 3) alpha).indicator
    (wordDomain_measurable w)

private theorem listKernel_integrable (ws : List (List ℕ)) (alpha : ℝ) :
    IntegrableOn (fun t =>
      (ws.map (fun w => (wordDomain w).indicator (kernel alpha) t)).sum)
      (continuousCube 3) := by
  induction ws with
  | nil => simpa using (integrable_zero : Integrable (fun _ : Point => (0 : ℝ))
      (volume.restrict (continuousCube 3)))
  | cons w ws ih => simpa only [List.map_cons,List.sum_cons] using
      (boxKernel_integrable w alpha).add ih

private theorem integral_list (ws : List (List ℕ)) (alpha : ℝ) :
    ((ws.map (fun w => boxMass w alpha)).sum) =
      ∫ t in continuousCube 3,
        ((ws.map (fun w => (wordDomain w).indicator (kernel alpha) t)).sum) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [ih]
    exact (integral_add (boxKernel_integrable w alpha) (listKernel_integrable ws alpha)).symm

/-- Exact grouped integral equality. Closed-boundary duplication is paid
by genuine coordinate-nullity; literal word multiplicities are retained. -/
theorem original_grouped_integral (j : Fin 7) (alpha : ℝ) :
    ((words j).map (fun w => nonunitIntegral w alpha)).sum = groupedMass j alpha := by
  rw [← original_boxMass j alpha,integral_list]
  rw [integral_congr_ae (ae_restrict_of_ae (original_group_indicator_ae j alpha))]
  rw [integral_indicator (nativeDomain_measurable j),Measure.restrict_restrict
    (nativeDomain_measurable j)]
  rw [Set.inter_eq_left.mpr (nativeDomain_subset_cube j)]
  rfl

theorem groupedMass_first (j : Fin 3) (alpha : ℝ) :
    groupedMass ⟨j.val,by omega⟩ alpha =
      P2SeedOmegaFirstThreeKernel.actualMass alpha j := by
  fin_cases j <;> rfl

theorem groupedMass_last (j : Fin 4) {alpha : ℝ} (ha : 2 ≤ alpha) :
    groupedMass ⟨3+j.val,by omega⟩ alpha =
      P2SeedOmegaSwitchedKernelFour.actualMass alpha j := by
  have hd : nativeDomain ⟨3+j.val,by omega⟩ =
      P2SeedOmegaSwitchedKernelFour.domain j := by fin_cases j <;> rfl
  unfold groupedMass P2SeedOmegaSwitchedKernelFour.actualMass
  rw [hd]
  apply setIntegral_congr_fun (P2SeedOmegaSwitchedKernelFour.domain_measurable j)
  intro t ht
  exact LowerTripleContinuous.weighted_legal_literal
    (LowerTripleContinuous.cube_legal ha
      (P2SeedOmegaSwitchedKernelFour.domain_subset_cube j ht))

def costIndex (j : Fin 7) : Fin 13 := ⟨j.val,by omega⟩

theorem original_Gamma9_to_15_literal_cap {alpha : ℝ} (ha : 2 ≤ alpha) (j : Fin 7) :
    ((words j).map (fun w => nonunitIntegral w alpha)).sum ≤
      P2SeedOmegaLiteralFunctional.switchedMass (costIndex j) := by
  rw [original_grouped_integral]
  have hfirst := P2SeedOmegaFirstThreeLiteralMass.original_first_three_mass_bounds ha
  fin_cases j
  · exact hfirst.1
  · exact hfirst.2.1
  · exact hfirst.2.2
  all_goals
    rw [groupedMass_last _ ha]
    exact P2SeedOmegaSwitchedMassFour.actual_M12_to_M15_le_literal alpha ha _

end
end ImbalancedChen.P2EnhancedGroupedTripleDictionary
