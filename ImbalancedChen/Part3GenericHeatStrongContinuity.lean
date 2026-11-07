import ImbalancedChen.Part3GenericHeatLaplaceResolvent

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The generic heat family is continuous in operator norm at every positive
time, and every vector trajectory is continuous on the full closed
nonnegative time interval. The endpoint uses the proved generic scalar
measure strong identity, not an operator-norm continuity claim at zero.
-/

namespace ImbalancedChen.Part3.GenericHeatStrongContinuity20261025a

noncomputable section
open Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericHeatLaplaceResolvent20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

theorem continuousOn_heatOperator_positive :
    ContinuousOn (heatOperator D) (Ioi (0 : ℝ)) := by
  change ContinuousOn (fun s : ℝ => cfcL D.selfAdjoint (heatScalar D s)) (Ioi (0 : ℝ))
  exact (cfcL D.selfAdjoint).continuous.comp_continuousOn (continuousOn_heatScalar_positive D)

theorem continuousOn_heatTrajectory_positive (f : H) :
    ContinuousOn (fun s : ℝ => heatOperator D s f) (Ioi (0 : ℝ)) :=
  (ContinuousLinearMap.apply ℂ H f).continuous.comp_continuousOn
    (continuousOn_heatOperator_positive D)

/-- Strong continuity on all nonnegative times, including the actual
identity at zero; positive-time norm continuity supplies the interior. -/
theorem continuousOn_heatTrajectory_nonnegative (f : H) :
    ContinuousOn (fun s : ℝ => heatOperator D s f) (Ici (0 : ℝ)) := by
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    have h0 : ContinuousWithinAt (fun t : ℝ => heatOperator D t f) (Ioi (0 : ℝ)) 0 := by
      change Tendsto (fun t : ℝ => heatOperator D t f) (𝓝[>] 0) (𝓝 (heatOperator D 0 f))
      rw [heatOperator_zero D]
      exact tendsto_heatOperator_at_zero D f
    have hset : insert (0 : ℝ) (Ioi 0) = Ici 0 := by
      ext x
      simp only [mem_insert_iff, mem_Ioi, mem_Ici]
      constructor
      · rintro (rfl | hx)
        · exact le_rfl
        · exact hx.le
      · intro hx
        rcases lt_or_eq_of_le hx with hx | hx
        · exact Or.inr hx
        · exact Or.inl hx.symm
    simpa only [hset] using h0.insert
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    exact ((continuousOn_heatTrajectory_positive D f).continuousAt
      (isOpen_Ioi.mem_nhds hsp)).continuousWithinAt

end
end ImbalancedChen.Part3.GenericHeatStrongContinuity20261025a
