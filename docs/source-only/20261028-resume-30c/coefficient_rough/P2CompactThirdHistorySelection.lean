import ImbalancedChen.P2ActualFifthBufferedParentWitness
import Mathlib.Topology.Order.Compact

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.

The selected-third table below is the original `HistoricalThirdCoarse.cells`,
with its actual rational endpoints, wholly ordered-box tests and first-stop
test.  One rational e, one chi and one mesh are constructed on a compact
subset of the strict original physical cells.  The table precedes omega
and N.  A positive compact rough floor then permits every later omega below
that floor.  The fifth history allowance is proved uniformly, rather than
being required point by point from an arithmetic caller.
-/

namespace ImbalancedChen.P2CompactThirdHistorySelection

noncomputable section
open Classical Filter Set
open scoped Topology
open VariableEnvelope HistoricalThirdCoarse
open Certificates.P2OriginalSixthElevenLogSemantics
open P2ActualFifthBufferedParentWitness

def thirdCoordinates (t : Physical) : Fin 3 → ℝ :=
  historicalPrefixProject (by omega : 3 ≤ 6) t

def selectionMargin (t : Physical) : ℝ :=
  min (parentAllowance t)
    (min (t 5) (min (t 1 - t 2)
      (min (t 0 - t 1) (extendedFirstStop - t 0))))

theorem continuous_selectionMargin : Continuous selectionMargin := by
  unfold selectionMargin parentAllowance R0 H3 H5
  fun_prop

theorem selectionMargin_pos (c : Cell) (t : Physical) (hc : PhysicalCell c t) :
    0 < selectionMargin t := by
  have hstop : t 0 < extendedFirstStop := by
    have hx := hc.largest
    norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu,
      extendedFirstStop] at *
    linarith
  exact lt_min (parentAllowance_pos c t hc)
    (lt_min (hc.coordinates_pos 5)
      (lt_min (sub_pos.mpr hc.order.2.2.2.1)
        (lt_min (sub_pos.mpr hc.order.2.2.2.2) (sub_pos.mpr hstop))))

theorem selectionMargin_bounds (t : Physical) :
    selectionMargin t ≤ parentAllowance t ∧
    selectionMargin t ≤ t 5 ∧
    selectionMargin t ≤ t 1 - t 2 ∧
    selectionMargin t ≤ t 0 - t 1 ∧
    selectionMargin t ≤ extendedFirstStop - t 0 := by
  unfold selectionMargin
  exact ⟨min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))⟩

structure CompactThirdChoice (C : Set Physical) where
  e : ℚ
  chi : ℝ
  mesh : ℕ
  roughFloor : ℝ
  e_pos : 0 < e
  e_small : (e : ℝ) < (3 / 256 : ℝ) / 100
  chi_pos : 0 < chi
  chi_small : chi < (e : ℝ) / 10
  roughFloor_pos : 0 < roughFloor
  rough_margin : ∀ t ∈ C, roughFloor < t 5
  history_buffer : ∀ t ∈ C, historyLoss (e : ℝ) chi < parentAllowance t
  selected_cover : ∀ t ∈ C, ∃ j ∈ cells (e : ℝ) chi mesh,
    thirdCoordinates t ∈ logPrimeMeshCell 0 (19 / 96) mesh j

/-- A single finite original coarse table covers the whole compact
physical set.  Its parameters are chosen before any target, original
prime history, row bank or rough activation exponent.  Empty C is allowed. -/
theorem exists_compactThirdChoice (C : Set Physical) (hC : IsCompact C)
    (hphysical : ∀ t ∈ C, ∃ c : Cell, PhysicalCell c t) :
    Nonempty (CompactThirdChoice C) := by
  have hpositive : ∀ t ∈ C, 0 < selectionMargin t := by
    intro t ht
    obtain ⟨c, hc⟩ := hphysical t ht
    exact selectionMargin_pos c t hc
  obtain ⟨delta, hd, hlower⟩ := hC.exists_forall_le'
    continuous_selectionMargin.continuousOn hpositive
  obtain ⟨e, he, hes⟩ := exists_rat_btwn
    (show (0 : ℝ) < min (delta / 100) ((3 / 256 : ℝ) / 100) by positivity)
  have heDelta : (e : ℝ) < delta / 100 := hes.trans_le (min_le_left _ _)
  have heSmall : (e : ℝ) < (3 / 256 : ℝ) / 100 :=
    hes.trans_le (min_le_right _ _)
  let chi : ℝ := (e : ℝ) / 20
  have hchi : 0 < chi := by dsimp [chi]; positivity
  have hchiSmall : chi < (e : ℝ) / 10 := by dsimp [chi]; linarith
  have hstepTarget : 0 < min chi (delta / 10) := lt_min hchi (by positivity)
  obtain ⟨mesh, hmesh⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 (19 / 96)).eventually (gt_mem_nhds hstepTarget))
  have hstep := hmesh mesh le_rfl
  have hstepChi : logPrimeMeshStep 0 (19 / 96) mesh < chi :=
    hstep.trans_le (min_le_left _ _)
  have hstepDelta : logPrimeMeshStep 0 (19 / 96) mesh < delta / 10 :=
    hstep.trans_le (min_le_right _ _)
  have hstep0 : 0 < logPrimeMeshStep 0 (19 / 96) mesh :=
    logPrimeMeshStep_pos (by norm_num) mesh
  refine ⟨⟨e, chi, mesh, delta / 2, by exact_mod_cast he, heSmall,
    hchi, hchiSmall, by positivity, ?_, ?_, ?_⟩⟩
  · intro t ht
    have hz := (hlower t ht).trans (selectionMargin_bounds t).2.1
    linarith
  · intro t ht
    have ha := (hlower t ht).trans (selectionMargin_bounds t).1
    dsimp only [historyLoss, chi]
    linarith
  · intro t ht
    obtain ⟨c, hc⟩ := hphysical t ht
    have hδ := hlower t ht
    have hbounds := selectionMargin_bounds t
    have hgap21 := hδ.trans hbounds.2.2.1
    have hgap10 := hδ.trans hbounds.2.2.2.1
    have hstop := hδ.trans hbounds.2.2.2.2
    have hbox : thirdCoordinates t ∈ logPrimeBox (fun _ => (0 : ℝ))
        (fun _ => (19 / 96 : ℝ)) := by
      apply mem_logPrimeBox.mpr
      intro i
      have hp : 0 < thirdCoordinates t i :=
        hc.coordinates_pos (i.castLE (by omega : 3 ≤ 6))
      have hu : thirdCoordinates t i < (19 / 96 : ℝ) := by
        have h0 : t 0 < (19 / 96 : ℝ) := by
          have hx := hc.largest
          norm_num [Certificates.P2OriginalSixthElevenLogSemantics.mu] at hx
          linarith
        fin_cases i <;> dsimp [thirdCoordinates, historicalPrefixProject] <;>
          linarith [hc.order.2.2.2.1, hc.order.2.2.2.2]
      exact ⟨hp.le, hu⟩
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) mesh hbox
    have hlo (i : Fin 3) : (qLogPrimeMeshLo 0 (19 / 96) mesh j i : ℝ) ≤
        thirdCoordinates t i := by
      rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) mesh j) i]
      exact (mem_logPrimeMeshCell.mp hj i).1
    have hhi (i : Fin 3) : thirdCoordinates t i <
        (qLogPrimeMeshHi 0 (19 / 96) mesh j i : ℝ) := by
      rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) mesh j) i]
      exact (mem_logPrimeMeshCell.mp hj i).2
    have hside (i : Fin 3) :
        (qLogPrimeMeshHi 0 (19 / 96) mesh j i : ℝ) =
          (qLogPrimeMeshLo 0 (19 / 96) mesh j i : ℝ) +
            logPrimeMeshStep 0 (19 / 96) mesh := by
      rw [congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) mesh j) i,
        congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) mesh j) i]
      exact logPrimeMeshHi_eq_lo_add_step 0 (19 / 96) mesh j i
    have hformed : (box mesh j).WellFormed := by
      have hle (i : Fin 3) : qLogPrimeMeshLo 0 (19 / 96) mesh j i ≤
          qLogPrimeMeshHi 0 (19 / 96) mesh j i := by
        have hleR : (qLogPrimeMeshLo 0 (19 / 96) mesh j i : ℝ) ≤
            (qLogPrimeMeshHi 0 (19 / 96) mesh j i : ℝ) := by linarith [hside i]
        exact_mod_cast hleR
      exact ⟨hle 0, hle 1, hle 2⟩
    have hzlo : 0 ≤ (box mesh j).lz := by
      have hzR : (0 : ℝ) ≤ (qLogPrimeMeshLo 0 (19 / 96) mesh j 2 : ℝ) := by
        rw [congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) mesh j) 2]
        exact (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 19 / 96) mesh j 2).1
      exact_mod_cast hzR
    have hordered21 : (box mesh j).uz ≤ (box mesh j).ly := by
      have hl := hlo 2
      have hu := hhi 1
      dsimp only [thirdCoordinates, historicalPrefixProject] at hl hu
      have hR : (qLogPrimeMeshHi 0 (19 / 96) mesh j 2 : ℝ) ≤
          (qLogPrimeMeshLo 0 (19 / 96) mesh j 1 : ℝ) := by linarith [hside 1, hside 2]
      exact_mod_cast hR
    have hordered10 : (box mesh j).uy ≤ (box mesh j).lx := by
      have hl := hlo 1
      have hu := hhi 0
      dsimp only [thirdCoordinates, historicalPrefixProject] at hl hu
      have hR : (qLogPrimeMeshHi 0 (19 / 96) mesh j 1 : ℝ) ≤
          (qLogPrimeMeshLo 0 (19 / 96) mesh j 0 : ℝ) := by linarith [hside 0, hside 1]
      exact_mod_cast hR
    have htop : ((box mesh j).ux : ℝ) ≤ extendedFirstStop - 4 * (e : ℝ) := by
      have hl := hlo 0
      dsimp only [thirdCoordinates, historicalPrefixProject] at hl
      change (qLogPrimeMeshHi 0 (19 / 96) mesh j 0 : ℝ) ≤ _
      linarith [hside 0]
    have hwidth : ((box mesh j).width : ℝ) = logPrimeMeshStep 0 (19 / 96) mesh := by
      simp only [RationalBox.width, Rat.cast_max, Rat.cast_zero, Rat.cast_sub, box]
      have hdif (i : Fin 3) :
          (qLogPrimeMeshHi 0 (19 / 96) mesh j i : ℝ) -
            (qLogPrimeMeshLo 0 (19 / 96) mesh j i : ℝ) =
              logPrimeMeshStep 0 (19 / 96) mesh := by linarith [hside i]
      rw [hdif 0, hdif 1, hdif 2]
      simp only [max_self, max_eq_right hstep0.le]
    refine ⟨j, (mem_cells (e : ℝ) chi mesh j).mpr
      ⟨hformed, hzlo, hordered21, hordered10, htop, ?_⟩, hj⟩
    rw [hwidth]
    exact hstepChi.le

end
end ImbalancedChen.P2CompactThirdHistorySelection
