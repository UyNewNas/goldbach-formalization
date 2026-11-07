import ImbalancedChen.P2OriginalFiniteWCommonBuffer

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite rational strict-W cover now has one actual corrected-grid mesh
threshold. Every later mesh, not an x-dependent mesh, works for the whole
compact chamber. Canonical exponentCode owns each actual point; its closed
endpoint vectors refine a single licensed box. The cap rounding loss is
quantified explicitly before N. Full functional/compiler loss is separate.
-/

namespace ImbalancedChen.P2OriginalCommonActualWMesh

noncomputable section
open scoped Classical Topology
open Set Filter
open P2PhysicalIncomingPrefixCells
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerOrderedWBranch
open P2OriginalLowerWThirdPhysicalRow
open P2OriginalStrictWLocalRationalCover
open P2OriginalLocalWBoxMeshLicence
open P2OriginalFiniteWCommonBuffer

def liftSlot (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩

def canonicalThirdCode (S : CompactStart) (mesh : ℕ) (x : Point) : Code mesh :=
  fun i => if hi : i.val < 3 then
    (exponentCode (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh x⟨i.val, hi⟩, false)
    else (none, false)

theorem canonicalThirdCode_at (S : CompactStart) (mesh : ℕ)
    (x : Point) (i : Fin 3) :
    canonicalThirdCode S mesh x (liftSlot i) =
      (exponentCode (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh (x i), false) := by
  simp [canonicalThirdCode, liftSlot]

theorem canonicalThirdCode_unmarked (S : CompactStart) (mesh : ℕ) (x : Point) :
    ∀ i : Fin 5, (canonicalThirdCode S mesh x i).2 = false := by
  intro i
  unfold canonicalThirdCode
  split <;> rfl

theorem canonicalThirdCode_prefix (S : CompactStart) (mesh : ℕ) (x : Point) :
    canonicalThirdCode S mesh x = prefixCode 3 (canonicalThirdCode S mesh x) := by
  funext i
  by_cases hi : i.val < 3 <;> simp [canonicalThirdCode, prefixCode, hi]

def meshLower (S : CompactStart) (mesh : ℕ) (x : Point) : Point :=
  fun i => qLo S (canonicalThirdCode S mesh x) (liftSlot i)

def meshUpper (S : CompactStart) (mesh : ℕ) (x : Point) : Point :=
  fun i => qHi S (canonicalThirdCode S mesh x) (liftSlot i)

private theorem codeCell_width (S : CompactStart) (mesh : ℕ) (c : CellCode mesh) :
    cellUpper S mesh c - cellLower S mesh c ≤
      logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh := by
  have hpos := logPrimeMeshStep_pos
    (show (S.epsilon : ℝ) < startCutoff S.start by exact_mod_cast S.epsilon_lt_start) mesh
  cases c with
  | none => simpa [cellUpper, cellLower] using hpos.le
  | some j =>
      simp only [cellUpper, cellLower, logPrimeMeshPoint_succ]
      linarith

theorem canonical_endpoint_bounds (S : CompactStart) (mesh : ℕ) (x : Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ))
    (i : Fin 3) :
    meshLower S mesh x i ≤ x i ∧ x i ≤ meshUpper S mesh x i ∧
      meshUpper S mesh x i - meshLower S mesh x i ≤
        logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh := by
  have hm := exponentCode_membership (m := mesh) (hx i)
  have hlo := cellLower_le_of_mem S mesh hm
  have hhi := mem_exponentCell_le_upper S mesh hm
  have hw := codeCell_width S mesh
    (exponentCode (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh (x i))
  simpa [meshLower, meshUpper, qLo, qHi, canonicalThirdCode_at,
    qCellLo_cast, qCellHi_cast] using And.intro hlo (And.intro hhi hw)

theorem canonical_endpoint_dist (S : CompactStart) (mesh : ℕ) (x : Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ)) :
    dist (meshLower S mesh x) x ≤
        logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh ∧
      dist (meshUpper S mesh x) x ≤
        logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh := by
  have hstep := (logPrimeMeshStep_pos
    (show (S.epsilon : ℝ) < startCutoff S.start by exact_mod_cast S.epsilon_lt_start) mesh).le
  constructor <;> apply (dist_pi_le_iff hstep).2 <;> intro i
  · have hb := canonical_endpoint_bounds S mesh x hx i
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith
  · have hb := canonical_endpoint_bounds S mesh x hx i
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> linarith

theorem strict_point_in_compact_coordinates (S : CompactStart) (rho : ℝ)
    (x : Point) (hx : StrictWPoint S rho x) :
    ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ) := by
  intro i
  fin_cases i
  · exact ⟨((hx.cutoff_lower.trans hx.order21).trans hx.order10).le, hx.cutoff_upper.le⟩
  · exact ⟨(hx.cutoff_lower.trans hx.order21).le,
      (hx.order10.trans hx.cutoff_upper).le⟩
  · exact ⟨hx.cutoff_lower.le, ((hx.order21.trans hx.order10).trans hx.cutoff_upper).le⟩

-- Metric Lebesgue-number uniformity turns the existing finite cover into
-- actual endpoint containment for every point of K at every mesh>=M.
theorem common_mesh_refines_cover {ι : Type*} [Fintype ι]
    (S : CompactStart) {rho : ℝ} (R : ι → LocalWBox S rho)
    (K : Set Point) (hK : IsCompact K)
    (hcover : K ⊆ ⋃ q, (R q).interiorSet)
    (hcoords : ∀ x ∈ K, ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ))
    (tau : ℝ) (htau : 0 < tau) :
    ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh < tau ∧
      ∀ x ∈ K, ∃ q : ι, CellRefines (R q) (canonicalThirdCode S mesh x) := by
  obtain ⟨d, hd, hballs⟩ := lebesgue_number_lemma_of_metric hK
    (fun q => (R q).interior_isOpen) hcover
  have hsmall := (tendsto_logPrimeMeshStep (S.epsilon : ℝ)
    (startCutoff S.start : ℝ)).eventually (gt_mem_nhds (lt_min hd htau))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  refine ⟨M, ?_⟩
  intro mesh hmesh
  have hstep : logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh < min d tau :=
    hM mesh hmesh
  refine ⟨lt_of_lt_of_le hstep (min_le_right _ _), ?_⟩
  intro x hx
  obtain ⟨q, hq⟩ := hballs x hx
  have hend := canonical_endpoint_dist S mesh x (hcoords x hx)
  have hlo : meshLower S mesh x ∈ (R q).interiorSet :=
    hq (lt_of_le_of_lt hend.1 (lt_of_lt_of_le hstep (min_le_left _ _)))
  have hhi : meshUpper S mesh x ∈ (R q).interiorSet :=
    hq (lt_of_le_of_lt hend.2 (lt_of_lt_of_le hstep (min_le_left _ _)))
  refine ⟨q, ?_⟩
  intro i
  constructor
  · have h := (hlo i).1.le
    exact_mod_cast h
  · have h := (hhi i).2.le
    exact_mod_cast h

-- This is the actual cap used by WThirdTable, not a cap approximation
-- parameter. The exact formula identifies the two distinct loss sources.
theorem W_cap_loss_formula (S : CompactStart) (mesh : ℕ) (x : Point) (r : ℚ) :
    B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) =
      (r : ℝ) + (3 / 8 : ℝ) * (meshUpper S mesh x 2 - x 2) := by
  simp only [B, Lambda, wCap, meshUpper, liftSlot]
  push_cast
  ring

theorem W_cap_loss_le (S : CompactStart) (mesh : ℕ) (x : Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ))
    (r : ℚ) (hr : 0 ≤ r) :
    0 ≤ B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) ∧
    B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) ≤
      (r : ℝ) + (3 / 8 : ℝ) *
        logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh := by
  have hb := canonical_endpoint_bounds S mesh x hx 2
  have hrR : (0 : ℝ) ≤ r := by exact_mod_cast hr
  rw [W_cap_loss_formula]
  constructor <;> linarith

-- One positive r and one actual mesh threshold are chosen for the entire
-- compact strict-W chamber before any arithmetic N. All later meshes keep
-- the exact common W licence and have cap loss below the prescribed tau.
theorem exists_common_actual_W_mesh (S : CompactStart) (rho : ℝ)
    (K : Set Point) (hK : IsCompact K)
    (hstrict : ∀ x ∈ K, StrictWPoint S rho x)
    (tau : ℚ) (htau : 0 < tau) :
    ∃ (F : Finset (LocalWBox S rho)) (r : ℚ)
      (R : {Q : LocalWBox S rho // Q ∈ F} → LocalWBox S rho) (M : ℕ),
      0 < r ∧ r ≤ tau / 2 ∧
      ∀ mesh : ℕ, M ≤ mesh → ∀ x ∈ K,
        ∃ q, CellRefines (R q) (canonicalThirdCode S mesh x) ∧
          WBoxCheck S (canonicalThirdCode S mesh x) rho r r ∧
          0 ≤ B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) ∧
          B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) < tau := by
  obtain ⟨F, r, R, hr, hrtau, hR, hcover⟩ :=
    compact_strict_chamber_common_buffer_cover S rho K hK hstrict (tau / 2) (by positivity)
  have htauR : (0 : ℝ) < tau := by exact_mod_cast htau
  obtain ⟨M, hM⟩ := common_mesh_refines_cover S R K hK hcover
    (fun x hx => strict_point_in_compact_coordinates S rho x (hstrict x hx)) tau htauR
  refine ⟨F, r, R, M, hr, hrtau, ?_⟩
  intro mesh hmesh x hx
  obtain ⟨hstep, hcells⟩ := hM mesh hmesh
  obtain ⟨q, hq⟩ := hcells x hx
  have hW := refined_cell_WBoxCheck S (R q) (canonicalThirdCode S mesh x) hq
    (fun i _ => canonicalThirdCode_unmarked S mesh x i)
  have hbeta := (hR q).2.2.1
  have hdelta := (hR q).2.2.2
  have hWactual : WBoxCheck S (canonicalThirdCode S mesh x) rho r r := by
    simpa only [hbeta, hdelta] using hW
  have hcoord := strict_point_in_compact_coordinates S rho x (hstrict x hx)
  have hloss := W_cap_loss_le S mesh x hcoord r hr.le
  have hrR : (r : ℝ) ≤ (tau : ℝ) / 2 := by exact_mod_cast hrtau
  exact ⟨q, hq, hWactual, hloss.1, by linarith [hloss.2]⟩


-- The cap error enters the original ordinary query at the SAME physical
-- prefix and denominator. This does not yet pay the stored whole-box
-- query's additional coordinate/denominator rounding errors.
theorem actual_point_query_loss (S : CompactStart) (mesh : ℕ) (x : Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ))
    (r : ℚ) (tau : ℝ) (htau : 0 < tau)
    (hloss0 : 0 ≤ B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ))
    (hloss : B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ) < tau) :
    0 ≤ (B (x 2) - (x 0 + x 1 + x 2)) / x 2 -
      ((wCap S (canonicalThirdCode S mesh x) r : ℝ) - (x 0 + x 1 + x 2)) / x 2 ∧
    (B (x 2) - (x 0 + x 1 + x 2)) / x 2 -
      ((wCap S (canonicalThirdCode S mesh x) r : ℝ) - (x 0 + x 1 + x 2)) / x 2 <
        tau / (S.epsilon : ℝ) := by
  have heps : (0 : ℝ) < S.epsilon := by exact_mod_cast S.epsilon_pos
  have hz : 0 < x 2 := lt_of_lt_of_le heps (hx 2).1
  have heq :
      (B (x 2) - (x 0 + x 1 + x 2)) / x 2 -
        ((wCap S (canonicalThirdCode S mesh x) r : ℝ) - (x 0 + x 1 + x 2)) / x 2 =
      (B (x 2) - (wCap S (canonicalThirdCode S mesh x) r : ℝ)) / x 2 := by ring
  rw [heq]
  refine ⟨div_nonneg hloss0 hz.le, ?_⟩
  exact (div_lt_div_of_pos_right hloss hz).trans_le
    (div_le_div_of_nonneg_left htau.le heps (hx 2).1)

end
end ImbalancedChen.P2OriginalCommonActualWMesh
