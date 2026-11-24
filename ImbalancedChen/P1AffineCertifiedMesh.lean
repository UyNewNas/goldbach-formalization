import ImbalancedChen.P1AffineBoxCompleteness
import ImbalancedChen.LogPrimeBoxMesh
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

An explicit finite half-open grid whose CLOSED boxes are tested by the
existing affine endpoint certificate. All regular points are eventually
covered. Rejected boxes are bounded by actual proper-wall strips; their
L1 mass vanishes. No quantitative prime-count estimate is inferred from
Lebesgue nullity. Refinement is after the fixed finite programs and before N.
-/
namespace ImbalancedChen.P1AffineCertifiedMesh
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter MeasureTheory P1FiniteAffineDecisionProgram P1AffineBoxCompleteness

abbrev Label (k m : ℕ) := Fin k → Fin (m + 1)
def cube (k : ℕ) : Set (Fin k → ℝ) := logPrimeBox (fun _ => 0) (fun _ => 1)
def lo {k : ℕ} (m : ℕ) (j : Label k m) := logPrimeMeshLo 0 1 m j
def hi {k : ℕ} (m : ℕ) (j : Label k m) := logPrimeMeshHi 0 1 m j
def cell {k : ℕ} (m : ℕ) (j : Label k m) := logPrimeMeshCell 0 1 m j
def center {k : ℕ} (m : ℕ) (j : Label k m) : Fin k → ℝ :=
  fun i => (lo m j i + hi m j i) / 2

theorem center_bounds {k : ℕ} (m : ℕ) (j : Label k m) :
    (∀ i, lo m j i ≤ center m j i) ∧ (∀ i, center m j i ≤ hi m j i) := by
  have hw (i : Fin k) : lo m j i < hi m j i :=
    (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m j i).2.1
  constructor <;> intro i <;> dsimp [center] <;> linarith [hw i]

/-- The center proposes a signature; acceptance checks the ENTIRE closed
box. This is not a midpoint-only decision test. -/
def approved {k : ℕ} (p : Program k) (m : ℕ) : Finset (Label k m) :=
  Finset.univ.filter fun j => p.BoxCertificate (p.signature (center m j)) (lo m j) (hi m j)

theorem mem_approved {k : ℕ} (p : Program k) (m : ℕ) (j : Label k m) :
    j ∈ approved p m ↔ p.BoxCertificate (p.signature (center m j)) (lo m j) (hi m j) := by
  simp only [approved, Finset.mem_filter, Finset.mem_univ, true_and]

def covered {k : ℕ} (p : Program k) (m : ℕ) : Set (Fin k → ℝ) :=
  ⋃ j ∈ approved p m, cell m j

theorem measurableSet_covered {k : ℕ} (p : Program k) (m : ℕ) :
    MeasurableSet (covered p m) := by
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro _
  exact measurableSet_logPrimeMeshCell 0 1 m j

theorem certificate_on_approved {k : ℕ} (p : Program k) (m : ℕ) (j : Label k m)
    (hj : j ∈ approved p m) (t : Fin k → ℝ)
    (hl : ∀ i, lo m j i ≤ t i) (hu : ∀ i, t i ≤ hi m j i) :
    t ∈ p.region (p.signature (center m j)) ∧
      (p.table (p.signature (center m j))).eval t = p.eval t :=
  p.boxCertificate_sound _ _ _ ((mem_approved p m j).mp hj) t hl hu

/-- Any surrounding cell of this mesh is certified, not a bespoke box
chosen after seeing a descendant. The witness signature is then identified
with the actual center signature by whole-box soundness. -/
theorem approved_of_separated {k : ℕ} (p : Program k) (m : ℕ)
    (t : Fin k → ℝ) (j : Label k m) (ht : t ∈ cell m j)
    (hs : Separated p (logPrimeMeshStep 0 1 m) t) : j ∈ approved p m := by
  have hw (i : Fin k) : hi m j i = lo m j i + logPrimeMeshStep 0 1 m :=
    logPrimeMeshHi_eq_lo_add_step 0 1 m j i
  have hb := mem_logPrimeMeshCell.mp ht
  have hc := boxCertificate_of_separated p (logPrimeMeshStep 0 1 m)
    (logPrimeMeshStep_pos (by norm_num : (0 : ℝ) < 1) m) (lo m j) (hi m j) t
    (fun i => by linarith [(hb i).2, hw i])
    (fun i => by linarith [(hb i).1, hw i]) hs
  have hm := (p.boxCertificate_sound _ _ _ hc (center m j)
    (center_bounds m j).1 (center_bounds m j).2).1
  change p.signature (center m j) = p.signature t at hm
  apply (mem_approved p m j).mpr
  rwa [hm]

theorem covered_of_separated {k : ℕ} (p : Program k) (m : ℕ)
    (t : Fin k → ℝ) (ht : t ∈ cube k)
    (hs : Separated p (logPrimeMeshStep 0 1 m) t) : t ∈ covered p m := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 1 m ht
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨approved_of_separated p m t j hj hs, hj⟩⟩

/-- Uniform mesh for an entire margin stratum; no compactness assumption
or pointwise mesh choice is used. Every subsequent finer mesh also works. -/
theorem exists_mesh_for_margin {k : ℕ} (p : Program k) (eta : ℝ) (heta : 0 < eta) :
    ∃ m0 : ℕ, ∀ m ≥ m0, ∀ t : Fin k → ℝ, t ∈ cube k →
      Separated p eta t → t ∈ covered p m := by
  obtain ⟨m0, hm⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep 0 1).eventually (gt_mem_nhds heta))
  refine ⟨m0, ?_⟩
  intro m hmt t ht hs
  exact covered_of_separated p m t ht (separated_mono p (hm m hmt).le hs)

/-- Failure has a concrete finite affine-strip witness. Zero-coefficient
comparisons, including identities, are absent from this exceptional set. -/
theorem uncovered_has_proper_strip {k : ℕ} (p : Program k) (m : ℕ)
    (t : Fin k → ℝ) (ht : t ∈ cube k) (hn : t ∉ covered p m) :
    ∃ ab : p.Label × p.Label,
      let a := ab.1.val.sub ab.2.val
      a.coefficient ≠ 0 ∧
        |a.eval t| < logPrimeMeshStep 0 1 m * (a.slopeMass + 1) := by
  have hns : ¬Separated p (logPrimeMeshStep 0 1 m) t :=
    fun h => hn (covered_of_separated p m t ht h)
  simpa only [Separated, not_forall, not_imp, not_le] using hns

theorem eventually_covered {k : ℕ} (p : Program k) (t : Fin k → ℝ)
    (ht : t ∈ cube k) (hr : Regular p t) :
    ∀ᶠ m : ℕ in atTop, t ∈ covered p m := by
  filter_upwards [eventually_separated p t hr (logPrimeMeshStep 0 1)
    (tendsto_logPrimeMeshStep 0 1)] with m hm
  exact covered_of_separated p m t ht hm

/-- A finite family can have different own ranks. Only injective embeddings
into the common analysis space are permitted. -/
structure Spec (d : ℕ) where
  rank : ℕ
  program : Program rank
  embed : Fin rank ↪ Fin d

def Spec.project {d : ℕ} (s : Spec d) (t : Fin d → ℝ) : Fin s.rank → ℝ :=
  fun i => t (s.embed i)

theorem Spec.continuous_project {d : ℕ} (s : Spec d) : Continuous s.project := by
  unfold Spec.project
  fun_prop

theorem Spec.project_mem_cube {d : ℕ} (s : Spec d) {t : Fin d → ℝ}
    (ht : t ∈ cube d) : s.project t ∈ cube s.rank := by
  exact mem_logPrimeBox.mpr (fun i => mem_logPrimeBox.mp ht (s.embed i))

def accepted {d : ℕ} {ι : Type*} (s : ι → Spec d) (m : ℕ) : Set (Fin d → ℝ) :=
  ⋂ i, (s i).project ⁻¹' covered (s i).program m

def rejected {d : ℕ} {ι : Type*} (s : ι → Spec d) (m : ℕ) : Set (Fin d → ℝ) :=
  cube d \ accepted s m

theorem measurableSet_accepted {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) (m : ℕ) : MeasurableSet (accepted s m) :=
  MeasurableSet.iInter (fun i => (measurableSet_covered (s i).program m).preimage
    (s i).continuous_project.measurable)

theorem measurableSet_rejected {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) (m : ℕ) : MeasurableSet (rejected s m) :=
  (measurableSet_logPrimeBox _ _).diff (measurableSet_accepted s m)

/-- A joint rejected box has a wall in one OWN-rank program, evaluated on
its own projection. This is not deletion of a projected child wall. -/
theorem rejected_has_proper_strip {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) (m : ℕ) (t : Fin d → ℝ) (ht : t ∈ rejected s m) :
    ∃ i : ι, ∃ ab : (s i).program.Label × (s i).program.Label,
      let a := ab.1.val.sub ab.2.val
      a.coefficient ≠ 0 ∧
      |a.eval ((s i).project t)| < logPrimeMeshStep 0 1 m * (a.slopeMass + 1) := by
  have hn : ¬∀ i, (s i).project t ∈ covered (s i).program m := by
    intro h
    exact ht.2 (mem_iInter.mpr h)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  obtain ⟨ab, ha⟩ := uncovered_has_proper_strip (s i).program m ((s i).project t)
    ((s i).project_mem_cube ht.1) hi
  exact ⟨i, ab, ha⟩

/-- Almost-everywhere eventual acceptance is DERIVED from proper linear
walls. It is not an assumed coverage premise of the loss theorem. -/
theorem ae_eventually_not_rejected {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) :
    ∀ᵐ t : Fin d → ℝ ∂volume, ∀ᶠ m : ℕ in atTop, t ∉ rejected s m := by
  have hreg : ∀ᵐ t : Fin d → ℝ ∂volume,
      ∀ i, Regular (s i).program ((s i).project t) :=
    ae_all_iff.mpr (fun i => ae_regular_projection (s i).program (s i).embed)
  filter_upwards [hreg] with t ht
  by_cases hc : t ∈ cube d
  · have ha : ∀ᶠ m : ℕ in atTop, t ∈ accepted s m := by
      have hall : ∀ᶠ m : ℕ in atTop,
          ∀ i, (s i).project t ∈ covered (s i).program m :=
        eventually_all.mpr (fun i => eventually_covered (s i).program ((s i).project t)
          ((s i).project_mem_cube hc) (ht i))
      exact hall.mono (fun _ h => mem_iInter.mpr h)
    exact ha.mono (fun _ hm hn => hn.2 hm)
  · exact Filter.Eventually.of_forall (fun _ hn => hc hn.1)

def omitted {d : ℕ} {ι : Type*} (s : ι → Spec d) (domain : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∫ t in domain, (rejected s m).indicator (fun t => ‖f t‖) t

theorem omitted_eq_sdiff {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) (domain : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (m : ℕ) :
    omitted s domain f m = ∫ t in domain ∩ rejected s m, ‖f t‖ := by
  unfold omitted
  rw [setIntegral_indicator (measurableSet_rejected s m)]

/-- Works for singular integrable kernels as well as volume. Integrability
is explicit; no particular archived kernel or arithmetic error is assumed. -/
theorem tendsto_omitted {d : ℕ} {ι : Type*} [Fintype ι]
    (s : ι → Spec d) (domain : Set (Fin d → ℝ))
    (f : (Fin d → ℝ) → ℝ) (hf : IntegrableOn f domain) :
    Tendsto (omitted s domain f) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict domain)
    (F := fun m => (rejected s m).indicator (fun t => ‖f t‖))
    (f := fun _ => (0 : ℝ)) (fun t => ‖f t‖)
    (fun m => (hf.norm.indicator (measurableSet_rejected s m)).aestronglyMeasurable)
    hf.norm
    (fun m => Filter.Eventually.of_forall fun t => by
      simpa only [norm_norm] using
        (norm_indicator_le_norm_self (s := rejected s m) (fun t => ‖f t‖) t))
    (show ∀ᵐ t ∂volume.restrict domain,
      Tendsto (fun m => (rejected s m).indicator (fun t => ‖f t‖) t) atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [ae_restrict_of_ae (ae_eventually_not_rejected s)] with t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [ht] with m hm
      simp only [indicator_of_notMem hm])
  simpa only [omitted, integral_zero] using hlim

end
end ImbalancedChen.P1AffineCertifiedMesh
