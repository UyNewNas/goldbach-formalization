import ImbalancedChen.P2SeedOmegaBadUniformIntegralError
import ImbalancedChen.LogPrimeBoxMesh

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine finite measurable sampler for the actual original bad domain.
The established logPrime mesh supplies exact Ico ownership; the top
endpoint is a separate singleton with its actual value. The producer
proves full closed-rectangle range and coordinate error2*step, including
the original switching kink and both bad-domain pieces. No approximation
error, checker pass, or numerical coefficient is assumed or evaluated.
-/

namespace ImbalancedChen.P2SeedOmegaFiniteMesh
noncomputable section
open Set Filter MeasureTheory Classical
open scoped BigOperators Topology
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadSpatialModulus

def node (n : ℕ) (j : Fin (n+1)) : ℝ := logPrimeMeshPoint corner a2 n j.val
def scalarCell (n : ℕ) (j : Fin (n+1)) : Set ℝ :=
  Ico (node n j) (logPrimeMeshPoint corner a2 n (j.val+1))
def step (n : ℕ) : ℝ := logPrimeMeshStep corner a2 n

theorem original_mesh_step_pos (n : ℕ) : 0<step n :=
  logPrimeMeshStep_pos (by norm_num [corner,a2]) n

theorem scalar_cell_unique {n : ℕ} {j k : Fin (n+1)} {x : ℝ}
    (hj : x ∈ scalarCell n j) (hk : x ∈ scalarCell n k) : j=k := by
  have h1 : (fun _ : Fin 1 => x) ∈ logPrimeMeshCell corner a2 n (fun _ => j) := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact hj
  have h2 : (fun _ : Fin 1 => x) ∈ logPrimeMeshCell corner a2 n (fun _ => k) := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact hk
  exact congrFun (logPrimeMeshCell_unique (by norm_num [corner,a2]) h1 h2) 0

theorem node_bounds (n : ℕ) (j : Fin (n+1)) :
    corner≤node n j ∧ node n j≤a2 := by
  have h := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
    n (fun _ => j) 0
  exact ⟨h.1,h.2.1.le.trans h.2.2⟩

def scalarSnap (n : ℕ) (x : ℝ) : ℝ :=
  if x=a2 then a2 else ∑ j : Fin (n+1),(scalarCell n j).indicator (fun _ => node n j) x

theorem scalarSnap_eq_node {n : ℕ} {j : Fin (n+1)} {x : ℝ}
    (hx : x ∈ scalarCell n j) : scalarSnap n x=node n j := by
  have htop : x<a2 := by
    have h := logPrimeMeshLoHi_bounds (d:=1) (by norm_num [corner,a2] : corner<a2)
      n (fun _ => j) 0
    exact hx.2.trans_le h.2.2
  rw [scalarSnap,if_neg htop.ne]
  rw [Finset.sum_eq_single j]
  · exact indicator_of_mem hx _
  · intro k hk hkj
    exact indicator_of_notMem (fun hxk => hkj (scalar_cell_unique hxk hx)) _
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem scalarSnap_measurable (n : ℕ) : Measurable (scalarSnap n) := by
  have hm : Measurable (fun x : ℝ =>
      ∑ j : Fin (n+1),(scalarCell n j).indicator (fun _ => node n j) x) := by
    apply Finset.measurable_sum
    intro j hj
    exact measurable_const.indicator measurableSet_Ico
  exact Measurable.ite (measurableSet_singleton a2) measurable_const hm

/-- A finite-node value, with the top singleton retained exactly. -/
theorem scalarSnap_finite_value (n : ℕ) {x : ℝ} (hx : x ∈ Icc corner a2) :
    scalarSnap n x=a2 ∨ ∃ j : Fin (n+1),scalarSnap n x=node n j := by
  by_cases htop : x=a2
  · left
    simp only [scalarSnap,htop,if_true]
  · obtain ⟨j,hj⟩ := exists_logPrimeMeshInterval corner a2 n
      (show x ∈ Ico corner a2 from ⟨hx.1,lt_of_le_of_ne hx.2 htop⟩)
    exact Or.inr ⟨j,scalarSnap_eq_node hj⟩

theorem scalarSnap_range_error (n : ℕ) {x : ℝ} (hx : x ∈ Icc corner a2) :
    scalarSnap n x ∈ Icc corner a2 ∧ |x-scalarSnap n x|≤step n := by
  by_cases htop : x=a2
  · simp only [scalarSnap,htop,if_true,sub_self,abs_zero]
    exact ⟨⟨by norm_num [corner,a2],le_rfl⟩,(original_mesh_step_pos n).le⟩
  · obtain ⟨j,hj⟩ := exists_logPrimeMeshInterval corner a2 n
      (show x ∈ Ico corner a2 from ⟨hx.1,lt_of_le_of_ne hx.2 htop⟩)
    rw [scalarSnap_eq_node hj]
    refine ⟨node_bounds n j,?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hj.1)]
    have he := logPrimeMeshPoint_succ corner a2 n j.val
    have hh := hj.2
    change x<logPrimeMeshPoint corner a2 n (j.val+1) at hh
    rw [he] at hh
    change x-logPrimeMeshPoint corner a2 n j.val≤logPrimeMeshStep corner a2 n
    linarith only [hh]

def meshSample (n : ℕ) (p : ℝ×ℝ) : ℝ×ℝ := (scalarSnap n p.1,scalarSnap n p.2)
def meshError (n : ℕ) : ℝ := 2*step n

theorem meshSample_measurable (n : ℕ) : Measurable (meshSample n) :=
  ((scalarSnap_measurable n).comp measurable_fst).prodMk
    ((scalarSnap_measurable n).comp measurable_snd)

theorem meshSample_coordinates (n : ℕ) {p : ℝ×ℝ} (hp : p ∈ primeRectangle) :
    meshSample n p ∈ primeRectangle ∧ coordinateDistance p (meshSample n p)≤meshError n := by
  have hu := scalarSnap_range_error n (show p.1 ∈ Icc corner a2 from ⟨hp.1.1,hp.2.1⟩)
  have hv := scalarSnap_range_error n (show p.2 ∈ Icc corner a2 from ⟨hp.1.2,hp.2.2⟩)
  refine ⟨⟨⟨hu.1.1,hv.1.1⟩,⟨hu.1.2,hv.1.2⟩⟩,?_⟩
  dsimp [coordinateDistance,meshSample,meshError]
  linarith only [hu.2,hv.2]

theorem meshError_nonnegative (n : ℕ) : 0≤meshError n :=
  mul_nonneg (by norm_num) (original_mesh_step_pos n).le

theorem meshError_tendsto_zero : Tendsto meshError atTop (𝓝 0) := by
  simpa only [meshError,step,mul_zero] using
    (tendsto_logPrimeMeshStep corner a2).const_mul (2:ℝ)

end
end ImbalancedChen.P2SeedOmegaFiniteMesh
