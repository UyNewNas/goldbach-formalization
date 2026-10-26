import ImbalancedChen.P2SeedOmegaMeshAdmissibility

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Concrete symbolic finite original-prime meshes now converge uniformly
to the ACTUAL bad Gamma5 integral on the whole alpha>=2 family.
Measurability, integrability, coordinate proximity, and kernel modulus
are all supplied by this chain; no AdmissibleSample/error/cap premise
is exported here. Nodes are exact rational original-prime exponents.
No numeric mesh/certificate was evaluated and the required J2 gain is OPEN.
-/

namespace ImbalancedChen.P2SeedOmegaFiniteMeshLimit
noncomputable section
open Set Filter
open scoped Topology
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadGlobalCost
open P2SeedOmegaBadUniformIntegralError
open P2SeedOmegaFiniteMesh
open P2SeedOmegaMeshAdmissibility

def rationalNode (n : ℕ) (j : Fin (n+1)) : ℚ :=
  19/58+(j.val:ℚ)*((10/29-19/58)/(n+1:ℚ))

/-- The finite sampler nodes have precisely rational original endpoints. -/
theorem rationalNode_cast (n : ℕ) (j : Fin (n+1)) :
    (rationalNode n j:ℝ)=node n j := by
  simp only [rationalNode,node,logPrimeMeshPoint,logPrimeMeshStep,corner,a2,
    Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_natCast,
    Rat.cast_ofNat,Rat.cast_one,Nat.cast_add,Nat.cast_one]

def meshCost (n : ℕ) (alpha : ℝ) : ℝ := sampledCost alpha (meshSample n)

/-- Explicit genuine mesh error; its constant is uniform in alpha and
does not use a numerical passing value or any pre-assumed integral bound. -/
theorem actual_finite_mesh_error (n : ℕ) {alpha : ℝ} (ha : 2≤alpha) :
    |actualBadCost alpha-meshCost n alpha|≤8192*step n := by
  have h := actual_bad_cost_sample_error ha (finite_mesh_admissible ha n)
  simpa only [meshCost,meshError,mul_assoc,show (4096:ℝ)*2=8192 by norm_num] using h

theorem original_finite_mesh_normalized_error (n : ℕ) {alpha : ℝ} (ha : 2≤alpha) :
    |(-actualBadCost alpha/5)-(-meshCost n alpha/5)|≤(8192/5:ℝ)*step n := by
  have h := original_normalized_bad_contribution_error ha (finite_mesh_admissible ha n)
  convert h using 1 <;> dsimp [meshCost,meshError] <;> ring

/-- The mesh threshold precedes EVERY alpha>=2. This is uniform
convergence of an actual concrete finite family, not an assumed modulus. -/
theorem finite_mesh_uniform_in_unbounded_alpha {epsilon : ℝ} (he : 0<epsilon) :
    ∃ N : ℕ,∀ n : ℕ,N≤n→∀ alpha : ℝ,2≤alpha→
      |actualBadCost alpha-meshCost n alpha|<epsilon := by
  have hlim : Tendsto (fun n : ℕ =>8192*step n) atTop (𝓝 0) := by
    simpa only [step,mul_zero] using
      (tendsto_logPrimeMeshStep corner a2).const_mul (8192:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds he))
  refine ⟨N,?_⟩
  intro n hn alpha ha
  exact (actual_finite_mesh_error n ha).trans_lt (hN n hn)

/-- Even arbitrary, unbounded admissible alpha_n have vanishing
concrete-mesh integration error along the SAME mesh sequence. -/
theorem concrete_mesh_error_tendsto_zero (A : ℕ → ℝ) (ha : ∀ n,2≤A n) :
    Tendsto (fun n =>meshCost n (A n)-actualBadCost (A n)) atTop (𝓝 0) := by
  exact uniform_actual_bad_sample_error_tendsto_zero
    (Eventually.of_forall ha)
    (Eventually.of_forall (fun n =>finite_mesh_admissible (ha n) n))
    meshError_tendsto_zero

theorem concrete_mesh_cost_tendsto {alpha : ℝ} (ha : 2≤alpha) :
    Tendsto (fun n =>meshCost n alpha) atTop (𝓝 (actualBadCost alpha)) := by
  exact sampled_bad_cost_tendsto ha (Eventually.of_forall (fun _ =>ha))
    (Eventually.of_forall (fun n =>finite_mesh_admissible ha n))
    meshError_tendsto_zero tendsto_const_nhds

end
end ImbalancedChen.P2SeedOmegaFiniteMeshLimit
