import ImbalancedChen.Part3ActualCylinderPhysicalFriedrichs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Genuine maximal native powers of the actual physical cylinder operator.
The kth graph is constructed by composing the ACTUAL native graph k
times, with a genuine intermediate-domain witness at every stage. Its
zero fiber is proved trivial inductively, giving an actual LinearPMap.
The exact recursive graph and domain formulas are proved, and the first
power equals the independently constructed physical Friedrichs operator.

The pinned LinearPMap.comp requires the entire preceding domain's image
to lie in the next domain. That would lose the maximal domain of an
unbounded power, so no such inclusion is assumed here. No power-domain
or spectral-domain supplier is an input. Whole cylinder only.
-/

namespace ImbalancedChen.Part3.ActualCylinderNativePowers20261026b
noncomputable section
open Set
open ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderPhysicalFriedrichs20261026b

def cylinderPowerGraph : ℕ → Submodule ℂ (zeroMeanCylinder × zeroMeanCylinder)
  | 0 =>
    { carrier := {p | p.2 = p.1}
      zero_mem' := rfl
      add_mem' := by rintro p q hp hq; change p.2 + q.2 = p.1 + q.1; rw [hp, hq]
      smul_mem' := by rintro c p hp; change c • p.2 = c • p.1; rw [hp] }
  | k + 1 =>
    { carrier := {p | ∃ w : zeroMeanCylinder,
        (p.1, w) ∈ actualCylinderFriedrichs.graph ∧ (w, p.2) ∈ cylinderPowerGraph k}
      zero_mem' := ⟨0, actualCylinderFriedrichs.graph.zero_mem, (cylinderPowerGraph k).zero_mem⟩
      add_mem' := by
        rintro p q ⟨w, hp, hp'⟩ ⟨z, hq, hq'⟩
        exact ⟨w + z, actualCylinderFriedrichs.graph.add_mem hp hq,
          (cylinderPowerGraph k).add_mem hp' hq'⟩
      smul_mem' := by
        rintro c p ⟨w, hp, hp'⟩
        exact ⟨c • w, actualCylinderFriedrichs.graph.smul_mem c hp,
          (cylinderPowerGraph k).smul_mem c hp'⟩ }

theorem cylinderPowerGraph_zero_fiber (k : ℕ) (p : zeroMeanCylinder × zeroMeanCylinder)
    (hp : p ∈ cylinderPowerGraph k) (hz : p.1 = 0) : p.2 = 0 := by
  induction k generalizing p with
  | zero => exact hp.trans hz
  | succ k ih =>
    obtain ⟨w, hA, hpow⟩ := hp
    have hw : w = 0 := LinearPMap.mem_graph_snd_inj actualCylinderFriedrichs
      hA actualCylinderFriedrichs.graph.zero_mem hz
    exact ih (w, p.2) hpow hw

def actualCylinderPower (k : ℕ) : zeroMeanCylinder →ₗ.[ℂ] zeroMeanCylinder :=
  (cylinderPowerGraph k).toLinearPMap

theorem actualCylinderPower_graph (k : ℕ) :
    (actualCylinderPower k).graph = cylinderPowerGraph k :=
  Submodule.toLinearPMap_graph_eq _ (cylinderPowerGraph_zero_fiber k)

theorem actualCylinderPower_zero_graph_iff (u v : zeroMeanCylinder) :
    (u, v) ∈ (actualCylinderPower 0).graph ↔ v = u := by
  rw [actualCylinderPower_graph]
  rfl

/-- Exact maximal recursive graph: both intermediate-domain obligations
are retained rather than hidden by a total-map convention. -/
theorem actualCylinderPower_succ_graph_iff (k : ℕ) (u v : zeroMeanCylinder) :
    (u, v) ∈ (actualCylinderPower (k + 1)).graph ↔
      ∃ w : zeroMeanCylinder, (u, w) ∈ actualCylinderFriedrichs.graph ∧
        (w, v) ∈ (actualCylinderPower k).graph := by
  rw [actualCylinderPower_graph, actualCylinderPower_graph]
  rfl

theorem actualCylinderPower_one : actualCylinderPower 1 = actualCylinderFriedrichs := by
  apply LinearPMap.eq_of_eq_graph
  apply SetLike.ext
  rintro ⟨u, v⟩
  rw [actualCylinderPower_succ_graph_iff, actualCylinderPower_zero_graph_iff]
  constructor
  · rintro ⟨w, hw, hEq⟩
    simpa only [← hEq] using hw
  · intro h
    exact ⟨v, h, rfl⟩

theorem actualCylinderPower_zero_domain : (actualCylinderPower 0).domain = ⊤ := by
  apply SetLike.ext
  intro u
  constructor
  · intro h; exact Submodule.mem_top
  · intro h
    exact LinearPMap.mem_domain_iff.mpr
      ⟨u, (actualCylinderPower_zero_graph_iff u u).mpr rfl⟩

theorem actualCylinderPower_succ_domain_iff (k : ℕ) (u : zeroMeanCylinder) :
    u ∈ (actualCylinderPower (k + 1)).domain ↔
      ∃ w : zeroMeanCylinder, (u, w) ∈ actualCylinderFriedrichs.graph ∧
        w ∈ (actualCylinderPower k).domain := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, hpow⟩ := (actualCylinderPower_succ_graph_iff k u v).mp hv
    exact ⟨w, hw, LinearPMap.mem_domain_iff.mpr ⟨v, hpow⟩⟩
  · rintro ⟨w, hw, hdom⟩
    obtain ⟨v, hv⟩ := LinearPMap.mem_domain_iff.mp hdom
    exact ⟨v, (actualCylinderPower_succ_graph_iff k u v).mpr ⟨w, hw, hv⟩⟩

end
end ImbalancedChen.Part3.ActualCylinderNativePowers20261026b
