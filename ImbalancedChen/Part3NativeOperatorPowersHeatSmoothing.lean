import ImbalancedChen.Part3GenericHeatAllPowersCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Native unbounded operator powers are constructed by genuine composition
of their linear graphs. Vertical fibers remain trivial by induction, so
each composed graph defines an actual native LinearPMap, not a formal
domain predicate. The all-orders heat graph recurrence puts every positive
time heat vector in every such native power domain and gives its exact
CFC multiplier and internally proved factorial norm bound.
-/

namespace ImbalancedChen.Part3.NativeOperatorPowersHeatSmoothing20261025a
noncomputable section
open Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Relational composition of actual linear operator graphs. -/
def composeGraphs (G K : Submodule ℂ (H × H)) : Submodule ℂ (H × H) where
  carrier := {p | ∃ w : H, (p.1, w) ∈ G ∧ (w, p.2) ∈ K}
  zero_mem' := ⟨0, G.zero_mem, K.zero_mem⟩
  add_mem' := by
    rintro p q ⟨u, hpu, hup⟩ ⟨v, hqv, hvq⟩
    exact ⟨u + v, G.add_mem hpu hqv, K.add_mem hup hvq⟩
  smul_mem' := by
    rintro c p ⟨u, hpu, hup⟩
    exact ⟨c • u, G.smul_mem c hpu, K.smul_mem c hup⟩

def powerGraph (A : H →ₗ.[ℂ] H) : ℕ → Submodule ℂ (H × H)
  | 0 => (LinearMap.id ℂ H).graph
  | n + 1 => composeGraphs (powerGraph A n) A.graph

theorem powerGraph_zero_iff (A : H →ₗ.[ℂ] H) (u v : H) :
    (u, v) ∈ powerGraph A 0 ↔ v = u := Iff.rfl

theorem powerGraph_succ_iff (A : H →ₗ.[ℂ] H) (n : ℕ) (u v : H) :
    (u, v) ∈ powerGraph A (n + 1) ↔
      ∃ w : H, (u, w) ∈ powerGraph A n ∧ (w, v) ∈ A.graph := Iff.rfl

/-- No single-valuedness supplier for a power is assumed. -/
theorem powerGraph_vertical_zero (A : H →ₗ.[ℂ] H) (n : ℕ)
    (p : H × H) (hp : p ∈ powerGraph A n) (hz : p.1 = 0) : p.2 = 0 := by
  induction n generalizing p with
  | zero =>
      change p.2 = p.1 at hp
      exact hp.trans hz
  | succ n ih =>
      obtain ⟨w, hpw, hwp⟩ := hp
      exact A.graph_fst_eq_zero_snd hwp (ih (p.1, w) hpw hz)

/-- The actual n-fold native unbounded operator power. The zeroth graph
is the identity, and each successor is true graph composition with A. -/
def nativePower (A : H →ₗ.[ℂ] H) (n : ℕ) : H →ₗ.[ℂ] H :=
  (powerGraph A n).toLinearPMap

theorem nativePower_graph_eq (A : H →ₗ.[ℂ] H) (n : ℕ) :
    (nativePower A n).graph = powerGraph A n :=
  Submodule.toLinearPMap_graph_eq _ (powerGraph_vertical_zero A n)

theorem nativePower_domain_iff (A : H →ₗ.[ℂ] H) (n : ℕ) (u : H) :
    u ∈ (nativePower A n).domain ↔ ∃ v : H, (u, v) ∈ powerGraph A n := by
  rw [LinearPMap.mem_domain_iff, nativePower_graph_eq]

variable (D : ResolventData H)

/-- A complete actual graph chain, rather than a supplier for Dom(A^n). -/
theorem heat_mem_powerGraph {s : ℝ} (hs : 0 < s) (n : ℕ) (f : H) :
    (heatOperator D s f, heatPowerOperator D s n f) ∈ powerGraph (friedrichsR D.R) n := by
  have h : (heatPowerOperator D s 0 f, heatPowerOperator D s n f) ∈
      powerGraph (friedrichsR D.R) n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        exact ⟨heatPowerOperator D s n f, ih, heatPower_native_graph D hs n f⟩
  rw [heatPowerOperator_zero_order D hs] at h
  exact h

theorem heat_mem_nativePower_graph {s : ℝ} (hs : 0 < s) (n : ℕ) (f : H) :
    (heatOperator D s f, heatPowerOperator D s n f) ∈ (nativePower (friedrichsR D.R) n).graph := by
  rw [nativePower_graph_eq]
  exact heat_mem_powerGraph D hs n f

/-- Positive time smooths EVERY actual vector into EVERY true native
operator power domain; there is no domain hypothesis on the vector. -/
theorem heat_mem_all_nativePower_domains {s : ℝ} (hs : 0 < s) (f : H) (n : ℕ) :
    heatOperator D s f ∈ (nativePower (friedrichsR D.R) n).domain :=
  LinearPMap.mem_domain_of_mem_graph (heat_mem_nativePower_graph D hs n f)

def heatPowerDomainVector (s : ℝ) (hs : 0 < s) (n : ℕ) (f : H) :
    (nativePower (friedrichsR D.R) n).domain :=
  ⟨heatOperator D s f, heat_mem_all_nativePower_domains D hs f n⟩

/-- Exact value of A^n on the actual smoothed vector is the genuine
continuous CFC multiplier lambda^n exp(-s lambda), including its endpoint. -/
theorem nativePower_heat_apply (s : ℝ) (hs : 0 < s) (n : ℕ) (f : H) :
    nativePower (friedrichsR D.R) n (heatPowerDomainVector D s hs n f) =
      heatPowerOperator D s n f :=
  LinearPMap.mem_graph_snd_inj _
    (LinearPMap.mem_graph _ (heatPowerDomainVector D s hs n f))
    (heat_mem_nativePower_graph D hs n f) rfl

theorem nativePower_heat_norm_le (s : ℝ) (hs : 0 < s) (n : ℕ) (f : H) :
    ‖nativePower (friedrichsR D.R) n (heatPowerDomainVector D s hs n f)‖ ≤
      ((n.factorial : ℝ) / s ^ n) * ‖f‖ := by
  rw [nativePower_heat_apply]
  exact heatPowerOperator_norm_le D hs n f

/-- All native power domains are dense because the genuine heat
semigroup tends strongly to the identity on every actual vector. -/
theorem dense_nativePower_domain (n : ℕ) :
    Dense ((nativePower (friedrichsR D.R) n).domain : Set H) := by
  intro f
  apply mem_closure_of_tendsto (tendsto_heatOperator_at_zero D f)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact heat_mem_all_nativePower_domains D hs f n

end
end ImbalancedChen.Part3.NativeOperatorPowersHeatSmoothing20261025a
