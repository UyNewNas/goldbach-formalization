import ImbalancedChen.P4AOriginalFiniteFallbackActualChangedSupport
import ImbalancedChen.P4AFull87FiniteWallRate

/-!
SOURCE_ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

The original finite wall catalogue bounds the changed mass of the actual
positive-cutoff policy, uniformly over the complete tag function. The two
rate constants are chosen before the tag function and before the target.
This is not a compiler-reserve expenditure or a same-rho PP estimate.
-/
namespace ImbalancedChen.P4AOriginalFiniteFallbackActualTaggedRate
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackRange (Bounded)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AUpperTaggedParityCompiler
open P4AOriginalFiniteFallbackWallRate (Charts centresFor count)

/-- One original catalogue and one pair of rate constants work for every
tag function on the actual policy and its physical rough carrier. -/
theorem actual_uniform_tagged_rate
    (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (D : OriginalData) (he : 0 ≤ D.e) :
    ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ B : ℝ, 0 ≤ B →
      ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ omega v tau : ℝ,
      0 < omega → omega ≤ v → v ≤ 1 → 0 < tau →
      3 ≤ (N : ℝ)^omega → E ≤ omega*Real.log (N : ℝ) →
      ∀ tags : ℕ → List Bool,
      (B/omega)*changedMass (F T delta n D omega N) tags N cap
          ((N : ℝ)^omega) ((N : ℝ)^v) tau ≤
        ((count T delta n D : ℝ)*150*B*tau +
          (count T delta n D : ℝ)*10*B*K/Real.log (N : ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hh⟩ :=
    P4AFull87FiniteWallRate.exists_finite_rate (ι := Charts T delta n D)
  refine ⟨K,E,hK,hE,?_⟩
  intro B hB N cap hN hEven omega v tau hw hv hv1 ht h3 hlog tags
  apply hh B hB N cap (by omega) hEven omega v tau hw hv hv1 ht.le h3 hlog
    (centresFor T delta n D N (P4AHeldTaggedCompilerSupport.J0 omega))
  intro x hx
  obtain ⟨hU,hc⟩ := Finset.mem_filter.mp hx
  exact P4AOriginalFiniteFallbackActualChangedSupport.actual_changed_seen
    T hT delta hd n D he N cap hN omega v tau hw hv ht tags hU hc

/-- After fixing the original positive rough exponent and physical cutoff,
one threshold works for all tags, finite caps, weights and positive widths. -/
theorem actual_uniform_tagged_rate_eventually
    (T : Bank) (hT : Bounded T) (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (D : OriginalData) (he : 0 ≤ D.e)
    (omega v : ℝ) (hw : 0 < omega) (hv : omega ≤ v) (hv1 : v ≤ 1) :
    ∃ K : ℝ, 1 < K ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (cap : ℕ) (tau B : ℝ), 0 < tau → 0 ≤ B → ∀ tags : ℕ → List Bool,
      (B/omega)*changedMass (F T delta n D omega N) tags N cap
          ((N : ℝ)^omega) ((N : ℝ)^v) tau ≤
        ((count T delta n D : ℝ)*150*B*tau +
          (count T delta n D : ℝ)*10*B*K/Real.log (N : ℝ))/omega^5 := by
  obtain ⟨K,E,hK,hE,hRate⟩ := actual_uniform_tagged_rate T hT delta hd n D he
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow := (tendsto_rpow_atTop hw).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 3 ≤ (N : ℝ)^omega ∧
      E/omega ≤ Real.log (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, hpow.eventually (eventually_ge_atTop 3),
      hlog.eventually (eventually_ge_atTop (E/omega))] with N hN h3 hE' using ⟨hN,h3,hE'⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hlarge
  refine ⟨K,hK,N0,(hN0 _ le_rfl).1,?_⟩
  intro N hN hEven cap tau B ht hB tags
  obtain ⟨hN2,h3,hE'⟩ := hN0 N hN
  have hwlog : E ≤ omega*Real.log (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hw).mp hE'
  exact hRate B hB N cap hN2 hEven omega v tau hw hv hv1 ht h3 hwlog tags

end
end ImbalancedChen.P4AOriginalFiniteFallbackActualTaggedRate
