import ImbalancedChen.OriginalFourthIntegerMeshEndpoints

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

The natural upper endpoint is now a canonical function of the ORIGINAL
target, fixed mesh and actual prime label. It is constructed from genuine
half-open interval ownership, not selected after an endpoint inequality.
Its upper bound is uniform over every source label below N^(19/96).
The target-deletion condition can therefore stay in the actual carrier.
-/

namespace ImbalancedChen.OriginalFourthCanonicalIntegerEndpoints20261026b

noncomputable section
open Filter Topology Set
open scoped Classical
open OriginalFourthIntegerMeshEndpoints20261026b

def primeCoordinate (N p : ℕ) : ℝ := Real.log (p : ℝ) / Real.log (N : ℝ)

def cellIndex (n N p : ℕ) : Fin (n + 1) :=
  if h : primeCoordinate N p ∈ Ico 0 (19 / 96 : ℝ) then
    Classical.choose (exists_logPrimeMeshInterval 0 (19 / 96 : ℝ) n h)
  else 0

def integerUpper (n N p : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ logPrimeMeshPoint 0 (19 / 96 : ℝ) n
    ((cellIndex n N p).val + 1))

theorem cellIndex_spec (n N p : ℕ)
    (hp : primeCoordinate N p ∈ Ico 0 (19 / 96 : ℝ)) :
    primeCoordinate N p ∈ Ico
      (logPrimeMeshPoint 0 (19 / 96 : ℝ) n (cellIndex n N p).val)
      (logPrimeMeshPoint 0 (19 / 96 : ℝ) n ((cellIndex n N p).val + 1)) := by
  simpa only [cellIndex, dif_pos hp] using
    Classical.choose_spec (exists_logPrimeMeshInterval 0 (19 / 96 : ℝ) n hp)

theorem primeCoordinate_rpow {N p : ℕ} (hN : 1 < N) (hp : 0 < p) :
    (N : ℝ) ^ primeCoordinate N p = (p : ℝ) := by
  simpa only [primeCoordinate, actualPrimeTupleLog] using
    actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hp) (0 : Fin 1)

theorem primeCoordinate_mem {N p : ℕ} (hN : 1 < N) (hp : 0 < p)
    (hcut : (p : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ)) :
    primeCoordinate N p ∈ Ico 0 (19 / 96 : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpower := primeCoordinate_rpow hN hp
  constructor
  · apply (Real.rpow_le_rpow_left_iff hNr).mp
    rw [Real.rpow_zero, hpower]
    exact_mod_cast (Nat.succ_le_of_lt hp)
  · apply (Real.rpow_lt_rpow_left_iff hNr).mp
    rw [hpower]
    exact hcut

/-- The same natural endpoint function works for every original prime
label, uniformly after one threshold fixed solely by tau and the mesh. -/
theorem eventually_all_canonical_endpoints (tau : ℝ) (htau : 0 < tau)
    (n : ℕ) (hstep : logPrimeMeshStep 0 (19 / 96 : ℝ) n ≤ tau / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 0 < p →
      (p : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ) →
      p ≤ integerUpper n N p ∧ (integerUpper n N p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ) := by
  filter_upwards [eventually_all_mesh_integer_endpoints tau htau n hstep,
    eventually_ge_atTop (2 : ℕ)] with N hbudget hN
  intro p hp hcut
  have hN' : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN'
  have hcell := cellIndex_spec n N p (primeCoordinate_mem hN' hp hcut)
  have hpower := primeCoordinate_rpow hN' hp
  have hbox : ∀ i : Fin 1,
      (N : ℝ) ^ logPrimeMeshLo 0 (19 / 96 : ℝ) n
          (fun _ : Fin 1 => cellIndex n N p) i ≤ (p : ℝ) ∧
      (p : ℝ) < (N : ℝ) ^ logPrimeMeshHi 0 (19 / 96 : ℝ) n
          (fun _ : Fin 1 => cellIndex n N p) i := by
    intro i
    change (N : ℝ) ^ logPrimeMeshPoint 0 (19 / 96 : ℝ) n
        (cellIndex n N p).val ≤ (p : ℝ) ∧
      (p : ℝ) < (N : ℝ) ^ logPrimeMeshPoint 0 (19 / 96 : ℝ) n
        ((cellIndex n N p).val + 1)
    rw [← hpower]
    exact ⟨Real.rpow_le_rpow_of_exponent_le hNr.le hcell.1,
      Real.rpow_lt_rpow_of_exponent_lt hNr hcell.2⟩
  have hb := hbudget 1 (fun _ : Fin 1 => cellIndex n N p)
    (fun _ : Fin 1 => p) hbox (0 : Fin 1)
  simpa only [integerUpper, logPrimeMeshHi] using hb

/-- A fixed finite grid and its canonical integer upper endpoint function
are chosen before the arithmetic target, label or retained history. -/
theorem exists_uniform_canonical_endpoints (tau : ℝ) (htau : 0 < tau) :
    ∃ n : ℕ, logPrimeMeshStep 0 (19 / 96 : ℝ) n ≤ tau / 2 ∧
      ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, 0 < p →
        (p : ℝ) < (N : ℝ) ^ (19 / 96 : ℝ) →
        p ≤ integerUpper n N p ∧
          (integerUpper n N p : ℝ) ≤ (N : ℝ) ^ tau * (p : ℝ) := by
  obtain ⟨n, hn, _hmesh⟩ := exists_uniform_integer_mesh tau htau
  exact ⟨n, hn, eventually_all_canonical_endpoints tau htau n hn⟩

end
end ImbalancedChen.OriginalFourthCanonicalIntegerEndpoints20261026b
