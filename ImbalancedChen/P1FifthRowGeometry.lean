import ImbalancedChen.VariableEnvelope
import ImbalancedChen.SelectedPrefixRationalMesh

/-! Shared exact geometric declarations; selected verification is recorded separately. -/
namespace ImbalancedChen.P1OriginalVariableFifthContinuation
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point5 := Fin 5 → ℝ
abbrev Label5 (m : ℕ) := Fin 5 → Fin (m + 1)

structure FifthRow (m : ℕ) where
  cell : Label5 m
  selected : Finset (Fin 5)

def envelope (I : Finset (Fin 5)) (t : Point5) : ℝ :=
  let s := ∑ i ∈ I, t i
  min ((1 + s) / 2) (57 / 64 - (3 / 2) * s)

def candidate (e : ℝ) (I : Finset (Fin 5)) (t : Point5) : ℝ :=
  envelope I t - 2 * e

theorem envelope_eq_v (I : Finset (Fin 5)) (t : Point5) :
    envelope I t = v (∑ i ∈ I, t i) := by
  rw [envelope, v_eq_min]
  rfl

theorem candidate_eq_original_cap (e : ℝ) (I : Finset (Fin 5)) (t : Point5) :
    candidate e I t =
      min ((1 + ∑ i ∈ I, t i) / 2)
        (57 / 64 - (3 / 2 : ℝ) * ∑ i ∈ I, t i) - 2 * e := rfl

theorem candidate_le_original_cap (e : ℝ) (he : 0 ≤ e)
    (I : Finset (Fin 5)) (t : Point5) : candidate e I t ≤ envelope I t := by
  dsimp [candidate]
  linarith

theorem candidate_le_global_cap (e : ℝ) (he : 0 ≤ e)
    (I : Finset (Fin 5)) (t : Point5) :
    candidate e I t ≤ VariableEnvelope.cap := by
  calc
    candidate e I t ≤ envelope I t := candidate_le_original_cap e he I t
    _ = v (∑ i ∈ I, t i) := envelope_eq_v I t
    _ ≤ VariableEnvelope.cap := v_le_cap _

end
end ImbalancedChen.P1OriginalVariableFifthContinuation
