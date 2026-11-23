import ImbalancedChen.P2LowerCapPlanIntegerRetention

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- A whole closed-box upper corner supplies strict original incoming gates.
-- The selected third/fourth/fifth CapPlan rows are not supplied here.
-- In particular this is a local implication for a future concrete table,
-- not a certificate that the actual selected table passes these checks.

namespace ImbalancedChen.P2OriginalSelectedBoxGateMargin

noncomputable section
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention

-- These are the exact three active lower-tree history checks on a five-rank
-- physical box. The third and fifth full ranks are odd and have no own cube.
structure StrictUpperCorner (upper : Fin 5 → ℝ)
    (seedCap cap3 delta : ℝ) : Prop where
  positive : 0 < delta
  first : 2 * upper 0 + delta ≤ seedCap
  second : upper 0 + 3 * upper 1 + delta ≤ seedCap
  fourth : upper 0 + upper 1 + upper 2 + 3 * upper 3 + delta ≤ cap3

theorem point_gates_of_strict_upper_corner
    {upper x : Fin 5 → ℝ} {seedCap cap3 delta : ℝ}
    (hbox : StrictUpperCorner upper seedCap cap3 delta)
    (hx : ∀ i, x i ≤ upper i) :
    2 * x 0 < seedCap ∧
      x 0 + 3 * x 1 < seedCap ∧
      x 0 + x 1 + x 2 + 3 * x 3 < cap3 := by
  rcases hbox with ⟨hdelta, hfirst, hsecond, hfourth⟩
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  constructor
  · linarith
  constructor
  · linarith
  · linarith

-- The fifth square uses the fourth INCOMING cap, not the just-selected
-- fourth outgoing cap. The latter enters only through cap monotonicity.
theorem fifth_square_of_strict_upper_corner
    {upper x : Fin 5 → ℝ} {seedCap cap3 cap4 delta : ℝ}
    (hbox : StrictUpperCorner upper seedCap cap3 delta)
    (hx : ∀ i, x i ≤ upper i)
    (horder : x 4 < x 3) (hcap : cap3 ≤ cap4) :
    (x 0 + x 1 + x 2 + x 3) + 2 * x 4 < cap4 := by
  have hfourth := (point_gates_of_strict_upper_corner hbox hx).2.2
  linarith

-- An actual selected fourth choice is read only AFTER admission at the
-- frozen third cap. This binds the corner check to the real Trace.step
-- rather than silently substituting the new fourth cap into its cube.
theorem selected_fourth_step_of_strict_upper_corner
    {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    {upper x : Fin 5 → ℝ} {seedCap cap3 cap4 delta argument : ℝ}
    (hbox : StrictUpperCorner upper seedCap cap3 delta)
    (hx : ∀ i, x i ≤ upper i)
    (horder : x 4 < x 3) (hcap : cap3 ≤ cap4)
    (H : Trace) (hword : H.word = [x 0, x 1, x 2])
    (hincoming : H.cap = cap3) (haccepted : H.accepted = true)
    (hchoice : planChoice P a b (H.word ++ [x 3]) =
      .fresh cap4 argument) :
    (step P a b H (x 3)).accepted = true ∧
      (step P a b H (x 3)).cap = cap4 ∧
      (x 0 + x 1 + x 2 + x 3) + 2 * x 4 < cap4 := by
  have hcube := (point_gates_of_strict_upper_corner hbox hx).2.2
  have hadmission : admission H (x 3) := by
    simpa [admission, hword, hincoming] using hcube
  have hpass := (step_accepted_iff P a b H (x 3)).mpr ⟨haccepted, hadmission⟩
  have hfreeze : (step P a b H (x 3)).cap = cap4 := by
    simp [step, hchoice, CapChoice.freeze]
  exact ⟨hpass, hfreeze,
    fifth_square_of_strict_upper_corner hbox hx horder hcap⟩

end
end ImbalancedChen.P2OriginalSelectedBoxGateMargin
