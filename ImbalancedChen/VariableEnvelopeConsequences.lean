import ImbalancedChen.VariableEnvelope

/-!
# Continuity and quantitative bounds for the variable envelope

The six-branch expression is continuous on all of `ℝ³`. The equality with
the literal gated expression therefore supplies continuity on the closed
ordered domain. The bounds below use the actual branches proved in
`VariableEnvelope`, without assuming any analytic or sieve estimate.
-/

namespace ImbalancedChen.VariableEnvelope

noncomputable section

theorem continuous_A : Continuous A := by
  exact (continuous_const.add continuous_id).div_const 2

theorem continuous_C : Continuous C := by
  exact continuous_const.sub (continuous_const.mul continuous_id)

theorem continuous_B : Continuous B := by
  exact continuous_const.sub (continuous_const.mul continuous_id)

theorem continuous_v : Continuous v := by
  change Continuous (fun t : ℝ => v t)
  simp only [v_eq_min]
  exact continuous_A.min continuous_C

/-- The six-branch formula itself is continuous without domain restrictions. -/
theorem continuous_six : Continuous (fun p : ℝ × ℝ × ℝ => six p.1 p.2.1 p.2.2) := by
  have hx : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) :=
    continuous_snd.comp continuous_snd
  unfold six
  exact (continuous_v.comp hx).max
    ((continuous_v.comp (hx.add hy)).max
      ((continuous_v.comp ((hx.add hy).add hz)).max
        ((continuous_B.comp hz).max
          ((continuous_v.comp (hx.add hz)).max (continuous_v.comp (hy.add hz))))))

/-- The domain includes all its boundary faces, including `z = 0`. -/
def orderedSet : Set (ℝ × ℝ × ℝ) := {p | Ordered p.1 p.2.1 p.2.2}

theorem isClosed_orderedSet : IsClosed orderedSet := by
  have hx : Continuous (fun p : ℝ × ℝ × ℝ => p.1) := continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hz : Continuous (fun p : ℝ × ℝ × ℝ => p.2.2) :=
    continuous_snd.comp continuous_snd
  exact (isClosed_le continuous_const hz).inter
    ((isClosed_le hz hy).inter ((isClosed_le hy hx).inter (isClosed_le hx continuous_const)))

/-- The gated formula is continuous relative to the closed ordered domain. -/
theorem continuousOn_original :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => original p.1 p.2.1 p.2.2) orderedSet := by
  apply continuous_six.continuousOn.congr
  intro p hp
  exact original_eq_six hp

theorem v_le_six (x y z : ℝ) : v x ≤ six x y z := by
  exact le_max_left _ _

theorem B_le_six (x y z : ℝ) : B z ≤ six x y z := by
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

theorem six_le_cap (x y : ℝ) {z : ℝ} (hz : 0 ≤ z) : six x y z ≤ cap := by
  have hB : B z ≤ cap := by dsimp [B]; linarith
  exact max_le (v_le_cap _) (max_le (v_le_cap _) (max_le (v_le_cap _)
    (max_le hB (max_le (v_le_cap _) (v_le_cap _)))))

theorem v_le_original {x y z : ℝ} (h : Ordered x y z) : v x ≤ original x y z := by
  rw [original_eq_six h]
  exact v_le_six x y z

theorem B_le_original {x y z : ℝ} (h : Ordered x y z) : B z ≤ original x y z := by
  rw [original_eq_six h]
  exact B_le_six x y z

theorem original_le_cap {x y z : ℝ} (h : Ordered x y z) : original x y z ≤ cap := by
  rw [original_eq_six h]
  exact six_le_cap x y h.1

/-- The strict surplus has the uniform, sharp lower bound `3/256`. -/
theorem original_margin {x y z : ℝ} (h : Ordered x y z) :
    3 / 256 ≤ original x y z - 3 * x := by
  have hv := v_le_original h
  rw [v_eq_A h.2.2.2] at hv
  have hx := h.2.2.2
  dsimp [A, mu] at *
  linarith

theorem three_mul_lt_original {x y z : ℝ} (h : Ordered x y z) :
    3 * x < original x y z := by
  have hm := original_margin h
  linarith

theorem original_margin_pos {x y z : ℝ} (h : Ordered x y z) :
    0 < original x y z - 3 * x := by
  have hm := original_margin h
  linarith

/-- The affine branch gives the manuscript's threshold criterion. -/
theorem threshold_le_original {x y z Theta : ℝ} (h : Ordered x y z)
    (hz : z ≤ (8 / 3) * (cap - Theta)) : Theta ≤ original x y z := by
  have hb := B_le_original h
  dsimp [B] at hb
  linarith

theorem cutoff_597 : (8 / 3 : ℝ) * (cap - 597 / 1000) = 7 / 4000 := by
  norm_num [cap]

theorem threshold_597_le_original {x y z : ℝ} (h : Ordered x y z)
    (hz : z ≤ 7 / 4000) : (597 / 1000 : ℝ) ≤ original x y z := by
  apply threshold_le_original h
  simpa only [cutoff_597] using hz

theorem ordered_mu : Ordered mu mu mu := by
  norm_num [Ordered, mu]

/-- The envelope reaches its cap on the whole face `x = mu`. -/
theorem original_mu_left {y z : ℝ} (h : Ordered mu y z) : original mu y z = cap := by
  apply le_antisymm (original_le_cap h)
  calc
    cap = A mu := by norm_num [cap, A, mu]
    _ = v mu := (v_eq_A (le_refl mu)).symm
    _ ≤ original mu y z := v_le_original h

theorem original_mu : original mu mu mu = cap := original_mu_left ordered_mu

theorem original_margin_eq_on_mu {y z : ℝ} (h : Ordered mu y z) :
    original mu y z - 3 * mu = 3 / 256 := by
  rw [original_mu_left h]
  norm_num [cap, mu]

/-- Equality at the positive diagonal point shows that the margin cannot be improved. -/
theorem original_margin_sharp : original mu mu mu - 3 * mu = 3 / 256 := by
  rw [original_mu]
  norm_num [cap, mu]

/-- The second pair gate also attains the uniform margin at a point with positive `z`. -/
theorem yz_gate_margin_sharp :
    v (mu / 2 + mu / 2) - (2 * mu + mu / 2 + mu / 2) = 3 / 256 := by
  have hs : mu / 2 + mu / 2 = mu := by linarith
  rw [hs, v_eq_A (le_refl mu)]
  norm_num [A, mu]

end

end ImbalancedChen.VariableEnvelope
