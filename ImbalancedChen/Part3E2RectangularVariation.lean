import ImbalancedChen.Part3SmoothRectangularAbel
import ImbalancedChen.Part3E2SlowPhase

/-!
# Removal of the exact five-coordinate E2 weight

Each logarithmic positive coordinate and the signed fifth coordinate is
sampled on one monotone grid. The coefficient array retains every
arithmetic gate. The estimate uses common endpoints fixed for each
rectangular prefix.
-/

namespace ImbalancedChen.Part3

open Classical Finset
open scoped BigOperators ContDiff SchwartzMap

noncomputable section

abbrev E2GridIndex := Fin 4 ⊕ Unit
abbrev E2LogSpace := (Fin 4 → ℝ) × ℝ

private def e2Direction : E2GridIndex → E2LogSpace
  | .inl i => (Pi.single i 1, 0)
  | .inr _ => (0, 1)

private theorem norm_e2Direction_le (i : E2GridIndex) : ‖e2Direction i‖ ≤ 1 := by
  cases i with
  | inl j =>
    rw [e2Direction, Prod.norm_def, max_le_iff]
    refine ⟨(pi_norm_le_iff_of_nonneg zero_le_one).mpr ?_, by simp⟩
    intro k
    by_cases hk : k = j <;> simp [hk]
  | inr j => simp [e2Direction, Prod.norm_def]

private theorem sum_e2Direction (p : E2GridIndex → ℝ) :
    (∑ i, p i • e2Direction i) = ((fun i => p (.inl i)), p (.inr ())) := by
  rw [Fintype.sum_sum_type]
  apply Prod.ext
  · ext i
    simp [e2Direction, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [e2Direction, Prod.snd_sum]

private def e2LogGridBox : Set E2LogSpace :=
  (Set.pi Set.univ (fun _ : Fin 4 => Set.Icc 0 (Real.log 2))) ×ˢ Set.Icc (-1) 1

private theorem convex_e2LogGridBox : Convex ℝ e2LogGridBox :=
  (convex_pi (fun _ _ => convex_Icc _ _)).prod (convex_Icc _ _)

/-- The literal normalized weight in the fixed d E2 sum. -/
def e2NormalizedWeight (ψ ψhat : ℝ → ℂ) (b L A : ℝ) (v : Fin 4 → ℝ) (t : ℝ) : ℂ :=
  ψ (b * v 0) * ψhat (L * t / (v 0 * v 1 * v 2)) *
    fourier (1 : ℤ) ((A * t / (v 0 * v 1 * v 2 * v 3) : ℝ) : UnitAddCircle)

private def logGridScalars (g : E2GridIndex → ℕ → ℝ) : E2GridIndex → ℕ → ℝ
  | .inl i => fun n => Real.log (g (.inl i) n)
  | .inr j => g (.inr j)

/-- Repeated partial summation removes the original smooth E2 weight
with one fifth-degree cost. The rectangle array may include all the
arithmetic cutoffs, including a zero coefficient at signed frequency zero. -/
theorem exists_e2NormalizedWeight_rectangular_norm_le (ψ ψhat : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b L A : ℝ), |b| ≤ 2 →
      ∀ (lo hi : E2GridIndex → ℕ), lo ≤ hi →
      ∀ (g : E2GridIndex → ℕ → ℝ),
      (∀ i, MonotoneOn (g i) (Set.Icc (lo i) (hi i))) →
      (∀ (i : Fin 4) (n : ℕ), n ∈ Set.Icc (lo (.inl i)) (hi (.inl i)) →
        g (.inl i) n ∈ Set.Icc (1 : ℝ) 2) →
      (∀ n : ℕ, n ∈ Set.Icc (lo (.inr ())) (hi (.inr ())) →
        g (.inr ()) n ∈ Set.Icc (-1 : ℝ) 1) →
      ∀ (coeff : (E2GridIndex → ℕ) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ y ∈ RectangularAbel.rectangle lo hi, ‖∑ x ∈ RectangularAbel.rectangle lo y, coeff x‖ ≤ B) →
      ‖∑ x ∈ RectangularAbel.rectangle lo hi, coeff x *
        e2NormalizedWeight ψ ψhat b L A (fun i => g (.inl i) (x (.inl i))) (g (.inr ()) (x (.inr ())))‖ ≤
        C * (1 + |L| + |A|)^5 * B := by
  obtain ⟨C, hC, hD⟩ := e2LogWeight_iteratedFDeriv_le ψ ψhat
  refine ⟨C * 3^5, by positivity, ?_⟩
  intro b L A hb lo hi hlo g hmono hpos hsigned coeff B hB0 hB
  let f := e2LogWeight ψ ψhat b L A
  let p := logGridScalars g
  have hsmooth : ContDiff ℝ ∞ f := e2LogWeight_contDiff ψ ψhat b L A (ψ.smooth _) (ψhat.smooth _)
  have hpMon (i : E2GridIndex) : MonotoneOn (p i) (Set.Icc (lo i) (hi i)) := by
    cases i with
    | inr j => exact hmono _
    | inl j =>
      intro n hn m hm hnm
      have hnpos := zero_lt_one.trans_le (hpos j n hn).1
      exact Real.log_le_log hnpos (hmono _ hn hm hnm)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (2 : ℝ) by norm_num)
    linarith
  have hpLength (i : E2GridIndex) : p i (hi i) - p i (lo i) ≤ 2 := by
    have hlow : lo i ∈ Set.Icc (lo i) (hi i) := ⟨le_rfl, hlo i⟩
    have hup : hi i ∈ Set.Icc (lo i) (hi i) := ⟨hlo i, le_rfl⟩
    cases i with
    | inl j =>
      have h1 := Real.log_nonneg (hpos j _ hlow).1
      have h2 := Real.log_le_log (zero_lt_one.trans_le (hpos j _ hup).1) (hpos j _ hup).2
      change Real.log (g (.inl j) (hi (.inl j))) - Real.log (g (.inl j) (lo (.inl j))) ≤ _
      linarith
    | inr j =>
      cases j
      have h1 := (hsigned _ hlow).1
      have h2 := (hsigned _ hup).2
      change g (.inr ()) (hi (.inr ())) - g (.inr ()) (lo (.inr ())) ≤ _
      linarith
  have hP (z : E2GridIndex → ℕ) (hz : z ∈ RectangularAbel.rectangle lo hi) :
      (∑ i, p i (z i) • e2Direction i) ∈ e2LogGridBox := by
    rw [sum_e2Direction]
    obtain ⟨hloz, hzhi⟩ := RectangularAbel.mem_rectangle.mp hz
    refine ⟨?_, hsigned _ ⟨hloz _, hzhi _⟩⟩
    intro i _
    obtain ⟨hp₁, hp₂⟩ := hpos i _ ⟨hloz _, hzhi _⟩
    exact ⟨Real.log_nonneg hp₁, Real.log_le_log (zero_lt_one.trans_le hp₁) hp₂⟩
  have hcard : Fintype.card E2GridIndex = 5 := by
    simp [E2GridIndex, Fintype.card_sum]
  have hD' (j : ℕ) (hj : j ≤ Fintype.card E2GridIndex) (z : E2LogSpace) (hz : z ∈ e2LogGridBox) :
      ‖iteratedFDeriv ℝ j f z‖ ≤ C * (1 + |L| + |A|)^5 := by
    have he : j ≤ 5 := hcard ▸ hj
    have hlog (i : Fin 4) : z.1 i ∈ Set.Icc (0 : ℝ) (Real.log 2) := hz.1 i (Set.mem_univ _)
    exact (hD b L A z j hb (fun i => (hlog i).1) (hlog 0).2 (abs_le.mpr hz.2) he).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [abs_nonneg L, abs_nonneg A]) he) hC.le)
  have hbound := RectangularAbel.norm_sum_scalarGrid_le lo hi hlo p e2Direction norm_e2Direction_le
    hpMon f hsmooth e2LogGridBox convex_e2LogGridBox coeff hB0
    (show 0 ≤ C * (1 + |L| + |A|)^5 by positivity) hpLength hP hD' hB
  have heq (z : E2GridIndex → ℕ) (hz : z ∈ RectangularAbel.rectangle lo hi) :
      f (∑ i, p i (z i) • e2Direction i) =
        e2NormalizedWeight ψ ψhat b L A (fun i => g (.inl i) (z (.inl i))) (g (.inr ()) (z (.inr ()))) := by
    rw [sum_e2Direction]
    obtain ⟨hloz, hzhi⟩ := RectangularAbel.mem_rectangle.mp hz
    exact e2LogWeight_at_normalized ψ ψhat b L A _ _
      (fun i => zero_lt_one.trans_le (hpos i _ ⟨hloz _, hzhi _⟩).1)
  have hsum :
      (∑ x ∈ RectangularAbel.rectangle lo hi, coeff x * f (∑ i, p i (x i) • e2Direction i)) =
      ∑ x ∈ RectangularAbel.rectangle lo hi, coeff x *
        e2NormalizedWeight ψ ψhat b L A (fun i => g (.inl i) (x (.inl i))) (g (.inr ()) (x (.inr ()))) :=
    sum_congr rfl (fun z hz => congrArg (coeff z * ·) (heq z hz))
  rw [hsum, hcard] at hbound
  exact hbound.trans_eq (by ring)

def e2PositiveScales (q₀ R N : ℝ) : Fin 4 → ℝ := ![q₀, R, R, N]

private def e2GridSamples (q₀ R N H : ℝ) (h₀ : ℤ) : E2GridIndex → ℕ → ℝ
  | .inl i => fun n => (n : ℝ) / e2PositiveScales q₀ R N i
  | .inr _ => fun n => ((h₀ : ℝ) + (n : ℝ)) / H

/-- The physical weight left after (21). The signed frequency is indexed
by an integer starting point and a natural offset. -/
def e2PhysicalGridWeight (ψ ψhat : ℝ → ℂ) (Q M d a : ℝ) (h₀ : ℤ)
    (x : E2GridIndex → ℕ) : ℂ :=
  let q : ℝ := x (.inl 0)
  let w₁ : ℝ := x (.inl 1)
  let w₂ : ℝ := x (.inl 2)
  let n₁ : ℝ := x (.inl 3)
  let h : ℝ := (h₀ : ℝ) + (x (.inr ()) : ℝ)
  ψ (q / Q) * ψhat (h * M / (q * d * w₁ * w₂)) *
    fourier (1 : ℤ) ((a * h / (q * d * w₁ * w₂ * n₁) : ℝ) : UnitAddCircle)

/-- Equation (22) on the physical rectangle. Both smooth cutoffs and
the retained slow phase are removed together. The bound for bare
rectangles is one common bound before any rectangular endpoint is chosen. -/
theorem exists_e2PhysicalWeight_rectangular_rpow {κ ε Cq Cd : ℝ}
    (hκ : 0 ≤ κ) (hε : 0 < ε) (hCq : 0 ≤ Cq) (hCd : 0 ≤ Cd)
    (ψ ψhat : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X M N Q D R q₀ d H a : ℝ),
      1 ≤ X → X = N * M → 0 < M → 0 < N → 0 < Q → 0 ≤ D → 0 < R →
      0 < q₀ → 0 < d → 0 < H → q₀ ≤ 2 * Q → Q / q₀ ≤ Cq → D / d ≤ Cd →
      H ≤ Q * D * R^2 * (Real.log X)^5 / M → |a| ≤ X ^ (1 + κ) →
      ∀ (lo hi : E2GridIndex → ℕ), lo ≤ hi → ∀ (h₀ : ℤ),
      (∀ (i : Fin 4) (n : ℕ), n ∈ Set.Icc (lo (.inl i)) (hi (.inl i)) →
        e2PositiveScales q₀ R N i ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * e2PositiveScales q₀ R N i) →
      (∀ n : ℕ, n ∈ Set.Icc (lo (.inr ())) (hi (.inr ())) →
        |(h₀ : ℝ) + (n : ℝ)| ≤ H) →
      ∀ (coeff : (E2GridIndex → ℕ) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ y ∈ RectangularAbel.rectangle lo hi, ‖∑ x ∈ RectangularAbel.rectangle lo y, coeff x‖ ≤ B) →
      ‖∑ x ∈ RectangularAbel.rectangle lo hi, coeff x * e2PhysicalGridWeight ψ ψhat Q M d a h₀ x‖ ≤
        C * X ^ (5 * κ + ε) * B := by
  obtain ⟨K, hK, hbound⟩ := exists_e2NormalizedWeight_rectangular_norm_le ψ ψhat
  let Klog := (1 + 2 * (Cq * Cd) * (25 / ε)^5)^5
  refine ⟨K * Klog, by dsimp only [Klog]; positivity, ?_⟩
  intro X M N Q D R q₀ d H a hX hscale hM hN hQ hD hR hq₀ hd hH hb hqRatio hdRatio
    hHcut ha lo hi hlo h₀ hboxPos hboxH coeff B hB0 hB
  let L := H * M / (q₀ * d * R^2)
  let A := a * H / (q₀ * d * R^2 * N)
  let g := e2GridSamples q₀ R N H h₀
  have hscalePos (i : Fin 4) : 0 < e2PositiveScales q₀ R N i := by
    fin_cases i
    · exact hq₀
    · exact hR
    · exact hR
    · exact hN
  have hmono (i : E2GridIndex) : MonotoneOn (g i) (Set.Icc (lo i) (hi i)) := by
    intro n _ m _ hnm
    cases i with
    | inl j => exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hnm) (hscalePos j).le
    | inr j => exact div_le_div_of_nonneg_right (add_le_add le_rfl (Nat.cast_le.mpr hnm)) hH.le
  have hpos (i : Fin 4) (n : ℕ) (hn : n ∈ Set.Icc (lo (.inl i)) (hi (.inl i))) :
      g (.inl i) n ∈ Set.Icc (1 : ℝ) 2 := by
    obtain ⟨hlo', hhi'⟩ := hboxPos i n hn
    exact ⟨(le_div_iff₀ (hscalePos i)).mpr (by simpa using hlo'),
      (div_le_iff₀ (hscalePos i)).mpr hhi'⟩
  have hsigned (n : ℕ) (hn : n ∈ Set.Icc (lo (.inr ())) (hi (.inr ()))) :
      g (.inr ()) n ∈ Set.Icc (-1 : ℝ) 1 := by
    obtain ⟨hl, hr⟩ := abs_le.mp (hboxH n hn)
    exact ⟨(le_div_iff₀ hH).mpr (by simpa using hl),
      (div_le_iff₀ hH).mpr (by simpa using hr)⟩
  have hb' : |q₀ / Q| ≤ 2 := by
    rw [abs_of_pos (div_pos hq₀ hQ)]
    exact (div_le_iff₀ hQ).mpr hb
  have hW := hbound (q₀ / Q) L A hb' lo hi hlo g hmono hpos hsigned coeff B hB0 hB
  have hweight (x : E2GridIndex → ℕ) (hx : x ∈ RectangularAbel.rectangle lo hi) :
      e2NormalizedWeight ψ ψhat (q₀ / Q) L A (fun i => g (.inl i) (x (.inl i)))
        (g (.inr ()) (x (.inr ()))) = e2PhysicalGridWeight ψ ψhat Q M d a h₀ x := by
    obtain ⟨hxlo, hxhi⟩ := RectangularAbel.mem_rectangle.mp hx
    have hxPos (i : Fin 4) : 0 < (x (.inl i) : ℝ) :=
      (hscalePos i).trans_le (hboxPos i _ ⟨hxlo _, hxhi _⟩).1
    unfold e2NormalizedWeight
    rw [← e2LogWeight_at_normalized ψ ψhat _ _ _ _ _
      (fun i => zero_lt_one.trans_le (hpos i _ ⟨hxlo _, hxhi _⟩).1)]
    have hv : (fun i : Fin 4 => g (.inl i) (x (.inl i))) =
        ![(x (.inl 0) : ℝ) / q₀, (x (.inl 1) : ℝ) / R,
          (x (.inl 2) : ℝ) / R, (x (.inl 3) : ℝ) / N] := by
      funext i
      fin_cases i <;> rfl
    rw [congrArg (fun v : Fin 4 → ℝ => fun i => Real.log (v i)) hv]
    exact e2LogWeight_at_physical ψ ψhat q₀ Q R N H M a d _ _ _ _ _
      hq₀ hQ hR hN hH hd (hxPos 0) (hxPos 1) (hxPos 2) (hxPos 3)
  have hsum :
      (∑ x ∈ RectangularAbel.rectangle lo hi, coeff x *
        e2NormalizedWeight ψ ψhat (q₀ / Q) L A (fun i => g (.inl i) (x (.inl i)))
          (g (.inr ()) (x (.inr ()))) ) =
      ∑ x ∈ RectangularAbel.rectangle lo hi, coeff x * e2PhysicalGridWeight ψ ψhat Q M d a h₀ x :=
    sum_congr rfl (fun x hx => congrArg (coeff x * ·) (hweight x hx))
  rw [hsum] at hW
  obtain ⟨hL, hA⟩ := e2LogWeight_physicalParameters_le hX hscale hM hN hq₀ hd hR
    hH.le hD hCq hqRatio hdRatio hHcut ha
  have hcost := e2LogWeight_amplitude_budget hX hκ hε (mul_nonneg hCq hCd) hL hA
  exact hW.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost hK.le) hB0).trans_eq
    (mul_assoc K Klog (X ^ (5 * κ + ε)) ▸ rfl))

end

end ImbalancedChen.Part3
