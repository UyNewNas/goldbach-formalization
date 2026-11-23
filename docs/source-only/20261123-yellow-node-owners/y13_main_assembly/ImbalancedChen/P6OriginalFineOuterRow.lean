import ImbalancedChen.P4BOriginalFineAttachedUpper

/-! A fixed-width signed count on the original attached coefficient. The width is
chosen from four physical wall estimates before the target N. -/
namespace ImbalancedChen.P6OriginalFineOuterRow

noncomputable section
open Filter Topology
open scoped BigOperators
open P4BOriginalFineAttachedUpper (Selection retention)
open P4BLabelledOuterPushforward
open P4BOuterRampRoughness (baseline)

variable {m r n q : ℕ} {e : ℚ} {a η B z : ℝ} {ft : ℝ → ℝ}

abbrev outerRow (s : Selection m r n e q a 1 (19/96) η B z ft) (b w : ℝ) (N : ℕ) :=
  let f := retention m r n e q a (1 * s.beta ^ 2)
  Part3.primeProductSignedError 2 N N (attachedUpperModuli 1 (19/96) s.beta f id N)
    (attachedUpperCoefficient 1 (19/96) s.beta f id N)
    (P4B.smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff (1/4) N) w)

/-- The outer main term, both localization losses and the coprime correction
are paid. The signed rank-two error has coefficient one on the count scale. -/
theorem exists_width_signed_upper (s : Selection m r n e q a 1 (19/96) η B z ft)
    {b t : ℝ} (hb : (1/2 : ℝ) < b) (hb1 : b < 1) (ht : 0 < t) :
    ∃ w : ℝ, 0 < w ∧ 2*w ≤ baseline b (1/4) - 1*(19/96) ∧
      ∀ᶠ N : ℕ in atTop, Even N → (RealB b N : ℝ) ≤
        (currentK * Real.log (1/b) + t) * singularNormalization N + outerRow s b w N := by
  let k : ℝ := 1/4
  let θ : ℝ := 1*(19/96)
  have hk : 0 < k := by norm_num [k]
  have hk1 : k < 1 := by norm_num [k]
  have hθ : θ < 1 := by norm_num [θ]
  have hb0 : 0 < b := by linarith only [hb]
  have hg : θ < baseline b k := by
    unfold baseline
    apply (lt_div_iff₀ (by linarith : 0 < 1+b)).mpr
    dsimp only [θ, k]
    linarith only [hb]
  let d := t / (2*currentK + 2)
  have hden : 0 < 2*currentK + 2 := by norm_num [currentK]
  have hd : 0 < d := div_pos ht hden
  have hspend : (2*currentK + 2)*d = t := by dsimp [d]; field_simp [hden.ne'] <;> ring
  obtain ⟨w, hw, hwMax, Nw, hNw, hmass⟩ := P4B.exists_smooth_physical_ramp_mass_reserve
    hb hb1 hk hk1 d ((baseline b k - θ)/2) hd (by linarith only [hg])
  have hwg : 2*w ≤ baseline b k - θ := by linarith only [hwMax]
  refine ⟨w, hw, hwg, ?_⟩
  let J := Real.log (1/b)
  have hsource : ∀ᶠ N : ℕ in atTop,
      ((realHalfProductSource b N (manuscriptHalfProductCutoff k N)).card : ℝ) /
        ((N : ℝ)/Real.log (N : ℝ)) < J+d :=
    (tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb0 hb1 hk).eventually
      (gt_mem_nhds (lt_add_of_pos_right J hd))
  have hceil : ∀ᶠ N : ℕ in atTop, (Nat.ceil ((N : ℝ)^θ) : ℝ) ≤ d*singularNormalization N := by
    simpa only [one_mul, pow_zero, mul_one] using
      eventually_ceil_powerLog_le_singularNormalization 1 θ 0 (by norm_num) hθ d hd
  have hcut : ∀ᶠ N : ℕ in atTop, manuscriptHalfProductCutoff k N+1 ≤ d*singularNormalization N := by
    simpa only [manuscriptHalfProductCutoff, pow_zero, mul_one] using
      eventually_powerLog_add_one_le_singularNormalization 2 (1-k) 0 (by linarith) d hd
  filter_upwards [hsource, hceil, hcut, s.attached_K, eventually_ge_atTop Nw] with N hs hc hTcost hD hN
  intro hev
  have h2 : 2 ≤ N := hNw.trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let T := manuscriptHalfProductCutoff k N
  let V := P4B.smoothPhysicalPairOuterRamp b N T w
  let f := retention m r n e q a (1*s.beta^2)
  let M := finiteSourceMass (productCarrier N) (productWeight N V)
  let X := (N : ℝ)/Real.log (N : ℝ)
  have hX : 0 < X := div_pos (zero_lt_one.trans hNr) (Real.log_pos hNr)
  have hT : 0 < T := mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _)
  have hV : ∀ u ∈ Part3.labelledPrimeTuples 2 N, 0 ≤ V u := fun u _ =>
    (P4B.smoothPhysicalPairOuterRamp_bounds b N T w u).1
  have hgeom := actual_outer_pushforward_majorant b N T V hV
    (fun _ hu => P4B.actual_W_le_smoothPhysicalPairOuterRamp hNr hT hw hu)
  have hM : M ≤ (J+2*d)*X := by
    dsimp only [M]
    rw [finiteSourceMass_eq_labelled]
    exact ((hmass N hN hev).trans (add_le_add_right ((div_le_iff₀ hX).mp hs.le) _)).trans_eq (by ring)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun u _ => productWeight_nonneg N V hV u)
  have hmain : M * P4BOriginalFineAttachedUpper.attachedDensity m r n e q a 1 (19/96) s.beta N ≤
      (currentK*(J+2*d))*singularNormalization N := by
    calc
      _ ≤ M*(currentK*(singularSeries N/Real.log (N : ℝ))) := mul_le_mul_of_nonneg_left (hD hev) hM0
      _ ≤ ((J+2*d)*X)*(currentK*(singularSeries N/Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hM (mul_nonneg (by norm_num [currentK]) (densityScale_pos h2).le)
      _ = _ := by rw [← sourceMassScale_mul_densityScale N]; dsimp only [X]; ring
  have hcap : (N : ℝ)^θ ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le hθ.le
  have hf := P4B.RealB_cast_le_attachedUpper_integer_outer_main_add_errors N f id
    (productCarrier N) (productWeight N V) hb1 hT.le zero_lt_one s.pos
    (s.lt_eighth.le.trans (by norm_num)) s.square_lt.le h2 hcap hgeom.1 hgeom.2
  have hzero := P4BSmoothOuterRampRoughness.smooth_physical_ramp_outer_signed_coprime_sum_eq_zero
    hb0 zero_lt_one h2 s.square_lt.le hw hwg f id
  rw [hzero, add_zero, signed_productWeight_eq_primeProductSignedError] at hf
  have hpaid := hf.trans (add_le_add (add_le_add (add_le_add_right hmain _) hc) hTcost)
  change (RealB b N : ℝ) ≤ (currentK*(J+2*d))*singularNormalization N + outerRow s b w N +
    d*singularNormalization N + d*singularNormalization N at hpaid
  change (RealB b N : ℝ) ≤ (currentK*J+t)*singularNormalization N + outerRow s b w N
  exact hpaid.trans_eq (by rw [← hspend]; ring)

end
end ImbalancedChen.P6OriginalFineOuterRow
