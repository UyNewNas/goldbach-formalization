import ImbalancedChen.NormalizedSmallRosserError
import ImbalancedChen.P5OriginalU5ClassicalComplement
import ImbalancedChen.CurrentChenPairHarmonicMean
import ImbalancedChen.P5zElevenErrorTransport
import ImbalancedChen.ActualUpperDensityAssembly
import ImbalancedChen.RealHalfProductMassSuppliers

/-! The lower projection works on an entire interval of precisions. This
allows the Fine policy of all three switched costs to select the *same*
precision as the original U5 attachment. All moduli and their signed
integer coefficients still belong to the source that produced them. -/
namespace ImbalancedChen.P5OriginalU5SharedAttachment

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5PlateauPrimeBV (Policy moduli integerRho)
open P5OriginalU5CausalFinite
open P5OriginalU5AllMarkHBReserves (branches)
open P5OriginalU5ClassicalComplement (beyond)

/-- Shrink the precision ceiling before the upper selector chooses beta.
The later threshold is uniform in the full U5 triangle and every policy. -/
theorem projection_for_every_small_beta {η : ℝ} (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ ∀ β : ℝ, 0 < β → β < 1/8 → β < b →
      ∀ᶠ N : ℕ in atTop, Even N → ∀ P : Policy,
        fullProjectedMainSum N P - projectionReserve N η ≤ mainSum N β P := by
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  obtain ⟨B, _, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨C, K, hC, hK, hSieve⟩ := exists_actualLowerSmallRoughRho_density_error
  obtain ⟨Kr, hKr, hRough⟩ := exists_fixedEvenRoughAbsoluteDensity_le_powerParameters
  have hdecay : Tendsto (fun t : ℝ => (B*C*attachmentR) * (t^4 * Real.exp (-t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).const_mul (B*C*attachmentR)
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((tendsto_order.1 hdecay).2 (η*attachmentNu) (mul_pos hη hnu))
  let U := max T 1
  have hU : 0 < U := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨1/U, one_div_pos.mpr hU, ?_⟩
  intro β hβ hβ8 hβb
  have hbr : β^2 ≤ attachmentR := by
    have hs := mul_self_le_mul_self hβ.le hβ8.le
    calc
      _ ≤ (1/8:ℝ)*(1/8) := by simpa only [pow_two] using hs
      _ ≤ _ := by norm_num [attachmentR,attachmentNu]
  have hfloor : (B/β^2) * (C*Real.exp (-(1/β))) * (attachmentR/β^2) < η*attachmentNu := by
    have hu : U < 1/β := by
      simpa only [one_div_one_div] using one_div_lt_one_div_of_lt hβ hβb
    calc
      _ = (B*C*attachmentR) * ((1/β)^4 * Real.exp (-(1/β))) := by field_simp [hβ.ne'] <;> ring
      _ < _ := hT _ ((le_max_left T 1).trans hu.le)
  have hlim := tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope B C K Kr attachmentR β hβ
  have htail := (tendsto_order.1 hlim).2 (η*attachmentNu) hfloor
  obtain ⟨Ds, hDs⟩ := eventually_atTop.mp (htail.and (eventually_four_le_smallRosserPower β hβ))
  obtain ⟨Df, _, hDf⟩ := hSieve β hβ hβ8
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^attachmentNu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (eventually_ge_atTop (max Ds Df)), eventually_ge_atTop (2 : ℕ)]
    with N hlarge hN
  intro hev P
  let D := (N : ℝ)^attachmentNu
  let cap := Nat.ceil (cutoff N)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNp := zero_lt_one.trans hNr
  have hD1 : 1 < D := Real.one_lt_rpow hNr hnu
  have hDp := zero_lt_one.trans hD1
  have hlog := Real.log_pos hD1
  have hscale := hDs D ((le_max_left _ _).trans hlarge)
  have hraw := hDf D ((le_max_right _ _).trans hlarge) N cap hev
  have hw : D ^ (β^2) = smallCutoff N β := (Real.rpow_mul hNp.le _ _).symm
  have hz : D ^ attachmentR = cutoff N := by
    dsimp only [D]
    rw [← Real.rpow_mul hNp.le, attachmentNu_mul_attachmentR]
  have hL : D ^ β = smallLevel N β := (Real.rpow_mul hNp.le _ _).symm
  have hgate := attachment_gates hN hβ hβ8
  have hcap : D^(β^2) ≤ (cap : ℝ) := by
    rw [hw]
    exact hgate.2.2.trans (Nat.le_ceil _)
  have hV := actualSmallEulerProduct_pos N cap (D^(β^2)) hev
  have hVmax := hEuler N cap (by omega) hev (D^(β^2)) hscale.2 hcap
  rw [Real.log_rpow hDp] at hVmax
  let E := actualSmallRosserDensityError C K D β
  let A := (attachmentR/β^2)*(1+Kr/(β^2*Real.log D))
  have hE : 0 ≤ E := by dsimp [E,actualSmallRosserDensityError]; positivity
  have hA : 0 ≤ A := by
    have hr : 0 < attachmentR := by norm_num [attachmentR,attachmentNu]
    have hr' : 0 < Kr := by linarith only [hKr]
    dsimp [A]; positivity
  have hscalar : (actualSmallEulerProduct N cap (D^(β^2))*E)*A ≤
      η*singularSeries N/Real.log (N : ℝ) := by
    calc
      _ ≤ (B*singularSeries N/(β^2*Real.log D))*E*A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVmax hE) hA
      _ = (singularSeries N/Real.log D) *
        ((B/β^2)*E*(attachmentR/β^2)*(1+Kr/(β^2*Real.log D))) := by dsimp [A]; field_simp [hβ.ne', hlog.ne'] <;> ring
      _ ≤ (singularSeries N/Real.log D)*(η*attachmentNu) :=
        mul_le_mul_of_nonneg_left hscale.1.le (div_nonneg (singularSeries_pos N).le hlog.le)
      _ = _ := by dsimp [D]; rw [Real.log_rpow hNp]; field_simp [hnu.ne'] <;> ring
  rw [fullProjectedMainSum, projectionReserve, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  let f := P t
  have hm := hRough f N cap hev D β attachmentR hD1 hβ hbr
    (show 2 ≤ D^(β^2) by linarith only [hscale.2])
  have herr := (hraw f (D^attachmentR)).2.trans
    ((mul_le_mul_of_nonneg_left hm (mul_nonneg hV.le hE)).trans hscalar)
  have hbase := fixedEvenRoughDensity_presieveProjection f N cap (smallCutoff N β) (cutoff N) hgate.2.2
  dsimp only at herr
  simp only [hw,hz,hL] at herr
  have hrow : fullDensity N f - η * singularSeries N / Real.log (N : ℝ) ≤ density N β f := by
    dsimp only [fullDensity,density,cap,f,support,rho] at hbase herr ⊢
    linarith only [hbase,herr]
  have hscaled := mul_le_mul_of_nonneg_left hrow
    (div_nonneg (Nat.cast_nonneg (chenPrimePrefix N).card) (Nat.cast_nonneg (Nat.totient (t.1*t.2))))
  simpa only [rowMain,f,mul_sub] using hscaled

/-- Every attachment precision below the common ceiling admits the original
sharp lower count with the projected density, with only nonzero physical
moduli above D_B inside the native HB branches. -/
theorem classical_count_for_every_small_beta (t τ : ℝ) (ht : 0<t) (ht1 : t<1) (hτ : t<τ)
    (K : ℕ) {η : ℝ} (hη : 0<η) :
    ∃ b : ℝ, 0<b ∧ ∃ B : ℝ, 0≤B ∧ ∃ C : ℝ, 0<C ∧
      ∀ β : ℝ, 0<β → β<1/8 → β<b → ∀ᶠ N : ℕ in atTop, Even N → ∀ P : Policy, ∀ ζ : ℝ,
        fullProjectedMainSum N P - projectionReserve N η +
          (branches t τ ζ 6 N K β P (beyond B N β P)).re -
          C*(N : ℝ)/(Real.log (N : ℝ))^3 ≤ currentChenUpsilon5 N := by
  obtain ⟨b,hb,hproj⟩ := projection_for_every_small_beta hη
  obtain ⟨B,hB,C,hC,hcut⟩ := P5OriginalU5ClassicalComplement.exists_full_classical_payment
  obtain ⟨F,hF,hplateau⟩ := P5OriginalU5PlateauPrimeBV.eventually_original_count_lower 3
  obtain ⟨G,hG,hbranch⟩ := P5OriginalU5ShortComplement.exists_sum_to_branches t τ ht ht1 hτ K 3
  refine ⟨b,hb,B,hB,F+C+G+1,by positivity,?_⟩
  intro β hβ hβ8 hβb
  filter_upwards [hproj β hβ hβ8 hβb, hcut, hplateau, hbranch,
    P5OriginalU5AllMarkCosts.eventually_all_outer_costs 3 1 zero_lt_one]
    with N hp hcl hsmall hlarge hcost
  intro hev P ζ
  have hf := hsmall β hβ hβ8 P
  rw [P5OriginalU5ClassicalComplement.actual_classical_partition hcl.1] at hf
  have hc := (abs_le.mp (hcl.2 β hβ hβ8 P (P5OriginalU5ClassicalComplement.classicalPart B N β P)
    (fun _ h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1)
    (fun _ h => (Finset.mem_filter.mp h).2))).1
  have hl := hlarge hev β hβ hβ8 P (beyond B N β P) (Finset.filter_subset _ _) ζ
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm _).trans hl)).1
  simp only [Complex.sub_re,Complex.ofReal_re] at hreal
  have hsum : (F+C+G+1)*(N : ℝ)/(Real.log (N : ℝ))^3 =
      F*N/(Real.log (N : ℝ))^3 + C*N/(Real.log (N : ℝ))^3 +
        G*N/(Real.log (N : ℝ))^3 + 1*N/(Real.log (N : ℝ))^3 := by ring
  rw [hsum]
  linarith only [hp hev P,hf,hc,hreal,hcost hev β hβ hβ8 P]

private theorem eventual_bounded_of_limit {F : ℕ → ℝ} {L : ℝ}
    (h : Tendsto F atTop (𝓝 L)) : ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop, F N ≤ A := by
  have hA : L < |L|+1 := by linarith only [le_abs_self L]
  exact ⟨|L|+1, by positivity, ((tendsto_order.1 h).2 _ hA).mono (fun _ h => h.le)⟩

/-- The price of the per-label projection is bounded uniformly for every
reserve on the entire original triangle. The total prime prefix and the
reciprocal totients are counted with the actual selector. -/
theorem eventual_projection_reserve :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 ≤ η →
      projectionReserve N η ≤ (A*η)*singularNormalization N := by
  obtain ⟨A,hA,htri⟩ := eventual_bounded_of_limit
    (tendsto_currentChenUpsilon5_harmonic_test (fun _ => (1:ℝ)) continuousOn_const)
  obtain ⟨X,_,hX⟩ := exists_primeCounting_real_relative_error_threshold_of_real_pnt
    realHalfProduct_primeCounting_asymptotic_real 1 zero_lt_one
  refine ⟨2*A,by positivity,?_⟩
  filter_upwards [htri, eventually_ge_atTop (Nat.ceil X), eventually_ge_atTop (2:ℕ)] with N ht hNX hN
  intro η hη
  have hbound : (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1*t.2) : ℝ)) ≤ A := ht
  obtain ⟨hlog,hπ⟩ := hX (N:ℝ) ((Nat.le_ceil X).trans (by exact_mod_cast hNX))
  have hpref : chenPrimePrefix N = Nat.primesLE N := by
    ext q
    rw [mem_chenPrimePrefix,Nat.mem_primesLE]
  have hcard : ((chenPrimePrefix N).card : ℝ) ≤ 2*((N:ℝ)/Real.log (N:ℝ)) := by
    rw [hpref,Nat.primesLE_card_eq_primeCounting]
    simp only [Nat.floor_natCast,one_mul] at hπ
    linarith only [(abs_le.mp hπ).2]
  have hsum0 : 0 ≤ ∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1*t.2) : ℝ) :=
    Finset.sum_nonneg (fun t _ => one_div_nonneg.mpr (Nat.cast_nonneg _))
  have hm := mul_le_mul hcard hbound hsum0 (by positivity)
  calc
    projectionReserve N η =
        (((chenPrimePrefix N).card : ℝ) * (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1*t.2) : ℝ))) *
          (η*(singularSeries N/Real.log (N:ℝ))) := by
      rw [projectionReserve,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ (2*((N:ℝ)/Real.log (N:ℝ))*A)*(η*(singularSeries N/Real.log (N:ℝ))) :=
      mul_le_mul_of_nonneg_right hm (mul_nonneg hη (densityScale_pos hN).le)
    _ = _ := by rw [← sourceMassScale_mul_densityScale N]; ring

/-- The projection and all logarithmic costs fit this independent U5
reserve. Only the signed original large-modulus branches remain. -/
theorem normalized_count_for_every_small_beta (t τ : ℝ) (ht : 0<t) (ht1 : t<1) (hτ : t<τ)
    (K : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ b : ℝ, 0<b ∧ ∃ B : ℝ, 0≤B ∧
      ∀ β : ℝ, 0<β → β<1/8 → β<b → ∀ᶠ N : ℕ in atTop, Even N → ∀ P : Policy, ∀ ζ : ℝ,
        fullProjectedMainSum N P + (branches t τ ζ 6 N K β P (beyond B N β P)).re -
          δ*singularNormalization N ≤ currentChenUpsilon5 N := by
  obtain ⟨A,hA,hres⟩ := eventual_projection_reserve
  let η := (δ/2)/A
  have hη : 0 < η := div_pos (half_pos hδ) hA
  have hpay : A*η = δ/2 := by dsimp [η]; field_simp [hA.ne']
  obtain ⟨b,hb,B,hB,C,_,hβ⟩ := classical_count_for_every_small_beta t τ ht ht1 hτ K hη
  refine ⟨b,hb,B,hB,?_⟩
  intro β hp h8 hbβ
  filter_upwards [hβ β hp h8 hbβ, hres,
    p5z_eventually_logCube_le_singularNormalization C (δ/2) (half_pos hδ)] with N h hR hL
  intro hev P ζ
  have hr := hR η hη.le
  rw [hpay] at hr
  linarith only [h hev P ζ,hr,hL]

end
end ImbalancedChen.P5OriginalU5SharedAttachment
