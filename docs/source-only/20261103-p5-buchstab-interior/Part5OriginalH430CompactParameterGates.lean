import ImbalancedChen.P2OriginalCompactMovingGateMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original finite-net proof is extended from one real parameter to an
arbitrary metric parameter space. This is needed for a simultaneously
moving residual exponent and BOTH interval endpoints. The pointwise
prime theorem, finite arithmetic sandwich and closed-wall payment are
reused. Uniform convergence is derived, not added as a licence.
-/

namespace ImbalancedChen.Part5OriginalH430CompactParameterGates

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalCompactMovingGateMass (Coord closedCube moving_gate_sum_sandwich)

variable {P : Type*} [MetricSpace P]

def parameterSum {d r : ℕ} (N : ℕ) (a b : ℝ)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : P → Fin r → ℝ)
    (F : P × Coord d → ℝ) (t : P) : ℝ :=
  actualPrimeBoxTestSum N (fun _ => a) (fun _ => b)
    ((primeAffineGateRegion A (c t)).indicator (fun x => F (t,x)))

def parameterIntegral {d r : ℕ} (a b : ℝ)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : P → Fin r → ℝ)
    (F : P × Coord d → ℝ) (t : P) : ℝ :=
  ∫ x in logPrimeBox (fun _ => a) (fun _ => b) ∩ primeAffineGateRegion A (c t),
    F (t,x) * (∏ i, 1/x i)

theorem parameter_fixed_limit {d r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (F : P × Coord d → ℝ)
    (hF : Continuous F) (t : P) :
    Tendsto (fun N : ℕ => parameterSum N a b A c F t) atTop
      (𝓝 (parameterIntegral a b A c F t)) :=
  tendsto_actualPrimeBoxTestSum_cube_affineGates ha hab A (c t) hA
    (fun x => F (t,x)) (hF.comp (continuous_const.prodMk continuous_id)).continuousOn

theorem kernel_oscillation {d : ℕ} {K : Set P} (hK : IsCompact K)
    (a b : ℝ) (F : P × Coord d → ℝ) (hF : Continuous F)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s ∈ K, ∀ t ∈ K, dist t s < delta →
      ∀ x ∈ closedCube d a b, |F (t,x)-F (s,x)| ≤ eta := by
  have hc : IsCompact (K ×ˢ closedCube d a b) :=
    hK.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨delta, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hF.continuousOn) eta heta
  refine ⟨delta, hd, ?_⟩
  intro s hs t ht hdist x hx
  have hh := hmod (t,x) ⟨ht,hx⟩ (s,x) ⟨hs,hx⟩
    (by simpa only [Prod.dist_eq, dist_self,
      max_eq_left (dist_nonneg : 0 ≤ dist t s)] using hdist)
  simpa only [Real.dist_eq] using hh.le

/-- Neighbourhoods, wall widths and prime thresholds are chosen before
any later target and any nearby residual/endpoint assignment. -/
theorem local_parameter_oscillation {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun t => c t j))
    (F : P × Coord d → ℝ) (hF : Continuous F)
    (hbound : ∀ t ∈ K, ∀ x ∈ closedCube d a b, |F (t,x)| ≤ B)
    {epsilon : ℝ} (he : 0 < epsilon) (s : P) (hs : s ∈ K) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      ∀ t ∈ K, dist t s < delta →
        |parameterSum N a b A c F t-parameterSum N a b A c F s| < epsilon := by
  let M : ℝ := (∏ _i : Fin d, Real.log (b/a))+1
  have hM : 0 < M := by
    have hp : 0 ≤ ∏ _i : Fin d, Real.log (b/a) :=
      Finset.prod_nonneg (fun _ _ => Real.log_nonneg ((one_le_div ha).mpr hab.le))
    dsimp [M]
    linarith
  let eta := epsilon/(4*(M+1))
  let zeta := epsilon/(4*(B+1))
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hzeta : 0 < zeta := by dsimp [zeta]; positivity
  have hebudget : eta*(M+1) = epsilon/4 := by
    dsimp [eta]
    field_simp [show M+1 ≠ 0 by linarith] <;> ring
  have hzbudget : zeta*(B+1) = epsilon/4 := by
    dsimp [zeta]
    field_simp [show B+1 ≠ 0 by linarith] <;> ring
  obtain ⟨width, hwidth, Tw, hTw, hstrip⟩ :=
    exists_actualPrimeAffineWallStrip_mass_lt ha hab A (c s) hA zeta hzeta
  obtain ⟨df, hdf, hfo⟩ := kernel_oscillation hK a b F hF heta
  have hce : ∀ᶠ t : P in 𝓝 s, ∀ j, |c t j-c s j| < width := by
    apply eventually_all.mpr
    intro j
    simpa only [Real.dist_eq] using
      Metric.tendsto_nhds.mp (hc j).continuousAt width hwidth
  obtain ⟨dc, hdc, hco⟩ := Metric.mem_nhds_iff.mp hce
  have hmass : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin d => a) (fun _ => b) < M :=
    (tendsto_actualPrimeBoxMass _ _ (fun _ => ha) (fun _ => hab)).eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨Tm, hTm⟩ := eventually_atTop.mp hmass
  refine ⟨min df dc, lt_min hdf hdc, max 2 (max Tw Tm), ?_⟩
  intro N hN t ht hd
  have hN1 : 1 < N := by omega
  have hS := hstrip N (by omega)
  have hM' := hTm N (by omega)
  have hf' := hfo s hs t ht (hd.trans_le (min_le_left _ _))
  have hc' : ∀ j, |c t j-c s j| ≤ width :=
    fun j => (hco (show t ∈ Metric.ball s dc from
      hd.trans_le (min_le_right _ _)) j).le
  have hh := moving_gate_sum_sandwich hN1 heta.le hB A (c s) (c t)
    (fun x => F (s,x)) (fun x => F (t,x)) hc' hf' (hbound s hs)
  change |parameterSum N a b A c F t-parameterSum N a b A c F s| ≤ _ at hh
  have hm := mul_le_mul_of_nonneg_left hM'.le heta.le
  have hw := mul_le_mul_of_nonneg_left hS.le hB
  nlinarith only [hh, hm, hw, hebudget, hzbudget, heta, hzeta, hM, hB, he]

/-- The product compactness argument supplies a single actual threshold;
it does not take a maximum over an infinite family of pointwise thresholds. -/
theorem compact_uniform_parameter_gates {d r : ℕ} {K : Set P} (hK : IsCompact K)
    {a b B : ℝ} (ha : 0 < a) (hab : a < b) (hB : 0 ≤ B)
    (A : Fin r → Coord d →L[ℝ] ℝ) (hA : ∀ j, A j ≠ 0)
    (c : P → Fin r → ℝ) (hc : ∀ j, Continuous (fun t => c t j))
    (F : P × Coord d → ℝ) (hF : Continuous F)
    (hbound : ∀ t ∈ K, ∀ x ∈ closedCube d a b, |F (t,x)| ≤ B)
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ t ∈ K,
      |parameterSum N a b A c F t-parameterIntegral a b A c F t| < epsilon := by
  have hlocal (s : K) := local_parameter_oscillation hK ha hab hB A hA c hc F hF
    hbound (by positivity : 0 < epsilon/4) s.1 s.2
  choose delta hd T hT using hlocal
  obtain ⟨net, hnet⟩ := hK.elim_finite_subcover (fun s : K => Metric.ball s.1 (delta s))
    (fun _ => Metric.isOpen_ball) (by
      intro t ht
      exact mem_iUnion.mpr ⟨⟨t,ht⟩, Metric.mem_ball_self (hd ⟨t,ht⟩)⟩)
  have hcenters : ∀ᶠ N : ℕ in atTop, ∀ s ∈ net,
      T s ≤ N ∧ |parameterSum N a b A c F s.1-parameterIntegral a b A c F s.1| < epsilon/4 := by
    apply (Finset.eventually_all net).mpr
    intro s hs
    exact (eventually_ge_atTop (T s)).and (by
      simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
        (parameter_fixed_limit ha hab A hA c F hF s.1) (epsilon/4) (by positivity))
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hcenters
  refine ⟨T0, ?_⟩
  intro N hN t ht
  obtain ⟨s, hs, hst⟩ := mem_iUnion₂.mp (hnet ht)
  have hnear := hT s N (hT0 N hN s hs).1 t ht hst
  have hlim : |parameterIntegral a b A c F t-parameterIntegral a b A c F s.1| ≤ epsilon/4 := by
    apply le_of_tendsto (((parameter_fixed_limit ha hab A hA c F hF t).sub
      (parameter_fixed_limit ha hab A hA c F hF s.1)).abs)
    filter_upwards [eventually_ge_atTop (T s)] with n hn
    exact (hT s n hn t ht hst).le
  have hcenter := (hT0 N hN s hs).2
  have htri := (abs_sub_le (parameterSum N a b A c F t)
    (parameterSum N a b A c F s.1) (parameterIntegral a b A c F t)).trans
      (add_le_add le_rfl (abs_sub_le _ (parameterIntegral a b A c F s.1) _))
  rw [abs_sub_comm (parameterIntegral a b A c F s.1)] at htri
  linarith

end
end ImbalancedChen.Part5OriginalH430CompactParameterGates
