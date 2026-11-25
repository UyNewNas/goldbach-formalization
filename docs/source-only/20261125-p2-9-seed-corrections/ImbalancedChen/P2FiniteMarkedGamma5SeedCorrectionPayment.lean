import ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionCarrier
import ImbalancedChen.P4AOriginalFiniteAll22FineDensity

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionPayment
noncomputable section
open Filter Finset Real
open P2FiniteMarkedGamma5NativeSeedSum (Index fixedWeight)
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor)
open Part5OriginalH430PhysicalRoots (Root)
open Part5OriginalH430SameQHistoryCells (cellQ)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry rank oldRank tailRank mark_nonneg)
open P2FiniteMarkedGamma5SeedCellReadout (planAt acceptAt)
open P2FiniteMarkedGamma5SeedCorrectionCarrier
open P2FiniteMarkedGamma5RadialRoughMass (cut cutExponent cutExponent_pos eventually_cut_le_half_floor)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open P2FiniteMarkedGamma5CoarseAtlasMass (uniform_mass_bound mass)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFiniteFallbackPolicy (rho)
open scoped Classical Topology BigOperators

private abbrev S {n : ℕ} (N : ℕ) (v : Entry n) :=
  Part3.labelledPrimeTuples (rank v) (2*N)

/-- A fixed weight family with the actual N target in both quantities.
The modulus carrier and real coefficients may move after the threshold. -/
private theorem entry_paid {n : ℕ} (v : Entry n) (root : Root) (tau : ℝ)
    (mesh : Index 430 → ℕ) {h : ℝ} (hp : 0<h) (h8 : h≤1/8) {eta : ℝ} (he : 0<eta) :
    let W := actualWeight v root tau mesh hp h8
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (D : Finset ℕ) (R : ℕ→ℝ),
      D ⊆ Icc 1 N → (∀ d∈D, |R d|≤1) →
      |p5z_labelledCoprimeCorrection (S N v) Part3.labelledProduct (W N) D R| ≤ eta*singularNormalization N ∧
      p5z_labelledSmallPrimeMass (S N v) Part3.labelledProduct (W N) N (Nat.ceil (cutoff N))
        ≤ eta*singularNormalization N := by
  let W := actualWeight v root tau mesh hp h8
  let T := fun N => kept N (W N)
  let V := fun (N : ℕ) (x : smallTuple N (rank v)) => W N (enlarge x)
  have hs (N : ℕ) : T N ⊆ Part3.labelledPrimeTuples (rank v) N := filter_subset _ _
  have hpos (N : ℕ) (x) (_ : x∈T N) : 0 ≤ V N x :=
    actual_nonneg v root tau mesh hp h8 _
  have hscale : ∀ᶠ N : ℕ in atTop, scaleThreshold frozenLeafCutoffFloor≤(N:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨J,hJ,H⟩ := uniform_mass_bound
  have hmass (e : ℝ) (he' : 0<e) : ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (T N) (V N) ≤ (J+e)*((N:ℝ)/log (N:ℝ)) := by
    filter_upwards [H,hscale,eventually_cut_le_half_floor,eventually_ge_atTop (2:ℕ)]
      with N HN hsc hf hN
    intro _
    have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    have hnorm := div_pos (log_pos hNr) (zero_lt_one.trans hNr)
    have H' := HN (oldRank v) (tailRank v) v.property (planAt mesh v)
      (acceptAt root tau mesh v N) (log (cellQ N n v.val.2.1)) h hp h8
    have heq : p5z_labelledMass (T N) (V N) =
        mass N (oldRank v) (tailRank v) (planAt mesh v) (acceptAt root tau mesh v N)
          (log (cellQ N n v.val.2.1)) h := by
      rw [compress_mass v root tau mesh hp h8 hN hsc hf]
      apply sum_congr rfl
      intro u _
      exact actual_at_rank v root tau mesh hp h8 u hsc
    rw [heq]
    calc
      _ ≤ J/(log (N:ℝ)/(N:ℝ)) := (le_div_iff₀ hnorm).mpr (by simpa only [mul_comm] using H')
      _ = J*((N:ℝ)/log (N:ℝ))  := by rw [div_div_eq_mul_div]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (Nat.cast_nonneg N) (log_pos hNr).le)
  have hc := p5z_eventually_marked_correction_le T V hs hpos cutExponent 1 1 J
    cutExponent_pos (by norm_num) (by norm_num) hJ.le
    (Filter.Eventually.of_forall (fun N _ x hx j => (mem_filter.mp hx).2.2.2 j))
    hmass eta he
  let U := fun N => (T N).filter (fun x => Part3.labelledProduct x ≤ N)
  have hsmall := p5z_eventually_marked_smallPrimeMass_le_ceil U V
    (fun N => (filter_subset _ _).trans (hs N)) 1 (by norm_num)
    (fun _ _ hx => (mem_filter.mp (mem_filter.mp hx).1).2.2.1)
    (fun _ _ hx => (mem_filter.mp hx).2) (19/96:ℝ) (by norm_num) eta he
  filter_upwards [hc,hsmall,hscale,eventually_cut_le_half_floor,eventually_ge_atTop (2:ℕ)]
    with N Hc Hs hsc hf hN
  intro heven D R hD hR
  constructor
  · rw [← compress_correction v root tau mesh hp h8 hN hsc hf D R]
    exact Hc heven D N R hD (by simp) hR
  · rw [← compress_small v root tau mesh hp h8 hN hsc hf]
    exact Hs

/-- The pointwise fallback estimates need only the real active support
receipt. For the Fine-selected family it is part of exists_fine_same_rho_hdensity;
positivity and the absolute coefficient bound below use the original bank. -/
theorem actual_fallback_errors (n : ℕ) (root : Root) (tau : ℝ) (mesh : Index 430→ℕ)
    {h : ℝ} (hp : 0<h) (h8 : h≤1/8) {epsilon : ℝ} (he : 0<epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (B : Bank) (r p : ℕ) (e : ℚ) (q : ℕ)
      (a omega tauGrid L : ℝ),
      let D := moduli N ((N:ℝ)^omega)
      let R := rho B r p e q a omega N tauGrid L
      (∀ d, R d ≠ 0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) →
      let W := fun v : Entry n => actualWeight v root tau mesh hp h8 N
      |∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledCoprimeCorrection (S N v) Part3.labelledProduct (W v) D R| +
      (∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledSmallPrimeMass (S N v) Part3.labelledProduct (W v) N (Nat.ceil (cutoff N)))
      ≤ epsilon*singularNormalization N := by
  let A : ℝ := ∑ v : Entry n, fixedWeight v.val.1
  have hA : 0 ≤ A := sum_nonneg (fun v _ => mark_nonneg v.val.1)
  let eta := epsilon/(2*(A+1))
  have heta : 0<eta := div_pos he (by positivity)
  have H := eventually_all_finite.mpr
    (fun v : Entry n => entry_paid v root tau mesh hp h8 heta)
  filter_upwards [H,eventually_ge_atTop (2:ℕ),eventually_singularNormalization_pos] with N HN hN hnormal
  intro hev B r p e q a omega grid L
  dsimp only
  intro hsupp
  let D := moduli N ((N:ℝ)^omega)
  let R := rho B r p e q a omega N grid L
  let D' := D.filter (fun d => R d ≠ 0)
  have hD : D' ⊆ Icc 1 N := by
    intro d hd
    obtain ⟨hmem,hne⟩ := mem_filter.mp hd
    have hpos := (P4AUpperTaggedBetaAttachment.support_squarefree N N _ (cutoff N) hmem).ne_zero
    have hR := hsupp d hne
    have hn1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
    have hupper : (N:ℝ)^(599/1000:ℝ)≤(N:ℝ) := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hn1 (by norm_num : (599/1000:ℝ)≤1)
    exact mem_Icc.mpr ⟨by omega,by exact_mod_cast (hR.le.trans hupper)⟩
  have hR (d : ℕ) (_ : d∈D') : |R d| ≤ 1 :=
    P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ _
  let W := fun v : Entry n => actualWeight v root tau mesh hp h8 N
  let C := fun v : Entry n => p5z_labelledCoprimeCorrection (S N v) Part3.labelledProduct (W v) D R
  let E := fun v : Entry n => p5z_labelledSmallPrimeMass (S N v) Part3.labelledProduct (W v) N
    (Nat.ceil (cutoff N))
  have HC (v : Entry n) : |C v| + E v ≤ 2*eta*singularNormalization N := by
    have heq : C v = p5z_labelledCoprimeCorrection (S N v) Part3.labelledProduct (W v) D' R := by
      unfold C p5z_labelledCoprimeCorrection D'
      rw [sum_filter]
      apply sum_congr rfl
      intro d _
      by_cases hz : R d=0 <;> simp [hz]
    obtain ⟨hc,hh⟩ := HN v hev D' R hD hR
    rw [heq]
    linarith
  have hAll := sum_le_sum (fun (v : Entry n) (_ : v∈univ) =>
    mul_le_mul_of_nonneg_left (HC v) (mark_nonneg v.val.1))
  have habs := abs_sum_le_sum_abs (fun v : Entry n => fixedWeight v.val.1*C v) univ
  have hrewrite : (∑ v : Entry n, |fixedWeight v.val.1*C v|) = ∑ v : Entry n, fixedWeight v.val.1*|C v| := by
    apply sum_congr rfl
    intro v _
    rw [abs_mul,abs_of_nonneg (mark_nonneg v.val.1)]
  rw [hrewrite] at habs
  have hsum : (∑ v : Entry n, fixedWeight v.val.1*|C v|) +
      (∑ v : Entry n, fixedWeight v.val.1*E v) ≤ A*(2*eta*singularNormalization N) := by
    simpa only [mul_add,sum_add_distrib,← sum_mul,A] using hAll
  have hbudget : A*(2*eta) ≤ epsilon := by
    calc
      _ ≤ (A+1)*(2*eta) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = epsilon := by dsimp [eta]; field_simp [show A+1≠0 by positivity]; ring
  have hlast := mul_le_mul_of_nonneg_right hbudget hnormal.le
  change |∑ v : Entry n, fixedWeight v.val.1*C v| +
    (∑ v : Entry n, fixedWeight v.val.1*E v) ≤ _
  exact ((add_le_add_right habs _).trans hsum).trans (by simpa only [mul_assoc] using hlast)

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionPayment
