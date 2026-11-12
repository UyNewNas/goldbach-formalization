import ImbalancedChen.P4BOriginalFiniteProperWords
import ImbalancedChen.P5ActualCommonRefinedPayments

/-! The arithmetic costs of the original two good integer axes and the
true finite-rectangle row. Only moduli with nonzero coefficient enter
the row budget. The product equal to the target has its own bound. -/
namespace ImbalancedChen.P4BOriginalFiniteProperArithmetic
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalFiniteSignedTrim (pairLicence)
open P4BOriginalFiniteProperWords
open P4BOuterRampRoughness (baseline)
open P5Z.ExactOriginalSmoothDyadicPartition (cutoffIndex)
open P5Z.ActualDyadicRankPolynomial (bankLogConstant bankLogConstant_pos eventually_actual_cutoffIndex_le_log)
open P5Z.ProperPowerActualReciprocalTail (reciprocalTailBudget distanceDivisorEnvelope)
open P5Z.ProperPowerPhysicalPolynomialPayment (distanceEnvelope_linear_subpower logBudget_polynomial_free_epsilon)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ProperPowerSignedModulusPayment (meanBudget rowBudget norm_signedRow_le)
open P5Z.RoughSquareWeightedBudget (logBudget logBudget_nonneg)
open P5OriginalPrimeEndpoint (distance)

abbrev modulusExponent : ℝ := 599/1000

/-- The true physical rectangle only uses positive moduli. All zero
coefficients can be removed from both the AP sum and the coprime mean,
including at the diagonal. The constants precede all policies and N. -/
theorem exists_row_costs (eps : ℝ) (he : 0<eps) :
    ∃ C D : ℝ,0<C ∧ 0<D ∧ ∀ N : ℕ,1≤N → ∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ d∈S,0<d) → (∀ d,|c d|≤1) →
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      (∀ x : ℕ,1≤x → (x:ℝ)≤Real.exp 1*(N:ℝ) → x≠N →
        ‖signedRow S (fun d => (c d:ℂ)) N x‖≤C*(N:ℝ)^eps) ∧
      ‖signedRow S (fun d => (c d:ℂ)) N N‖≤D*(N:ℝ)^(modulusExponent+eps) := by
  obtain ⟨C,hC,H⟩ := distanceEnvelope_linear_subpower he
  let E := 4*(1+1/eps)
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨C*(Real.exp 1+2)^eps+E,1+E,by positivity,by positivity,?_⟩
  intro N hN S c hs hc hrange
  let T := S.filter (fun d => c d≠0)
  let X := (N:ℝ)^modulusExponent
  have hbase : (1:ℝ)≤N := by exact_mod_cast hN
  have hX : 0≤X := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : T⊆Finset.Icc 1 (Nat.floor X) := by
    intro d hd
    obtain ⟨hd,hz⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨hs d hd,Nat.le_floor (hrange d hz).le⟩
  have hne (x : ℕ) : signedRow S (fun d => (c d:ℂ)) N x =
      signedRow T (fun d => (c d:ℂ)) N x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hdt
    have hz : c d=0 := by
      by_contra hh
      exact hdt (Finset.mem_filter.mpr ⟨hd,hh⟩)
    simp only [hz,Complex.ofReal_zero,zero_mul]
  have hcard : (T.card:ℝ)≤X := by
    have h : T.card≤Nat.floor X := by
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr h).trans (Nat.floor_le hX)
  have hmean : meanBudget T (fun d => (c d:ℂ))≤E*(N:ℝ)^eps := by
    have hlog := logBudget_polynomial_free_epsilon (show 0≤(1:ℝ) by norm_num) he hN
      (show ((Nat.floor X:ℕ):ℝ)≤(N:ℝ)^(1:ℝ) from
        (Nat.floor_le hX).trans (Real.rpow_le_rpow_of_exponent_le hbase (by norm_num [modulusExponent])))
    calc
      _ ≤ ∑ d∈T,1/(d.totient:ℝ) := Finset.sum_le_sum (fun d _ =>
        div_le_div_of_nonneg_right (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hc d)
          (Nat.cast_nonneg _))
      _ ≤ 4*logBudget (Nat.floor X) := sum_reciprocal_totient_subset_le_log T _ hsub
      _ ≤ _ := by simpa only [E,mul_assoc] using
            (mul_le_mul_of_nonneg_left hlog (by norm_num : (0:ℝ)≤4))
  have hrow (x : ℕ) := norm_signedRow_le T (fun d => (c d:ℂ)) 1 (by norm_num)
    (fun d _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hc d) N x
  constructor
  · intro x hx hXmax hn
    have hle : x≤Nat.ceil (Real.exp 1*(N:ℝ)) := by exact_mod_cast hXmax.trans (Nat.le_ceil _)
    have hdist : ((distance N x).divisors.card:ℝ)≤
        (distanceDivisorEnvelope N (Nat.ceil (Real.exp 1*(N:ℝ))):ℝ) := by
      exact_mod_cast Finset.le_sup (f:=fun v => (distance N v).divisors.card)
        (Finset.mem_Icc.mpr ⟨hx,hle⟩)
    have hd := hdist.trans (H (Real.exp 1) (Real.exp_pos _) N hN)
    rw [hne]
    apply (hrow x).trans
    simp only [rowBudget,if_neg hn,one_mul]
    exact (add_le_add hd hmean).trans_eq (by ring)
  · rw [hne]
    apply (hrow N).trans
    simp only [rowBudget,if_pos rfl,one_mul]
    have h1 : X≤(N:ℝ)^(modulusExponent+eps) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith only [he])
    have h2 : (N:ℝ)^eps≤(N:ℝ)^(modulusExponent+eps) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by
        linarith only [show 0≤modulusExponent by norm_num [modulusExponent]])
    exact (add_le_add (hcard.trans h1)
      (hmean.trans (mul_le_mul_of_nonneg_left h2 hE.le))).trans_eq (by ring)

/-- An absolute polynomial saving of exponent 19/192 pays all proper
words at once. The only logarithms are the proper-power exponents,
the harmonic base sum and the other ordered axis. -/
theorem eventually_active_count :
    ∀ᶠ N : ℕ in atTop,2≤N ∧ ∀ (b kappa s : ℝ) (hb : 0<b),0<kappa →
      ∀ (hs : 0<s) (hgap : 2*s≤baseline b kappa-exponent),
      ((active (pairLicence hb hs hgap N) N).card:ℝ)≤
        (8*Real.exp 1*bankLogConstant)*(N:ℝ)^(1-exponent/2)*Real.log (N:ℝ)^3 := by
  have hlog : ∀ᶠ N : ℕ in atTop,1≤Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_actual_cutoffIndex_le_log 1 (by norm_num),hlog] with N hN hl
  obtain ⟨hN,hJ⟩ := hN
  have h1 : 1≤N := by omega
  have hNr : (1:ℝ)≤N := by exact_mod_cast h1
  have hpos := zero_lt_one.trans_le hNr
  have hj : ((Nat.log2 N+1:ℕ):ℝ)≤bankLogConstant*Real.log (N:ℝ) := by
    have hJ' : ((cutoffIndex N+2:ℕ):ℝ)≤bankLogConstant*Real.log (N:ℝ) := by simpa using hJ
    exact (show ((Nat.log2 N+1:ℕ):ℝ)≤((cutoffIndex N+2:ℕ):ℝ) by
      exact_mod_cast (show Nat.log2 N+1≤cutoffIndex N+2 by unfold cutoffIndex; omega)).trans hJ'
  have hlogM (M : ℕ) (hm : M≤N) : logBudget M≤2*Real.log (N:ℝ) := by
    have he := Real.log_le_log (zero_lt_one.trans_le (le_max_left 1 (M:ℝ)))
      (max_le hNr (by exact_mod_cast hm))
    unfold logBudget
    linarith
  have hroot : Nat.sqrt N≤N := Nat.sqrt_le_self N
  have hclog : 0≤bankLogConstant*Real.log (N:ℝ) :=
    mul_nonneg bankLogConstant_pos.le (by linarith only [hl])
  have hmult : ((Nat.log2 N+1:ℕ):ℝ)*logBudget (Nat.sqrt N)*logBudget N ≤
      4*bankLogConstant*Real.log (N:ℝ)^3 := by
    have he := mul_le_mul
      (mul_le_mul hj (hlogM _ hroot) (logBudget_nonneg _) hclog)
      (hlogM N le_rfl) (logBudget_nonneg _) (mul_nonneg hclog (by linarith only [hl]))
    exact he.trans_eq (by ring)
  have hscale : (N:ℝ)/Real.sqrt ((N:ℝ)^exponent)=(N:ℝ)^(1-exponent/2) := by
    simpa only [one_mul,Real.sqrt_one,one_div_one] using
      Part3.AllKFamilyProperPowerSaving.physical_scale_power_identity
        (a:=exponent) hpos (lower:=1) (by norm_num)
  refine ⟨hN,?_⟩
  intro b kappa s hb hk hs hgap
  apply (active_card_le h1 hb hk hs hgap).trans
  calc
    _ = (2*Real.exp 1*((N:ℝ)/Real.sqrt ((N:ℝ)^exponent)))*
        (((Nat.log2 N+1:ℕ):ℝ)*logBudget (Nat.sqrt N)*logBudget N) := by
      unfold reciprocalTailBudget
      ring
    _ ≤ (2*Real.exp 1*((N:ℝ)/Real.sqrt ((N:ℝ)^exponent)))*
        (4*bankLogConstant*Real.log (N:ℝ)^3) :=
      mul_le_mul_of_nonneg_left hmult (by positivity)
    _ = _ := by rw [hscale]; ring

end
end ImbalancedChen.P4BOriginalFiniteProperArithmetic
