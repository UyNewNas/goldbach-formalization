import ImbalancedChen.P4BOriginalHighRankPostModulusFibres

/-! All actual mother rows on one rectangular rho and one logarithmic
band. Restore the original HB scalars once and insert the result in the
positive upper count at the chosen legal trim and resolution. -/
namespace ImbalancedChen.P4BOriginalHighRankPostModulusCount
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BOriginalUpperFourierTailPaid (groupEval groupEval_sub_le groupScalarMass sourceScalarMass
  sourceScalarMass_le dyadicConstant dyadicConstant_pos)
open P4BUpperPairOrderedRowGeometry (rowRoles)
open P4BUpperPairOrderedRowModes (rowBank modeBank rowBank_eq_modeBank)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le target_le_countingScale)
open P4BOriginalHighRankScheduledCount (outerWidth resolution eventually_width eventually_RealB_le_high_modes)
open P4BOriginalHighRankMotherModes (modes)
open P4BOriginalHighRankPostModulusFibres (split exists_split_payment)
open P4BOriginalFiniteSmoothCount (Q coefficient mass)
open P4BOriginalAllRankClassicalRange (wholeHigh)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOuterRampRoughness (baseline)

def retainedMother (b kap : ℝ) (N K A cj ck : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) :=
  groupEval cj (fun j bs => groupEval ck (fun l cs =>
    split (u:=2*(j+1)) (v:=2*(l+1)) b kap (outerWidth N) N kap0 cj ck zeta
      (Fin.append (blockVector (2*(j+1)) bs) (blockVector (2*(l+1)) cs))
      (beforeHBCutoff K [cj,ck])
      (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
      (Fin.append (rowRoles j) (rowRoles l)) S c A))

def band (b kap : ℝ) (N K A : ℕ) (kap0 zeta : ℝ) (S : Finset ℕ) (c : ℕ→ℝ) :=
  ∑ js∈chartBank N 2,retainedMother b kap N K A (js.getD 0 0) (js.getD 1 0) kap0 zeta S c

/-- After the complete original signed Q-sum, all HB scalars, original group
labels and true complementary windows, the omitted frequencies cost one
arbitrary logarithmic saving. All retained arithmetic remains explicit. -/
theorem exists_all_mother_payment :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
      ∀ᶠ N : ℕ in atTop,∀ (K A : ℕ) (kap0 zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ)
      (a omega : ℝ) (k : ℕ) (ell : ℝ) (S : Finset ℕ),S⊆Q omega N →
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ‖modes b kap (outerWidth N) N K kap0 S c-band b kap N K A kap0 zeta S c‖≤
        C*(N:ℝ)/logScale (countingScale N)^(A+3) := by
  obtain ⟨C,hC,HC⟩ := exists_split_payment
  refine ⟨49*dyadicConstant^14*C,by positivity,?_⟩
  intro b kap hb hb1 hk hgate
  filter_upwards [eventually_width _ (half_pos (sub_pos.mpr hgate))] with N hw
  obtain ⟨hN,hs,hs',hres,_⟩ := hw
  have hN0 : 0<N := by omega
  have hg : 2*outerWidth N≤baseline b kap-19/96 := by linarith
  have hG : 2*outerWidth N≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  intro K A kap0 zeta m r n e q a omega k ell S hS
  dsimp only
  intro hr
  let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
  let L := logScale (countingScale N)
  let E := C*(N:ℝ)/L^(A+14+3)
  have hL := logScale_one_le (countingScale_one_le hN0)
  have hp : 0<L := zero_lt_one.trans_le hL
  have hE : 0≤E := div_nonneg (mul_nonneg hC (Nat.cast_nonneg N)) (pow_nonneg hp.le _)
  have H (cj ck : ℕ) :
      ‖modeBank b kap (outerWidth N) N K cj ck kap0 S (fun d => (c d:ℂ))-
        retainedMother b kap N K A cj ck kap0 zeta S c‖≤(groupScalarMass cj*groupScalarMass ck)*E := by
    rw [←rowBank_eq_modeBank hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs hG]
    change ‖groupEval cj _-groupEval cj _‖≤_
    rw [mul_assoc]
    apply groupEval_sub_le
    intro j hj bs hbs
    apply groupEval_sub_le
    intro l hl cs hcs
    have hm : 2*(j+1)+2*(l+1)≤12 := by
      have h1 := Finset.mem_range.mp hj
      have h2 := Finset.mem_range.mp hl
      omega
    exact HC hN0 hb hb1 hk hg hres hm kap0 zeta A cj ck _ _ _ _ m r n e q a omega k ell S hS hr
  unfold modes band
  rw [←Finset.sum_sub_distrib]
  calc
    _≤∑ js∈chartBank N 2,‖modeBank b kap (outerWidth N) N K (js.getD 0 0) (js.getD 1 0) kap0
          S (fun d => (c d:ℂ))-retainedMother b kap N K A (js.getD 0 0) (js.getD 1 0) kap0 zeta S c‖ :=
      norm_sum_le _ _
    _≤∑ js∈chartBank N 2,(groupScalarMass (js.getD 0 0)*groupScalarMass (js.getD 1 0))*E :=
      Finset.sum_le_sum (fun js _ => H _ _)
    _=sourceScalarMass N*E := by rw [←Finset.sum_mul]; rfl
    _≤(49*dyadicConstant^14*L^14)*E :=
      mul_le_mul_of_nonneg_right (sourceScalarMass_le hN0) hE
    _=_ := by
      dsimp only [E]
      rw [show A+14+3=(A+3)+14 by omega,pow_add]
      field_simp [hp.ne']
      ring

/-- Choose a legal trim after kappa and the requested cap. The modulus family,
fixed beta and aligned k coincide in the density and retained finite-band term.
An arithmetic evaluation of this remaining term is still necessary. -/
theorem exists_trimmed_RealB_le_band {b kappa : ℝ} (hb : (1:ℝ)/2<b) (hb1 : b<1)
    (hk : 0<kappa) (cap : ℝ) (hcap : 0<cap) :
    ∃ kap0 : ℝ,0<kap0 ∧ kap0<cap ∧ kap0<1 ∧ kap0<kappa/(4*(1+kappa)) ∧ 19/96<baseline b kap0 ∧
      ∀ (K : ℕ),2≤K → ∀ eta : ℝ,0<eta → ∀ᶠ N : ℕ in atTop,Even N →
      0≤mass b kap0 (outerWidth N) N ∧
      |mass b kap0 (outerWidth N) N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (nu beta : ℝ),
      0<nu → 0<beta → beta≤1 → nu*beta^2≤19/96 → nu*beta<1/1000 →
      let omega := nu*beta^2
      let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+
        (band b kap0 N K 0 kap0 zeta (wholeHigh m r n e q a omega k N (nu*beta)) c).re+
        eta*singularNormalization N := by
  obtain ⟨kap0,h0,hc,h1,ht,hgate⟩ := P4BOriginalHighRankLocalLevel.exists_direct_trim hb hk cap hcap
  refine ⟨kap0,h0,hc,h1,ht,hgate,?_⟩
  intro K hK eta he
  obtain ⟨C,hC,H⟩ := exists_all_mother_payment
  have hb0 : 0<b := by linarith
  filter_upwards [eventually_RealB_le_high_modes hb hb1 h0 h1 hgate K hK (eta/2) (half_pos he),
    H hb0 hb1.le h0 hgate,p5z_eventually_logCube_le_singularNormalization C (eta/2) (half_pos he),
    eventually_one_le_nat_log,eventually_ge_atTop (2:ℕ)] with N hB hM hfee hlog hN
  intro hev
  obtain ⟨hpos,happrox,hcount⟩ := hB hev
  refine ⟨hpos,happrox.trans (by linarith),?_⟩
  intro zeta m r n e q a k nu beta hnu hb' hbOne hw hell
  dsimp only
  intro hr
  let omega := nu*beta^2
  let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
  let S := wholeHigh m r n e q a omega k N (nu*beta)
  let full := modes b kap0 (outerWidth N) N K kap0 S c
  let main := band b kap0 N K 0 kap0 zeta S c
  have hsub : S⊆Q omega N := fun d hd => (Finset.mem_sdiff.mp hd).1
  have htail : ‖full-main‖≤C*N/logScale (countingScale N)^3 :=
    hM K 0 kap0 zeta m r n e q a omega k (nu*beta) S hsub hr
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hX := countingScale_one_le (show 0<N by omega)
  have hNX := target_le_countingScale N
  have hl : Real.log (N:ℝ)≤logScale (countingScale N) := by
    have H := Real.log_le_log hNpos (show (N:ℝ)≤7*countingScale N by linarith)
    unfold logScale; linarith
  have htail' : full.re-main.re≤eta/2*singularNormalization N := by
    have hx := div_le_div_of_nonneg_left (mul_nonneg hC (Nat.cast_nonneg N))
      (pow_pos (by linarith : 0<Real.log (N:ℝ)) 3) (pow_le_pow_left₀ (by linarith) hl 3)
    simpa only [Complex.sub_re] using (Complex.re_le_norm (full-main)).trans (htail.trans (hx.trans hfee))
  have HC := hcount m r n e q a k nu beta hnu hb' hbOne hw hell hr
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+full.re+
    eta/2*singularNormalization N at HC
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+main.re+
    eta*singularNormalization N
  linarith only [HC,htail']

end
end ImbalancedChen.P4BOriginalHighRankPostModulusCount
