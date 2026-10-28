import ImbalancedChen.P5OriginalWRealEndpointCapacities
import ImbalancedChen.P5SelectedRealWholeAtomGroups
import ImbalancedChen.Part3ActualWResidualCompletion
import ImbalancedChen.Part3ActualWFineWordAdapter
import ImbalancedChen.P5ZU1011OriginalW16ResidueUniform
import ImbalancedChen.P5ActualSmallBetaMonomialCost

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL W program is computed ONCE from real upper endpoints of the
entire four-marked-plus-rough word. Its first two original positions are
initialized exactly as in the manuscript; the unread p2,p3 and residual
word enter the actual three-capacity run and first-overflow completion.
All support/capacity inputs follow from the independent original eligible
near-cap certificate and actual residual endpoint cubes/budget. No actual
prime representative, target allocation or tuplewise decision fibre is a
premise. This port is distinct from old compact-W4 policies.
-/

namespace ImbalancedChen.P5Z.OriginalWWholeRealAssignment
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalNearCapRealEndpointGeometry OriginalWRealEndpointCapacities
open PresievedRoughSlotAffineGates SelectedRealEndpointSupport SelectedRealWholeAtomGroups
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open U1011OriginalW16FactorMonomials U1011OriginalW16ResidueUniform

def initial {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (A : ℝ) : Bins (Fin 4 ⊕ Fin r) :=
  let ac := actualTwoCapacityGreedy (weight N u v) A [Sum.inl 1]
  ⟨ac.1, [Sum.inl 0], ac.2⟩

def suffix (r : ℕ) : List (Fin 4 ⊕ Fin r) :=
  [Sum.inl 2, Sum.inl 3] ++ (List.finRange r).map Sum.inr

def out {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (B : Box) (eta : ℚ) (A : ℝ) :
    Bins (Fin 4 ⊕ Fin r) :=
  complete (weight N u v) A (middleCapacity B eta N) (rightCapacity B eta N A)
    (initial N u v A) (suffix r)

def groups {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (B : Box) (eta : ℚ) (A : ℝ) :
    List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) × List (Fin 4 ⊕ Fin r) :=
  let g := out N u v B eta A
  (g.left, g.middle, g.right)

def endpointFactors {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (B : Box) (eta : ℚ) (A : ℝ) :
    ℝ × ℝ × ℝ :=
  let g := out N u v B eta A
  (wp (weight N u v) g.left, wp (weight N u v) g.middle, wp (weight N u v) g.right)

theorem endpointFactors_positive {r N : ℕ} (hN : 1 < N) (u : LogFour)
    (v : Fin r → ℝ) (B : Box) (eta : ℚ) (A : ℝ) :
    0 < (endpointFactors N u v B eta A).1 ∧
      0 < (endpointFactors N u v B eta A).2.1 ∧ 0 < (endpointFactors N u v B eta A).2.2 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hp (l : List (Fin 4 ⊕ Fin r)) : 0 < wp (weight N u v) l := by
    apply List.prod_pos
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact Real.rpow_pos_of_pos hn0 _
  exact ⟨hp _, hp _, hp _⟩

theorem initial_partition {r : ℕ} (N : ℕ) (u : LogFour) (v : Fin r → ℝ) (A : ℝ) :
    ((initial N u v A).left ++ (initial N u v A).middle ++ (initial N u v A).right).Perm
      [Sum.inl 0, Sum.inl 1] := by
  let ac := actualTwoCapacityGreedy (weight N u v) A [Sum.inl 1]
  have hp := actualTwoCapacityGreedy_partition (weight N u v) A [Sum.inl 1]
  have hm : (ac.1 ++ [Sum.inl 0] ++ ac.2).Perm ([Sum.inl 0] ++ (ac.1 ++ ac.2)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := ac.1) (l₂ := [Sum.inl 0])).append_right ac.2
  exact hm.trans (hp.perm.append_left [Sum.inl 0])

/-- The true whole-word W computation returns its actual original trace,
complete product, positivity, and success/first-overflow capacities.
All endpoint support and initialization bounds are DERIVED here. -/
theorem actual_W_whole_real_cases {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0) (hu32 : u 3 ≤ u 2)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hvlate : ∀ i, v i ≤ u 2) {roughWidth : ℝ}
    (hrw : roughWidth ≤ (delta wPolicy B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < (physicalResidual wPolicy B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta wPolicy B eta : ℝ) / 64) :
    let g := out N u v B eta A
    let w := weight N u v
    Trace (initial N u v A) (suffix r) g ∧
      (g.left ++ g.middle ++ g.right).Perm (wholeLabels r) ∧
      total w g = wp w (wholeLabels r) ∧ Positive w g ∧
      (Bounded w A (middleCapacity B eta N) (rightCapacity B eta N A) g ∨
        (middleCapacity B eta N < wp w g.middle ∧
          wp w g.middle ≤ (N : ℝ) ^ (actualSelectedSubproductUpper (1 + 3 * kappa)
            (nu wPolicy B eta : ℝ) - (delta wPolicy B eta : ℝ)) ∧
          wp w g.left ≤ A ∧
          wp w g.right ≤ runCapacity B eta N / (A * wp w g.middle))) := by
  let w := weight N u v
  let level : ℝ := (nu wPolicy B eta : ℝ) - 2 * (delta wPolicy B eta : ℝ)
  let U : ℝ := (N : ℝ) ^ (actualSelectedSubproductUpper (1 + 3 * kappa)
    (nu wPolicy B eta : ℝ) - (2 * (nu wPolicy B eta : ℝ) - 1) - (delta wPolicy B eta : ℝ))
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hd : (0 : ℝ) < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  obtain ⟨hB, hC, hABC, hfirst, hsecond, hlate⟩ := actual_W_real_capacity_inputs hN B eta hv hw hc heta
    u hlo hhi hu2 hu10 A hA hAupper hk0 hk
  have hsquare : PrefixSquareBound w (A * rightCapacity B eta N A) [Sum.inl 1] := by
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [w, weight, exponent, Sum.elim_inl, List.take_zero, List.map_nil,
      List.prod_nil, List.getElem_cons_zero, one_mul] using hsecond
  obtain ⟨hpart, hleft, hright⟩ := actualTwoCapacityGreedy_correct w hA hC [Sum.inl 1] hsquare
  have hinit : Bounded w A (middleCapacity B eta N) (rightCapacity B eta N A) (initial N u v A) := by
    exact ⟨hleft, by simpa [initial, wp, w, weight, exponent] using hfirst, hright⟩
  have hpositive : Positive w (initial N u v A) := by
    have hpos (l : List (Fin 4 ⊕ Fin r)) : 0 < wp w l :=
      List.prod_pos (fun a ha => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        exact Real.rpow_pos_of_pos hn0 _)
    exact ⟨hpos _, hpos _, hpos _⟩
  have hseed : total w (initial N u v A) = wp w [Sum.inl 0, Sum.inl 1] := by
    have hprod := hpart.prod_eq w
    simpa [initial, total, wp, w, mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun z : ℝ => w (Sum.inl 0) * z) hprod
  have hres := actual_padded_endpoint_reserves wPolicy B eta hv hw hc heta u hlo hhi hrw
  have hfull : ∀ j : Fin 4, fullSquare j u ≤ level := fun j => by
    dsimp [level]
    linarith [hres.2.1 j]
  have hselected : ∀ j : Fin 4, ¬ Selected wPolicy j → selectedSquare wPolicy j u ≤ level := by
    intro j hj
    simpa [Selected, wPolicy, selectedSquare, selectedMass, fullSquare] using hfull j
  have hbudget : (∑ i : Fin 4, u i) + ((physicalResidual wPolicy B eta : ℝ) + roughWidth) ≤ level := by
    dsimp [level]
    linarith [hres.2.2.1]
  have hsfull := (original_endpoint_append_support hN wPolicy u v level
    ((physicalResidual wPolicy B eta : ℝ) + roughWidth)
    hfull hselected hv0 hvanti hcubes hbudget).1
  have hword : [Sum.inl (0 : Fin 4), Sum.inl 1] ++ suffix r = wholeLabels r := by
    simp [suffix, wholeLabels, front]
  have hfullword : PrefixSquareBound w (runCapacity B eta N) ([Sum.inl 0, Sum.inl 1] ++ suffix r) := by
    simpa only [hword, runCapacity, level, w] using hsfull
  have hslots : ∀ q ∈ suffix r, 0 < w q ∧ w q ≤ U := by
    intro q hq
    refine ⟨Real.rpow_pos_of_pos hn0 _, ?_⟩
    have hqlog : exponent u v q ≤ u 2 := by
      rcases List.mem_append.mp hq with hq | hq
      · simp only [List.mem_cons, List.mem_singleton] at hq
        rcases hq with rfl | rfl
        · rfl
        · exact hu32
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
        exact hvlate i
    have hl := hlate (exponent u v q) hqlog
    have hlogs := (Real.rpow_le_rpow_left_iff hn).mp (by
      simpa only [middleCapacity, ← Real.rpow_add hn0] using hl)
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [U]; linarith)
  obtain ⟨htrace, hprod, hcases⟩ := complete_correct w hAp hinit hpositive hslots hseed hfullword
  have hpos := trace_positive w htrace hpositive (fun q hq => (hslots q hq).1)
  have hperm := (Part3.ActualWFineWordAdapter.trace_perm htrace).trans
    ((initial_partition N u v A).append_right (suffix r))
  have hpartfull : ((out N u v B eta A).left ++ (out N u v B eta A).middle ++
      (out N u v B eta A).right).Perm (wholeLabels r) := by
    simpa only [Part3.ActualWFineWordAdapter.flatten, hword] using hperm
  refine ⟨htrace, hpartfull, by simpa only [hword] using hprod, hpos, ?_⟩
  rcases hcases with hbounded | ⟨hblo, hbhi, ha, hc'⟩
  · exact Or.inl hbounded
  · refine Or.inr ⟨hblo, hbhi.trans_eq ?_, ha, hc'⟩
    dsimp [middleCapacity, U]
    rw [← Real.rpow_add hn0]
    congr 1
    ring

/-- The SAME computed real W groups satisfy the three original numeric
monomials in BOTH real program branches. The tiny moving-alpha range is
paid by the genuine padded W cap; no critical lower bound is imposed on
a successful small middle product. -/
theorem actual_W_whole_real_monomials {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0) (hu32 : u 3 ≤ u 2)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hvlate : ∀ i, v i ≤ u 2) {roughWidth : ℝ}
    (hrw : roughWidth ≤ (delta wPolicy B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < (physicalResidual wPolicy B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta wPolicy B eta : ℝ) / 64) :
    let abc := endpointFactors N u v B eta A
    let d : ℝ := (delta wPolicy B eta : ℝ)
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ (N : ℝ) ^ (1 - 4 * d) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 15 * d / 4) ∧
      (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 39 * d / 8) := by
  let abc := endpointFactors N u v B eta A
  let d : ℝ := (delta wPolicy B eta : ℝ)
  let nu0 : ℝ := (nu wPolicy B eta : ℝ)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hd : 0 < d := by exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  obtain ⟨ha, hb, hcpos⟩ := endpointFactors_positive hN u v B eta A
  obtain ⟨htrace, hperm, hprod, hpos, hcases⟩ := actual_W_whole_real_cases hN B eta hv hw hc heta
    u hlo hhi hu2 hu10 hu32 v hv0 hvanti hvlate hrw hcubes A hA hAupper hk0 hk
  have hres := actual_padded_endpoint_reserves wPolicy B eta hv hw hc heta u hlo hhi hrw
  have hnures : nu0 + 60 * d ≤ 153 / 256 := by
    have hcap := hres.1
    change nu0 + 60 * d < 153 / 256 - (3 / 8 : ℝ) * u 2 at hcap
    linarith
  rcases hcases with hbounded | ⟨hlower, hupper, hleft, hright⟩
  · have hleft' : abc.1 ≤ A := hbounded.1
    have hmiddle' : abc.2.1 ≤ (N : ℝ) ^ (2 * nu0 - 1) := hbounded.2.1
    have hright' : abc.2.2 ≤ (N : ℝ) ^ (1 - nu0 - 2 * d) / A := hbounded.2.2
    have hbase := W_success_monomials hn hAp ha hb hcpos (by linarith : nu0 ≤ 153 / 256)
      hleft' hmiddle' hright'
    let d' : ℝ := 15 * d / 16
    have hright'' : abc.2.2 ≤ (N : ℝ) ^ (1 - nu0 - 2 * d') / A := hright'.trans
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [d']; linarith)) hAp.le)
    have hsecond := W_success_second_residue hn (show 0 ≤ d' by dsimp [d']; positivity)
      (show kappa ≤ d' by dsimp [d']; dsimp [d] at hk; linarith)
      hAp ha hb hcpos (show nu0 + 64 * d' ≤ 153 / 256 by dsimp [d']; linarith)
      hleft' hmiddle' hright''
    refine ⟨hleft', hbase.1, ?_, hbase.2.2⟩
    exact hsecond.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [d']; linarith))
  · have hleft' : abc.1 ≤ A := hleft
    have hmiddle' : (N : ℝ) ^ (2 * nu0 - 1) ≤ abc.2.1 := hlower.le
    have hupper' : abc.2.1 ≤ (N : ℝ) ^ actualSelectedSubproductUpper (1 + 3 * kappa) nu0 :=
      hupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [d]; linarith))
    have hcap : A * abc.2.1 * abc.2.2 ≤ (N : ℝ) ^ (nu0 - 2 * d) := by
      have h := (le_div_iff₀ (mul_pos hAp hb)).mp hright
      simpa only [runCapacity, nu0, d, mul_assoc, mul_comm, mul_left_comm] using h
    obtain ⟨h1, h2, h3⟩ := selectedPair_monomials hn hAp ha hb hcpos hcap hmiddle' hupper' hleft'
    exact ⟨hleft', h1, h2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)), h3⟩

/-- The ACTUAL nonzero common beta supplies e<N^epsilon and is charged
only to the third factor of THIS SAME frozen W assignment. Both original
program outcomes retain positive fixed-power margins after attachment. -/
theorem actual_W_whole_beta_monomials {r N cap betaRank e : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0) (hu32 : u 3 ≤ u 2)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hvlate : ∀ i, v i ≤ u 2) {roughWidth : ℝ}
    (hrw : roughWidth ≤ (delta wPolicy B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < (physicalResidual wPolicy B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta wPolicy B eta : ℝ) / 64)
    (w epsilon : ℝ) (hepsilon : epsilon ≤ (delta wPolicy B eta : ℝ) / 4)
    (hbeta : ActualAll16UnrestrictedResidualConvolution.rawBetaWeight N cap betaRank w
      ((N : ℝ) ^ epsilon) e ≠ 0) :
    let abc := endpointFactors N u v B eta A
    let d : ℝ := (delta wPolicy B eta : ℝ)
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * ((e : ℝ) * abc.2.2) ^ 2 ≤ (N : ℝ) ^ (1 - 3 * d) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 *
        ((e : ℝ) * abc.2.2) ^ 2 ≤ (N : ℝ) ^ (2 - 3 * d) ∧
      (A * ((e : ℝ) * abc.2.2) / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 *
        ((e : ℝ) * abc.2.2) ^ 2 ≤ (N : ℝ) ^ (2 - 4 * d) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  let abc := endpointFactors N u v B eta A
  let d : ℝ := (delta wPolicy B eta : ℝ)
  have hd : 0 < d := by exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  obtain ⟨ha, hb, hcpos⟩ := endpointFactors_positive hN u v B eta A
  obtain ⟨hleft, h1, h2, h3⟩ := actual_W_whole_real_monomials hN B eta hv hw hc heta u hlo hhi
    hu2 hu10 hu32 v hv0 hvanti hvlate hrw hcubes A hA hAupper hk0 hk
  obtain ⟨hepos, heupper⟩ := ActualSmallBetaMonomialCost.actual_raw_beta_endpoint hbeta
  have hepos' : (0 : ℝ) < e := by exact_mod_cast hepos
  obtain ⟨h1', h2', h3'⟩ := ActualSmallBetaMonomialCost.third_factor_beta_cost hn
    (zero_lt_one.trans_le hA) ha hb hcpos hepos' heupper.le h1 h2 h3
  exact ⟨hleft, h1'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
    h2'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
    h3'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))⟩

end
end ImbalancedChen.P5Z.OriginalWWholeRealAssignment
