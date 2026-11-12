import ImbalancedChen.Part5OriginalH430OwnedThetaWord
import ImbalancedChen.Part5OriginalH430CutoffCoherence
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-! The arithmetic normalization on every original owner, with the literal
prime-box weight, repeated primes and a common derived physical prime floor. -/
namespace ImbalancedChen.Part5OriginalH430OwnedPrimeBoxWeight
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization Part5OriginalH430CutoffCoherence
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430SameQHistoryCells Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OwnedMemberMass Part5OriginalH430OwnedThetaWord
open Part5OriginalH430RootIntervalTheta (literalScale)
open Part5OriginalH430SelectedBankCarrierSupply

def CeilingBelowWord (p : PhysicalNode) : Prop := ∀ x ∈ word p, p.ceiling ≤ x

private theorem oneBelow {p : PhysicalNode} {x s : ℝ} (hw : CeilingBelowWord p)
    (hx : x ≤ p.ceiling) : CeilingBelowWord (appendOne p x s) := by
  intro y hy
  rw [word_appendOne, List.mem_append, List.mem_singleton] at hy
  rcases hy with h | rfl
  · exact hx.trans (hw _ h)
  · exact le_rfl

private theorem pairBelow {p : PhysicalNode} {x y s : ℝ} (hw : CeilingBelowWord p)
    (hx : x ≤ y) (hy : y ≤ p.ceiling) : CeilingBelowWord (appendPair p x y s) := by
  intro v hv
  rw [word_appendPair, List.mem_append, List.mem_cons, List.mem_singleton] at hv
  rcases hv with h | rfl | rfl
  · exact (hx.trans hy).trans (hw _ h)
  · exact hx
  · exact le_rfl

theorem member_ceilingBelowWord {lo hi : ℝ} {mesh d : ℕ} {p : TypedNode}
    {code : Program mesh d} {z : Coordinates d}
    (hw : CeilingBelowWord p.physical) (hz : Member lo hi d p code z) :
    CeilingBelowWord (realize d p code z).physical := by
  induction d generalizing p with
  | zero => exact hw
  | succ d ih =>
    apply ih _ hz.2.2.2
    have hd := hz.2.2.1
    change CeilingBelowWord (perform p.physical (code 0).1 (z 0))
    generalize hs : (code 0).1 = s at hd ⊢
    cases s
    case buchstabUpper => exact oneBelow hw hd.2.1.2.1
    case buchstabLower => exact oneBelow hw hd.2.2.1.2.1
    case w1Singleton => exact oneBelow hw hd.2.1.2.1
    case w2Singleton => exact oneBelow hw hd.2.1.2.1
    case w2Pair => exact pairBelow hw hd.2.1.2.1.le hd.2.1.2.2.1
    all_goals exact hw

def primeFloor (N : ℕ) : ℝ := (N:ℝ) ^ (frozenResidualFloor/6)

theorem owned_letter_floor {N n m mesh : ℕ} {k : Root} {tau : ℝ} {c : RootKey n m}
    {h : Label N mesh} (hN : 2 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hh : h ∈ ownedMembers N n m mesh k tau c)
    {p : ℕ} (hp : p ∈ labelWord h) : primeFloor N ≤ (p:ℝ) := by
  let v := (labelNode n tau h).physical
  have hv := (mem_ownedMembers.mp hh).1
  have hs := owned_support hN ht ht' hn hh
  dsimp only at hs
  have hc : 0 < v.ceiling := hs.1.2.2.2.2
  have hfit : residual v ≤ v.argument*v.ceiling := valid_label_cutoffFits hv
  have hlow : frozenResidualFloor/6 ≤ v.ceiling := by
    have harg : v.argument * v.ceiling ≤ 6 * v.ceiling :=
      mul_le_mul_of_nonneg_right hs.2.2.2.1.2 hc.le
    linarith only [hs.2.2.1.1, hs.2.1, hfit, harg]
  have hroot : CeilingBelowWord
      (frozenRoot n h.2.1 tau (physicalPrime N h.2.2.1.val)).physical := by
    simp [CeilingBelowWord, frozenRoot, sourceRoot, word]
  have hall : CeilingBelowWord v := member_ceilingBelowWord hroot hv.2.2.2.2
  have hw : word v = (labelWord h).map (physicalPrime N) :=
    history_word_dictionary N n h.2.1 tau h.2.2.1.val _ _
  have hmem : physicalPrime N p ∈ word v := by
    rw [hw]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hx := hlow.trans (hall _ hmem)
  have hp' : p.Prime := (integerWord_letters [h.2.2.1.val] h.2.2.2.1 (labelPrimes h)
    (fun q hq => (List.mem_singleton.mp hq).symm ▸ hv.1) hv.2.2.1 p hp).1
  have hNr : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hp0 : (0:ℝ) < p := Nat.cast_pos.mpr hp'.pos
  rw [primeFloor, Real.rpow_def_of_pos (zero_lt_one.trans hNr), ← Real.exp_log hp0]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm (Real.log (N:ℝ))] using
    (le_div_iff₀ (Real.log_pos hNr)).mp hx

theorem primeFloor_tendsto : Tendsto primeFloor atTop atTop :=
  (tendsto_rpow_atTop (div_pos frozenResidualFloor_pos (by norm_num : (0:ℝ)<6))).comp
    tendsto_natCast_atTop_atTop

def primeBoxWord (ps : List ℕ) : ℝ := (ps.map (fun p => 1/((p:ℝ)-1))).prod

theorem primeBoxWord_ofFn {r : ℕ} (p : Fin r → ℕ) :
    primeBoxWord (List.ofFn p) = ∏ i, 1/((p i:ℝ)-1) := by
  simp [primeBoxWord, List.map_ofFn, List.prod_ofFn, Function.comp_def]

theorem primeBox_ratio {A : ℝ} (hA : 4 ≤ A) (ps : List ℕ)
    (hs : ∀ p ∈ ps, A ≤ (p:ℝ)) :
    1 ≤ primeBoxWord ps * (ps.prod:ℝ) ∧
      primeBoxWord ps * (ps.prod:ℝ) ≤ (1+4/A)^ps.length := by
  induction ps with
  | nil => simp [primeBoxWord]
  | cons p ps ih =>
    have hp := hs p (List.mem_cons_self ..)
    have h0 : (0:ℝ) < (p:ℝ)-1 := by linarith
    have hA0 : 0 < A := by linarith
    have ha : 1/((p:ℝ)-1)*(p:ℝ) = 1 + 1/((p:ℝ)-1) := by
      field_simp [h0.ne'] <;> ring
    have hb : 1/((p:ℝ)-1) ≤ 4/A := (div_le_div_iff₀ h0 hA0).mpr (by linarith)
    have hc : 1 ≤ 1+1/((p:ℝ)-1) := by have := (one_div_pos.mpr h0).le; linarith
    have ht := ih (fun q hq => hs q (List.mem_cons_of_mem _ hq))
    have he : primeBoxWord (p::ps)*((p::ps).prod:ℝ) =
        (1+1/((p:ℝ)-1)) * (primeBoxWord ps*(ps.prod:ℝ)) := by
      rw [← ha]; simp [primeBoxWord, mul_assoc, mul_comm, mul_left_comm]
    rw [he,List.length_cons,pow_succ]
    exact ⟨one_le_mul_of_one_le_of_one_le hc ht.1,
      (mul_le_mul (show 1+1/((p:ℝ)-1) ≤ 1+4/A by linarith only [hb]) ht.2 (zero_le_one.trans ht.1)
        (by positivity)).trans_eq (mul_comm _ _)⟩

private theorem wordLen {mesh depth : ℕ} (old : List ℕ) (code : Program mesh depth)
    (q : IntegerCoordinates depth) :
    (integerWord depth old code q).length ≤ old.length + 2*depth := by
  induction depth generalizing old with
  | zero => simp [integerWord]
  | succ d ih =>
    have ht := ih (old ++ appendedWord (code 0).1 (q 0)) (tail code) (tail q)
    have hs : (appendedWord (code 0).1 (q 0)).length ≤ 2 := by
      cases (code 0).1 <;> simp [appendedWord]
    rw [List.length_append] at ht
    change (integerWord d _ _ _).length ≤ _
    omega

def boxRate (N : ℕ) : ℝ := (1 + 4 / primeFloor N)^881 - 1

theorem boxRate_tendsto : Tendsto boxRate atTop (𝓝 0) := by
  have h := (tendsto_const_nhds.add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (4:ℝ)) atTop (𝓝 4)).mul
    (tendsto_inv_atTop_zero.comp primeFloor_tendsto)) : Tendsto
      (fun n : ℕ => 1+4*(primeFloor n)⁻¹) atTop (𝓝 (1+4*0)))
  simpa [boxRate,div_eq_mul_inv] using (h.pow 881).sub (tendsto_const_nhds (x := (1:ℝ)))

/-- Exact finite-event comparison to the prime-box weights used by
actualPrimeBoxTestSum. The normalizer is H_N and the parent level stays
attached to its original root fibre. -/
theorem owned_primeBox_absolute {N n m mesh : ℕ} {k : Root} {tau : ℝ} {c : RootKey n m}
    {h : Label N mesh} (hN : 2 ≤ N) (he : Even N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hA : 4 ≤ primeFloor N)
    (hh : h ∈ ownedMembers N n m mesh k tau c) :
    |thetaAtom N (cellQ N n c.1) (labelPrefix h) / singularNormalization N -
      literalScale N * (4 / Lkey c h) * primeBoxWord (labelWord h)| ≤
      |literalScale N| * (4 / Lkey c h) * (boxRate N / ((labelWord h).prod:ℝ)) := by
  let ps := labelWord h
  have hp (p : ℕ) (hps : p ∈ ps) : primeFloor N ≤ (p:ℝ) := owned_letter_floor hN ht ht' hn hh hps
  have h1 := word_to_harmonic hA ps hp 1
  have h2 := primeBox_ratio hA ps hp
  have hprodNat := Part5OriginalH430IntegerItineraries.prod_pos (old := ps) (fun p hps => by
    exact_mod_cast (show (0:ℝ) < p by linarith only [hp p hps,hA]))
  have hprod : (0:ℝ) < ps.prod := Nat.cast_pos.mpr hprodNat
  have hlen := wordLen [h.2.2.1.val] h.2.2.2.1 (labelPrimes h)
  have hd : ps.length ≤ 881 := by
    change (integerWord _ _ _ _).length ≤ _
    simp only [List.length_cons, List.length_nil] at hlen
    have := h.1.isLt
    omega
  have hfloorpos : 0 < primeFloor N := by linarith only [hA]
  have hinc : 1 ≤ 1+4/primeFloor N := by
    linarith only [div_pos (by norm_num : (0:ℝ)<4) hfloorpos]
  have hm := pow_le_pow_right₀ hinc hd
  have hdiff : |wordFactor 1 ps - primeBoxWord ps| ≤ boxRate N / (ps.prod:ℝ) := by
    apply (le_div_iff₀ hprod).mpr
    rw [← abs_of_pos hprod, ← abs_mul, sub_mul, abs_le]
    unfold boxRate
    constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,hm]
  have s := owned_support hN ht ht' hn hh
  dsimp only at s
  have hl := frozenResidualFloor_pos.trans_le s.2.2.1.1
  rw [owned_theta_density hN he ht ht' hn hh]
  change |literalScale N*(4*wordFactor 1 ps/Lkey c h) -
    literalScale N*(4/Lkey c h)*primeBoxWord ps| ≤ _
  rw [show literalScale N*(4*wordFactor 1 ps/Lkey c h) -
        literalScale N*(4/Lkey c h)*primeBoxWord ps =
        literalScale N*(4/Lkey c h)*(wordFactor 1 ps-primeBoxWord ps) by ring,
    abs_mul,abs_mul,abs_of_pos (div_pos (by norm_num) hl)]
  exact mul_le_mul_of_nonneg_left hdiff (mul_nonneg (abs_nonneg _) (by positivity))

end
end ImbalancedChen.Part5OriginalH430OwnedPrimeBoxWeight

