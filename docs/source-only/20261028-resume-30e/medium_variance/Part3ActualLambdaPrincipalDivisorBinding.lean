import ImbalancedChen.Part3ActualMediumVarianceAtomBinding
import ImbalancedChen.Part3ActualPrincipalGramVarianceBound
import ImbalancedChen.Part3MediumActualPsiPreliminaryDispersion
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual strict-receiver Lambda_d(r), q,d representation fibres, and
reciprocal-totient divisor payment in manuscript (15). All finite
objects below use the original paperPsi carrier and dyadic owner.
-/

namespace ImbalancedChen.Part3.ActualLambdaPrincipalDivisorBindingSourceOnly

noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumOwnedCanonicalReindex20261028
open MediumActualPreliminaryCauchy20261028 MediumReceiverCutoffArithmetic20261028
open OriginalSamePsiS1OwnedAtlas MediumActualPsiPreliminaryDispersion20261028
open OriginalGevreyPoissonPacket20261028 OriginalGevreyFinalPsi20261028
open OriginalMediumPrincipalFiniteCRT ActualPrincipalGramVarianceBoundSourceOnly
open ActualFilteredPrimitiveSWSourceOnly ActualCrudeWeightedVarianceSourceOnly
open ActualLowConductorQuotientSumSourceOnly ActualMediumVarianceAtomBindingSourceOnly
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def originalLambda (atom : MediumAtom) (z : ℝ) (k : Key) (d r : ℕ) : ℂ :=
  lambdaTrim atom (strictReceiverCutoff z) (originalSmoothTrim atom) k d r

def actualQD (atom : MediumAtom) (k : Key) : Finset (ℕ × ℕ) :=
  paperPsiNaturalCarrier atom.Q1 ×ˢ activeD atom k

def qdFibre (atom : MediumAtom) (k : Key) (ell : ℕ) : Finset (ℕ × ℕ) :=
  (actualQD atom k).filter (fun p => p.1*p.2=ell)

def roughNat (k : Key) : ℕ := (2 : ℕ)^k.w

def principalCore (atom : MediumAtom) (z : ℝ) (k : Key) : ℝ :=
  ∑ p ∈ actualQD atom k, paperQWeight atom p.1 * ((p.1*p.2).totient : ℝ) *
    paperPrincipalVariance atom.alphaCarrier atom.alpha (p.1*p.2)
      (dyadicWindow k.w) (originalLambda atom z k p.2)

/-- The actual Lambda from independent owned choices has the fixed divisor bound. -/
theorem originalLambda_norm_le {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (z : ℝ) (k : Key) (d r : ℕ) :
    ‖originalLambda atom z k d r‖ ≤ tau (d*r) := by
  have h := lambdaTrim_norm_le_tau atom (strictReceiverCutoff z)
    (originalSmoothTrim atom) k d r hA
  change ‖lambdaTrim atom (strictReceiverCutoff z) (originalSmoothTrim atom) k d r‖ ≤
    ((d*r).divisors.card : ℝ) at h
  exact h

theorem roughNat_pos (k : Key) : 0 < roughNat k := pow_pos (by norm_num) _

theorem rough_window_bounds (k : Key) {r : ℕ} (hr : r ∈ dyadicWindow k.w) :
    0 < r ∧ (roughNat k : ℝ) ≤ r := by
  have h := (Finset.mem_Ico.mp hr).1
  exact ⟨(roughNat_pos k).trans_le h,by exact_mod_cast h⟩

theorem rough_window_card (k : Key) : (dyadicWindow k.w).card = roughNat k := by
  simp only [dyadicWindow,Nat.card_Ico,roughNat,pow_succ]
  omega

/-- Real support gates of the actual smooth q carrier and half-open d owner. -/
theorem actualQD_geometry {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) {p : ℕ × ℕ} (hp : p ∈ actualQD atom k) :
    0 < p.1 ∧ 0 < p.2 ∧ 0 < p.1*p.2 ∧
      keyY atom k / 2 ≤ (p.1*p.2 : ℕ) ∧
      p.1*p.2 ≤ actualVarianceCap atom k := by
  obtain ⟨hq,hd⟩ := Finset.mem_product.mp hp
  have hd' := (Finset.mem_filter.mp hd).1
  obtain ⟨hql,hqh⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hdl,hdh⟩ := Finset.mem_Ico.mp hd'
  have hQ1 : 1 ≤ atom.Q1 := hA.2.2.1
  have hDpos : 0 < (2 : ℕ)^k.d := pow_pos (by norm_num) _
  have hdlR : keyD k ≤ (p.2 : ℝ) := by exact_mod_cast hdl
  have hdhR : (p.2 : ℝ) ≤ 2*keyD k := by
    have h := hdh.le
    simpa only [keyD,pow_succ,Nat.cast_mul,Nat.cast_ofNat,mul_comm] using
      (show (p.2 : ℝ) ≤ ((2 : ℕ)^(k.d+1) : ℕ) by exact_mod_cast h)
  have hqlR : atom.Q1/2 ≤ (p.1 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hql)
  have hqhR : (p.1 : ℝ) ≤ 5*atom.Q1/2 :=
    (by exact_mod_cast hqh : (p.1 : ℝ) ≤ (Nat.floor (5*atom.Q1/2) : ℝ)).trans
      (Nat.floor_le (by linarith : 0 ≤ 5*atom.Q1/2))
  have hqposR : (0 : ℝ) < p.1 := by linarith
  have hqpos : 0 < p.1 := by exact_mod_cast hqposR
  have hdpos : 0 < p.2 := hDpos.trans_le hdl
  have hlow : keyY atom k/2 ≤ ((p.1*p.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    have h := mul_le_mul hqlR hdlR (by dsimp [keyD]; positivity)
      (by linarith : 0 ≤ atom.Q1/2)
    simpa only [keyY,div_mul_eq_mul_div] using h
  have hhigh : ((p.1*p.2 : ℕ) : ℝ) ≤ 8*keyY atom k := by
    rw [Nat.cast_mul]
    have h := mul_le_mul hqhR hdhR (Nat.cast_nonneg p.2)
      (by linarith : 0 ≤ 5*atom.Q1/2)
    have hY0 : 0 ≤ keyY atom k := by dsimp [keyY,keyD]; positivity
    dsimp only [keyY] at *
    nlinarith
  exact ⟨hqpos,hdpos,Nat.mul_pos hqpos hdpos,hlow,Nat.le_floor hhigh⟩

/-- A physical divisor fibre with a genuine Key (separate from the
natural modulus ell) admits the actual d coordinate as an injection. -/
theorem actual_qdFibre_card_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) {ell : ℕ} (hell : 0 < ell) :
    (qdFibre atom k ell).card ≤ ell.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2)
  · intro p hp
    obtain ⟨hp,hprod⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨⟨p.1,by rw [← hprod]; ring⟩,hell.ne'⟩
  · intro p hp q hq heq
    obtain ⟨hp,hpEq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq,hqEq⟩ := Finset.mem_filter.mp hq
    have hdp := (actualQD_geometry hA k hp).2.1
    have hq1 : p.1=q.1 := by
      apply Nat.eq_of_mul_eq_mul_right hdp
      calc
        p.1*p.2=ell := hpEq
        _ = q.1*q.2 := hqEq.symm
        _ = q.1*p.2 := by rw [heq]
    exact Prod.ext hq1 heq

/-- Positive sums group by the actual full level, with precisely its
divisor repetition payment and the actual cap floor(8Y). -/
theorem actual_qd_sum_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) (F : ℕ → ℝ)
    (hF : ∀ ell, 0 ≤ F ell) :
    (∑ p ∈ actualQD atom k, F (p.1*p.2)) ≤
      ∑ ell ∈ Finset.Icc 1 (actualVarianceCap atom k), tau ell*F ell := by
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => p.1*p.2) (actualQD atom k)
      (Finset.Icc 1 (actualVarianceCap atom k)) := by
    intro p hp
    have hg := actualQD_geometry hA k hp
    exact Finset.mem_Icc.mpr ⟨hg.2.2.1,hg.2.2.2.2⟩
  have hf := Finset.sum_fiberwise_of_maps_to (s := actualQD atom k)
    (t := Finset.Icc 1 (actualVarianceCap atom k)) (g := fun p => p.1*p.2) hmaps
    (fun p => F (p.1*p.2))
  calc
    _ = ∑ ell ∈ Finset.Icc 1 (actualVarianceCap atom k),
        ∑ p ∈ qdFibre atom k ell, F (p.1*p.2) := hf
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ell hell
      have he0 := (Finset.mem_Icc.mp hell).1
      have hsum : (∑ p ∈ qdFibre atom k ell, F (p.1*p.2)) =
          ((qdFibre atom k ell).card : ℝ)*F ell := by
        calc
          _ = ∑ _p ∈ qdFibre atom k ell, F ell := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
          _ = _ := by simp
      rw [hsum]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast actual_qdFibre_card_le hA k he0) (hF ell)

/-- The real reciprocal-totient bound is a fixed divisor weight, so no
subpower loss is introduced into a logarithmic-error estimate. -/
theorem one_div_totient_le_tau_div {n : ℕ} (hn : 0 < n) :
    1/(n.totient : ℝ) ≤ tau n/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  have h : (n : ℝ) ≤ (n.totient : ℝ)*tau n := by
    have h := le_totient_mul_fouvryTau_two n
    rw [fouvryTau_two] at h
    exact_mod_cast h
  exact (div_le_div_iff₀ hphi hnR).mpr (by simpa only [one_mul,mul_comm] using h)

theorem tau_le_of_dvd {n d : ℕ} (hn : 0 < n) (h : d ∣ n) : tau d ≤ tau n := by
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' h)

/-- Literal Lambda has the correct divisor/level weight inside the
principal Gram diagonal; d is a divisor of this same physical ell. -/
theorem actual_lambda_phi_diagonal_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    {p : ℕ × ℕ} (hp : p ∈ actualQD atom k) {r : ℕ} (hr : r ∈ dyadicWindow k.w) :
    ((p.1*p.2).totient : ℝ)*(roughNat k : ℝ)*‖originalLambda atom z k p.2 r‖^2 /
      (((p.1*p.2)*r).totient : ℝ)^2 ≤
        2/(keyY atom k*(roughNat k : ℝ))*tau (p.1*p.2)^4*tau r^4 := by
  let ell := p.1*p.2
  have hg := actualQD_geometry hA k hp
  have he : 0 < ell := hg.2.2.1
  have hr0 : 0 < r := (rough_window_bounds k hr).1
  have hRr : (roughNat k : ℝ) ≤ r := (rough_window_bounds k hr).2
  have hER : (0 : ℝ) < ell := by exact_mod_cast he
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hRR : (0 : ℝ) < roughNat k := by exact_mod_cast roughNat_pos k
  have hY : 0 < keyY atom k := by
    dsimp only [keyY,keyD]
    have hq := hA.2.2.1
    positivity
  have hd : p.2 ∣ ell := ⟨p.1,by dsimp only [ell]; ring⟩
  have hnorm : ‖originalLambda atom z k p.2 r‖ ≤ tau ell*tau r :=
    (originalLambda_norm_le hA z k p.2 r).trans
      ((tau_mul_le p.2 r).trans (mul_le_mul_of_nonneg_right (tau_le_of_dvd he hd) (tau_nonneg r)))
  have hinv : 1/((ell*r).totient : ℝ) ≤ tau ell*tau r/((ell : ℝ)*(r : ℝ)) := by
    refine (one_div_totient_le_tau_div (Nat.mul_pos he hr0)).trans ?_
    rw [Nat.cast_mul]
    exact div_le_div_of_nonneg_right (tau_mul_le ell r) (by positivity)
  have hphi : (ell.totient : ℝ) ≤ ell := by exact_mod_cast Nat.totient_le ell
  have hgeom : (roughNat k : ℝ)/((ell : ℝ)*(r : ℝ)^2) ≤
      2/(keyY atom k*(roughNat k : ℝ)) := by
    apply (div_le_div_iff₀ (mul_pos hER (pow_pos hrR 2)) (mul_pos hY hRR)).mpr
    have hYell : keyY atom k ≤ 2*(ell : ℝ) := by
      have h := hg.2.2.2.1
      dsimp only [ell] at *
      linarith
    have hsq : (roughNat k : ℝ)^2 ≤ (r : ℝ)^2 := pow_le_pow_left₀ hRR.le hRr 2
    have h := mul_le_mul hYell hsq (sq_nonneg _) (by positivity : 0 ≤ 2*(ell : ℝ))
    convert h using 1 <;> ring
  have hb : ((ell.totient : ℝ)*(roughNat k : ℝ))*‖originalLambda atom z k p.2 r‖^2 *
      (1/((ell*r).totient : ℝ))^2 ≤
        ((ell : ℝ)*(roughNat k : ℝ))*(tau ell*tau r)^2*
          (tau ell*tau r/((ell : ℝ)*(r : ℝ)))^2 := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hphi hRR.le
      · exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      · exact sq_nonneg _
      · positivity
    · exact pow_le_pow_left₀ (by positivity) hinv 2
    · exact sq_nonneg _
    · positivity
  calc
    _ = ((ell.totient : ℝ)*(roughNat k : ℝ))*‖originalLambda atom z k p.2 r‖^2 *
        (1/((ell*r).totient : ℝ))^2 := by rw [div_pow]; ring
    _ ≤ _ := hb
    _ = ((roughNat k : ℝ)/((ell : ℝ)*(r : ℝ)^2))*tau ell^4*tau r^4 := by
      field_simp [hER.ne',hrR.ne']
      <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgeom (pow_nonneg (tau_nonneg ell) 4))
      (pow_nonneg (tau_nonneg r) 4)

end
end ImbalancedChen.Part3.ActualLambdaPrincipalDivisorBindingSourceOnly
