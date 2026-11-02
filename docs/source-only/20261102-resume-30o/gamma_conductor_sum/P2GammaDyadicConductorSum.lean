import ImbalancedChen.P2GammaExactConductorRegrouping
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-! SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.
Complete finite dyadic and quotient summation. The large-sieve logarithm is
retained as its literal ceiling expression throughout the finite theorem.
-/

namespace ImbalancedChen.P2GammaDyadicConductorSum
noncomputable section
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping

def lsLog (Q : ℕ) : ℝ :=
  2*(Nat.ceil (Real.log ((Q : ℝ)^2)/Real.log 2) : ℝ)+12

theorem lsLog_nonneg (Q : ℕ) : 0≤lsLog Q := by unfold lsLog; positivity

theorem lsLog_mono {P Q : ℕ} (hP : 0<P) (hPQ : P≤Q) : lsLog P≤lsLog Q := by
  have hp : (0 : ℝ)<P := by exact_mod_cast hP
  have hq : (P : ℝ)≤Q := by exact_mod_cast hPQ
  have hlog := Real.log_le_log (sq_pos_of_pos hp)
    (pow_le_pow_left₀ hp.le hq 2)
  have hc := Nat.ceil_mono (div_le_div_of_nonneg_right hlog
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)
  unfold lsLog
  exact_mod_cast (show 2*Nat.ceil (Real.log ((P : ℝ)^2)/Real.log 2)+12≤
      2*Nat.ceil (Real.log ((Q : ℝ)^2)/Real.log 2)+12 by omega)

theorem largeSieveBound_eq (L Q : ℕ) :
    largeSieveBound L (1/(Q : ℝ)^2)=(L : ℝ)+lsLog Q*(Q : ℝ)^2 := by
  unfold largeSieveBound lsLog
  simp only [one_div,inv_inv,div_eq_mul_inv,inv_pow]

def dyadicIndices (Q T b : ℕ) : Finset ℕ :=
  (Finset.Ico b (Nat.log 2 Q+1)).filter (fun j => 2^j<T)

def dyadicShell (T j : ℕ) : Finset ℕ :=
  Finset.Ioc (2^j) (min (2*2^j) T)

theorem shell_log {T j r : ℕ} (hr : r ∈ dyadicShell T j) :
    Nat.log 2 (r-1)=j := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hr
  have hp : 0<2^j := Nat.two_pow_pos j
  have hr0 : r-1≠0 := by omega
  apply (Nat.log_eq_iff (Or.inr ⟨by omega,hr0⟩)).mpr
  rw [pow_succ]
  have hhi' := (le_min_iff.mp hhi).1
  omega

/-- Exact truncated cover: no duplicated boundary conductor and no dropped
last interval, including when the high-conductor range is empty. -/
theorem sum_high_eq_dyadic (Q T b : ℕ) (hTQ : T≤Q) (F : ℕ → ℝ) :
    (∑ r ∈ (Finset.Icc 2 T).filter (fun r => 2^b<r),F r) =
      ∑ j ∈ dyadicIndices Q T b, ∑ r ∈ dyadicShell T j,F r := by
  rw [← Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun r _ => (⟨Nat.log 2 (r-1),r⟩ : Σ _ : ℕ,ℕ))
    (fun p _ => p.2) ?_ ?_ ?_ ?_ ?_
  · intro r hr
    obtain ⟨hrT,hbr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr2,hrT⟩ := Finset.mem_Icc.mp hrT
    have hr0 : r-1≠0 := by omega
    have hlo := Nat.pow_log_le_self 2 hr0
    have hhi := Nat.lt_pow_succ_log_self (by omega : 1<2) (r-1)
    have hb := Nat.le_log_of_pow_le (by omega : 1<2)
      (show 2^b≤r-1 by omega)
    have hQ := Nat.log_mono_right (show r-1≤Q by omega)
    rw [Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hb,by omega⟩,by omega⟩,?_⟩
    rw [dyadicShell,Finset.mem_Ioc,le_min_iff]
    rw [pow_succ] at hhi
    omega
  · rintro ⟨j,r⟩ hp
    obtain ⟨hj,hr⟩ := Finset.mem_sigma.mp hp
    have hbj := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
    have hpj : 2^b≤2^j := Nat.pow_le_pow_right (by omega : 1≤2) hbj
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hr
    have hp0 : 0<2^b := Nat.two_pow_pos b
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega,(le_min_iff.mp hhi).2⟩,by omega⟩
  · intro r hr
    rfl
  · rintro ⟨j,r⟩ hp
    have h := shell_log (Finset.mem_sigma.mp hp).2
    simp only [h]
  · intro r hr
    rfl

private theorem sum_dyadic_powers (H : ℕ) :
    (∑ j ∈ Finset.range H,(2 : ℝ)^j)=(2 : ℝ)^H-1 := by
  induction H with
  | zero => norm_num
  | succ H ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

private theorem sum_dyadic_inverses (b h : ℕ) :
    (∑ j ∈ Finset.Ico b (b+h),1/(2 : ℝ)^j)=
      2/(2 : ℝ)^b-2/(2 : ℝ)^(b+h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show b+(h+1)=(b+h)+1 by omega,Finset.sum_Ico_succ_top (by omega),ih,pow_succ]
    field_simp
    <;> ring

theorem dyadic_inverse_sum_le (Q T b : ℕ) :
    (∑ j ∈ dyadicIndices Q T b,1/(2 : ℝ)^j)≤2/(2 : ℝ)^b := by
  calc
    _ ≤ ∑ j ∈ Finset.Ico b (Nat.log 2 Q+1),1/(2 : ℝ)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ ≤ _ := by
      by_cases hb : b≤Nat.log 2 Q+1
      · obtain ⟨h,hh⟩ := Nat.exists_eq_add_of_le hb
        rw [hh,sum_dyadic_inverses]
        have : 0≤2/(2 : ℝ)^(b+h) := by positivity
        linarith
      · rw [Finset.Ico_eq_empty (by omega)]
        simp only [Finset.sum_empty]
        positivity

theorem dyadic_power_sum_le (Q T b : ℕ) :
    (∑ j ∈ dyadicIndices Q T b,(2 : ℝ)^j)≤2*(T : ℝ) := by
  by_cases hT : T=0
  · subst T
    simp [dyadicIndices]
  have hsub : dyadicIndices Q T b⊆Finset.range (Nat.log 2 T+1) := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (by
      have := Nat.le_log_of_pow_le (by omega : 1<2) h.le
      omega)
  calc
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 T+1),(2 : ℝ)^j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (2 : ℝ)^(Nat.log 2 T+1)-1 := sum_dyadic_powers _
    _ ≤ 2*(T : ℝ) := by
      have h := Nat.pow_log_le_self 2 hT
      have h' : (2 : ℝ)^(Nat.log 2 T)≤T := by exact_mod_cast h
      rw [pow_succ]
      linarith

theorem dyadic_count_le (Q T b : ℕ) :
    (dyadicIndices Q T b).card≤Nat.log 2 Q+1 := by
  apply (Finset.card_le_card (show dyadicIndices Q T b⊆
      Finset.range (Nat.log 2 Q+1) from ?_)).trans
  · simp only [Finset.card_range]
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2

/-- A square-root expansion with all nonnegative cross terms retained. -/
private theorem sqrt_add_le (u v : ℝ) (hu : 0≤u) (hv : 0≤v) :
    Real.sqrt (u+v)≤Real.sqrt u+Real.sqrt v := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (add_nonneg hu hv)]
  nlinarith [Real.sq_sqrt hu,Real.sq_sqrt hv,Real.sqrt_nonneg u,Real.sqrt_nonneg v]

def energyProduct (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb : ℕ) : ℝ :=
  Real.sqrt (rowEnergy a Ma La)*Real.sqrt (rowEnergy b Mb Lb)

theorem energyProduct_nonneg (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb : ℕ) :
    0≤energyProduct a b Ma Mb La Lb := by unfold energyProduct; positivity

/-- Expansion of M's actual theorem, with c=lsLog(2Q). This is derived
from its square roots and energies, rather than assumed as a dyadic bound. -/
theorem inducedShell_expanded (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q R k : ℕ) (hR : 0<R) (hRQ : R≤Q) (hk : 0<k)
    (S : Finset ℕ) (hS : S⊆Finset.Ioc R (2*R)) :
    inducedShell a b Ma Mb La Lb k S ≤
      energyProduct a b Ma Mb La Lb/(k.totient : ℝ)*
        (Real.sqrt La*Real.sqrt Lb/(R : ℝ)+
          2*Real.sqrt (lsLog (2*Q))*(Real.sqrt La+Real.sqrt Lb)+
          4*lsLog (2*Q)*(R : ℝ)) := by
  let c := lsLog (2*Q)
  have hc : 0≤c := lsLog_nonneg _
  have hRr : (0 : ℝ)<R := by exact_mod_cast hR
  have hphi : (0 : ℝ)<k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hlen (L : ℕ) :
      Real.sqrt (largeSieveBound L (1/((2*R : ℕ) : ℝ)^2)) ≤
        Real.sqrt L+2*Real.sqrt c*(R : ℝ) := by
    rw [largeSieveBound_eq]
    have hlog := lsLog_mono (by omega : 0<2*R)
      (Nat.mul_le_mul_left 2 hRQ)
    calc
      _ ≤ Real.sqrt ((L : ℝ)+c*(2*(R : ℝ))^2) := by
        apply Real.sqrt_le_sqrt
        push_cast
        nlinarith [sq_nonneg (2*(R : ℝ))]
      _ ≤ Real.sqrt L+Real.sqrt (c*(2*(R : ℝ))^2) :=
        sqrt_add_le _ _ (by positivity) (by positivity)
      _ = _ := by rw [Real.sqrt_mul hc,Real.sqrt_sq (by positivity)]; ring
  have hLS := inducedShell_largeSieve a b Ma Mb La Lb R k hR hk S hS
  have hEa := rowEnergy_nonneg a Ma La
  have hEb := rowEnergy_nonneg b Mb Lb
  rw [Real.sqrt_mul (largeSieveBound_nonneg _ (by positivity)),
    Real.sqrt_mul (largeSieveBound_nonneg _ (by positivity))] at hLS
  refine hLS.trans ?_
  have hprod := mul_le_mul (hlen La) (hlen Lb)
    (Real.sqrt_nonneg _) (by positivity : 0≤Real.sqrt La+2*Real.sqrt c*(R : ℝ))
  have he := mul_le_mul_of_nonneg_right hprod
    (energyProduct_nonneg a b Ma Mb La Lb)
  have hden : 0≤1/((R : ℝ)*(k.totient : ℝ)) := by positivity
  have h := mul_le_mul_of_nonneg_left he hden
  dsimp [energyProduct,c] at h ⊢
  convert h using 1 <;>
    field_simp [hRr.ne',hphi.ne'] <;>
    ring_nf <;> simp only [Real.sq_sqrt hc] <;> ring

def highConductorTotal (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q b0 : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 Q,inducedShell a b Ma Mb La Lb k
    ((Finset.Icc 2 (Q/k)).filter (fun r => 2^b0<r))

def highU (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q b0 : ℕ) : ℝ :=
  energyProduct a b Ma Mb La Lb*
    (2*Real.sqrt La*Real.sqrt Lb/(2 : ℝ)^b0+
      2*Real.sqrt (lsLog (2*Q))*(Nat.log 2 Q+1 : ℕ)*
        (Real.sqrt La+Real.sqrt Lb))

def highV (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb Q : ℕ) : ℝ :=
  8*lsLog (2*Q)*energyProduct a b Ma Mb La Lb*(Q : ℝ)

/-- Entire fixed-k high range has the U+V/k shape. -/
theorem fixed_quotient_high_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q b0 k : ℕ) (hk : 0<k) :
    inducedShell a b Ma Mb La Lb k
      ((Finset.Icc 2 (Q/k)).filter (fun r => 2^b0<r)) ≤
      (highU a b Ma Mb La Lb Q b0+highV a b Ma Mb La Lb Q/(k : ℝ))/
        (k.totient : ℝ) := by
  let E := energyProduct a b Ma Mb La Lb
  let c := lsLog (2*Q)
  let J := dyadicIndices Q (Q/k) b0
  have hE : 0≤E := energyProduct_nonneg _ _ _ _ _ _
  have hc : 0≤c := lsLog_nonneg _
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hphi : (0 : ℝ)<k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hcover := sum_high_eq_dyadic Q (Q/k) b0 (Nat.div_le_self Q k)
    (fun r => (1/((r*k).totient : ℝ))*∑ psi : PrimitiveCharacter r,
      rowAmplitude (unitMask k a) Ma La r psi*
        rowAmplitude (unitMask k b) Mb Lb r psi)
  unfold inducedShell
  rw [hcover]
  have hshell : ∀ j ∈ J, inducedShell a b Ma Mb La Lb k (dyadicShell (Q/k) j) ≤
      E/(k.totient : ℝ)*(Real.sqrt La*Real.sqrt Lb/(2 : ℝ)^j+
        2*Real.sqrt c*(Real.sqrt La+Real.sqrt Lb)+4*c*(2 : ℝ)^j) := by
    intro j hj
    have hcut := (Finset.mem_filter.mp hj).2
    have hRQ : 2^j≤Q := hcut.le.trans (Nat.div_le_self _ _)
    have hsub : dyadicShell (Q/k) j⊆Finset.Ioc (2^j) (2*2^j) := by
      intro r hr
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hr
      exact Finset.mem_Ioc.mpr ⟨hlo,(le_min_iff.mp hhi).1⟩
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      inducedShell_expanded a b Ma Mb La Lb Q (2^j) k
        (Nat.two_pow_pos j) hRQ hk _ hsub
  calc
    _ ≤ ∑ j ∈ J,E/(k.totient : ℝ)*
        (Real.sqrt La*Real.sqrt Lb/(2 : ℝ)^j+
          2*Real.sqrt c*(Real.sqrt La+Real.sqrt Lb)+4*c*(2 : ℝ)^j) :=
      Finset.sum_le_sum fun j hj => hshell j hj
    _ = E/(k.totient : ℝ)*
        (Real.sqrt La*Real.sqrt Lb*(∑ j ∈ J,1/(2 : ℝ)^j)+
          2*Real.sqrt c*(Real.sqrt La+Real.sqrt Lb)*J.card+
          4*c*(∑ j ∈ J,(2 : ℝ)^j)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
        nsmul_eq_mul,div_eq_mul_inv]
      ring
    _ ≤ E/(k.totient : ℝ)*
        (Real.sqrt La*Real.sqrt Lb*(2/(2 : ℝ)^b0)+
          2*Real.sqrt c*(Real.sqrt La+Real.sqrt Lb)*(Nat.log 2 Q+1 : ℕ)+
          4*c*(2*((Q/k : ℕ) : ℝ))) := by
      gcongr
      · exact dyadic_inverse_sum_le Q (Q/k) b0
      · exact_mod_cast dyadic_count_le Q (Q/k) b0
      · exact dyadic_power_sum_le Q (Q/k) b0
    _ ≤ (highU a b Ma Mb La Lb Q b0+highV a b Ma Mb La Lb Q/(k : ℝ))/
        (k.totient : ℝ) := by
      have hquot : ((Q/k : ℕ) : ℝ)≤(Q : ℝ)/(k : ℝ) := by
        apply (le_div_iff₀ hkR).mpr
        exact_mod_cast Nat.div_mul_le_self Q k
      calc
        _ ≤ E/(k.totient : ℝ)*
            (Real.sqrt La*Real.sqrt Lb*(2/(2 : ℝ)^b0)+
              2*Real.sqrt c*(Real.sqrt La+Real.sqrt Lb)*(Nat.log 2 Q+1 : ℕ)+
              4*c*(2*((Q : ℝ)/(k : ℝ)))) := by gcongr
        _ = _ := by dsimp [highU,highV,E,c]; ring

/-- The complete large-conductor payment from the actual M finite LS.
The ceiling/log constant is explicit, and the last lane uses the convergent
1/(k phi(k)) sum. No small-conductor or geometric estimate is assumed. -/
theorem highConductorTotal_le (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb Q b0 : ℕ) :
    highConductorTotal a b Ma Mb La Lb Q b0 ≤
      4*(1+Real.log (max 1 (Q : ℝ)))*highU a b Ma Mb La Lb Q b0+
        8*highV a b Ma Mb La Lb Q := by
  unfold highConductorTotal
  refine (Finset.sum_le_sum fun k hk => fixed_quotient_high_le
    a b Ma Mb La Lb Q b0 k (Finset.mem_Icc.mp hk).1).trans ?_
  apply induced_quotient_charge
  · unfold highU energyProduct
    positivity
  · unfold highV energyProduct
    have := lsLog_nonneg (2*Q)
    exact mul_nonneg (by positivity) (by positivity)

end
end ImbalancedChen.P2GammaDyadicConductorSum
