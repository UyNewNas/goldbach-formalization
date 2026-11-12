import ImbalancedChen.Part5OriginalH430ClassicalSmoothPhysicalRoughMass

/-! Absolute true coprime recentering and the original small-additive-prime
fee. The tuple cap is 2N, while the target in every test and coefficient is N. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRankArithmetic
noncomputable section
open Finset Real
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open Part5OriginalH430ClassicalSmoothRankCoordinates (rank)
open Part5OriginalH430ClassicalSmoothRankSupport (W W_bounds)
open Part5OriginalH430ClassicalSmoothPositiveSieve (coprimePart smallPart)
open Part5OriginalH430ClassicalSmoothPrimorialEnvelope
open Part5OriginalH430ClassicalSmoothPhysicalRoughMass
open scoped Classical BigOperators

def fibreBound : ℝ := ∑ k : Fin 201,((k.val^k.val:ℕ):ℝ)

theorem fibre_nonneg : 0≤fibreBound := sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem fibre_le {k : ℕ} (hk : k≤200) : ((k^k:ℕ):ℝ)≤fibreBound := by
  let i : Fin 201 := ⟨k,by omega⟩
  exact single_le_sum (fun j (_ : j∈(univ : Finset (Fin 201))) =>
    show (0:ℝ)≤((j.val^j.val:ℕ):ℝ) from Nat.cast_nonneg _) (mem_univ i)

theorem small_rank {N r : ℕ} (cs : List ℕ) (ν δ h c : ℝ) (hN : 1≤N)
    (hk : rank cs.length r≤200) :
    smallPart N ν δ h c (Nat.ceil (cutoff N)) cs r≤(2*fibreBound)*(N:ℝ)^(19/96:ℝ) := by
  let k := rank cs.length r
  let S := Part3.labelledPrimeTuples k (2*N)
  let w := fun t : Fin k → Fin (2*N+1) => W cs t ν δ h c
  have ht := P5zLabelledIntegerShiftPositiveSieve.smallPrimeMass_le S (fun _ h => h)
    w 1 zero_le_one (fun t _ => (W_bounds cs t ν δ h c).2) N (Nat.ceil (cutoff N))
  have hp : 1≤cutoff N := one_le_rpow (by exact_mod_cast hN) (by norm_num : (0:ℝ)≤19/96)
  have hceil := (Nat.ceil_lt_add_one (show 0≤cutoff N from zero_le_one.trans hp)).le
  have hc2 : ((Nat.ceil (cutoff N):ℕ):ℝ)≤2*cutoff N := by linarith only [hp,hceil]
  have hh := mul_le_mul (fibre_le hk) hc2 (Nat.cast_nonneg _) fibre_nonneg
  change p5z_labelledSmallPrimeMass S Part3.labelledProduct w N _≤_
  have hsmall : p5z_labelledSmallPrimeMass S Part3.labelledProduct w N (Nat.ceil (cutoff N))≤
      ((k^k:ℕ):ℝ)*(Nat.ceil (cutoff N):ℕ) := by simpa only [one_mul] using ht
  exact hsmall.trans (hh.trans_eq (by unfold cutoff; ring))

theorem correction_rank :
    ∃ A : ℝ,0<A ∧ ∀ (B : Bank) (round n : ℕ) (e : ℚ) (q : ℕ) (a ω : ℝ)
      (N : ℕ) (τ L ν δ h c : ℝ) (cs : List ℕ) (r : ℕ),
      2≤N → Even N → (N:ℝ)^ω≤cutoff N → cut N≤(N:ℝ)^(1/90:ℝ)/2 →
      0<h → h≤1/8 → 0<c → c≤1/8 → rank cs.length r≤200 →
        |coprimePart N ν δ h c (moduli N ((N:ℝ)^ω)) (rho B round n e q a ω N τ L) cs r|≤
          A*(N:ℝ)^(1-1/96:ℝ)*log (N:ℝ) := by
  obtain ⟨C,hC,prime⟩ := prime_divisor_cost
  let A := (2*C)*200*3*(fibreBound+1)
  have hA : 0<A := by
    have hf := fibre_nonneg
    dsimp only [A]
    positivity
  refine ⟨A,hA,?_⟩
  intro B round n e q a ω N τ L ν δ h c cs r hN heven hw hz hh hh' hc hc' hk
  let k := rank cs.length r
  let S := Part3.labelledPrimeTuples k (2*N)
  let w := fun t : Fin k → Fin (2*N+1) => W cs t ν δ h c
  let D := moduli N ((N:ℝ)^ω)
  let R := rho B round n e q a ω N τ L
  let U := (2/cut N)*(C*log (N:ℝ))
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hNp := zero_lt_one.trans hNr
  have hlog := (log_pos hNr).le
  have hcut : 0<cut N := rpow_pos_of_pos hNp _
  have hU : 0≤U := mul_nonneg (div_nonneg (by norm_num) hcut.le) (mul_nonneg hC.le hlog)
  have hR (d : ℕ) : |R d|≤1 := P4AUpperTaggedBetaAttachment.rho_abs_le_one _ _ _ _ _ _ _ _ d
  have hrow (t : Fin k → Fin (2*N+1)) (ht : t∈S) :
      w t*(∑ d∈D,if Nat.Coprime (Part3.labelledProduct t) d then 0 else |R d|/(d.totient:ℝ))≤
        w t*((k:ℝ)*U) := by
    by_cases hwt : w t=0
    · simp only [hwt,zero_mul,le_refl]
    have hs := (nonzero_slots t (by omega) hz hh hh' hc hc' hwt).1
    apply mul_le_mul_of_nonneg_left _ (W_bounds cs t ν δ h c).1
    exact tuple_divisor_cost t ht D R (fun d _ => hR d)
      (fun i => prime hN heven _ hw ((mem_filter.mp ht).2 i) hcut (hs i))
  have hw0 (t : Fin k → Fin (2*N+1)) : 0≤w t := (W_bounds cs t ν δ h c).1
  have hfinite : |coprimePart N ν δ h c D R cs r|≤((k:ℝ)*U)*p5z_labelledMass S w := by
    change |p5z_labelledCoprimeCorrection S Part3.labelledProduct w D R|≤_
    rw [p5z_markedCoprimeCorrection_eq_neg_sum,abs_neg]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ t∈S,∑ d∈D,|w t*(R d*(if Nat.Coprime (Part3.labelledProduct t) d then 0 else 1/(d.totient:ℝ)))| :=
        sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
      _ = ∑ t∈S,w t*(∑ d∈D,if Nat.Coprime (Part3.labelledProduct t) d then 0 else |R d|/(d.totient:ℝ)) := by
        apply sum_congr rfl
        intro t _
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        by_cases hd : Nat.Coprime (Part3.labelledProduct t) d
        · simp only [if_pos hd,mul_zero,abs_zero]
        · simp only [if_neg hd,abs_mul,abs_of_nonneg (hw0 t),abs_div,abs_one,
            abs_of_nonneg (Nat.cast_nonneg d.totient)]
          ring
      _ ≤ ∑ t∈S,w t*((k:ℝ)*U) := sum_le_sum hrow
      _ = _ := by rw [←sum_mul,mul_comm] <;> rfl
  have hm : p5z_labelledMass S w≤(fibreBound+1)*(3*(N:ℝ)) :=
    (row_mass cs ν δ h c (by omega) hz hh hh' hc hc').trans
      (mul_le_mul_of_nonneg_right ((fibre_le hk).trans (le_add_of_nonneg_right zero_le_one)) (by positivity))
  have hkR : (k:ℝ)≤200 := by exact_mod_cast hk
  have hfull := mul_le_mul (mul_le_mul_of_nonneg_right hkR hU) hm
    (show 0≤p5z_labelledMass S w from sum_nonneg (fun t _ => hw0 t)) (mul_nonneg (by norm_num) hU)
  apply hfinite.trans (hfull.trans_eq ?_)
  dsimp only [U,A,cut]
  rw [rpow_sub hNp,rpow_one]
  field_simp [(rpow_pos_of_pos hNp (1/96:ℝ)).ne'] <;> ring

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRankArithmetic

