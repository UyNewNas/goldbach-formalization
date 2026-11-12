import ImbalancedChen.Part5OriginalH430ClassicalRootCredits
import ImbalancedChen.Part5OriginalH430SeedHistoryMass
import ImbalancedChen.P2EnhancedShortWordUnitBound
import ImbalancedChen.P2EnhancedExactExceptionTheta

/-! The original external U3 modulus persists in every causal word.
On the classical branch it gives an absolute saving at the third power
of the residual level, including all inherited and scalar requests. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalCausalSeedScale
noncomputable section
open Finset Real Wu2008DoubleSieve
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430RootIntervalTheta (clampLevel)
open Part5OriginalH430ClassicalRootCredits (classical_Q_exact)
open Part5OriginalH430TaggedArithmeticReceivers (original_band_prime)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedSwitchedTrueNormalization (prefixExponent residualExponent trueAlpha trueAlpha_eq)
open P2EnhancedSwitchedUnsiftedSource (labels)
open P2EnhancedShortWordUnitBound (label_product_cap)
open P2SeedOmegaLiteralFibre (b)
open scoped Classical BigOperators

private theorem replay_keeps_modulus {N p : ℕ} (r : Request) (es : List (Edge N))
    (hp : p∈r.old) : p∈(replay r es).old := by
  induction es generalizing r with
  | nil => exact hp
  | cons e es ih => exact ih (nextRequest r e) (List.mem_append.mpr (Or.inl hp))

theorem root_modulus_mem {N n p dep : ℕ} {τ : ℝ}
    (l : LevelIndex N n .U3 τ p dep) : p∈(levelOccurrence l).current.old := by
  have h := (history_facts (levelOccurrence_source l).1).2.2
  rw [h]
  exact replay_keeps_modulus _ _ (List.mem_singleton.mpr rfl)

theorem root_modulus_dvd {N n p dep : ℕ} {τ : ℝ}
    (l : LevelIndex N n .U3 τ p dep) : p ∣ wordProduct l :=
  List.dvd_prod (root_modulus_mem l)

def smallProduct (N : ℕ) (κ : ℝ) : ℝ := (N:ℝ)^(1-κ)

/-- The margin 1/112 comes from 2(57/224)-1/2. It is independent
of the precision, reserve, path, positive mark and positive leaf mass. -/
theorem actual_cubic_residual {N n p dep : ℕ} {τ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) :
    let Q := rootQ N n .U3 τ p
    let d := wordProduct l
    0<d ∧ 1<Q/(d:ℝ) ∧ (N:ℝ)^frozenResidualFloor≤Q/d ∧
      3<trueAlpha N Q d ∧ (d:ℝ)*(Q/d)^(3:ℝ)≤smallProduct N (1/112) := by
  let d := wordProduct l
  let ν := clampLevel n τ
  let T := prefixExponent N d
  let L := ν-T
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  obtain ⟨hd,_,_,hscale,_⟩ := scale_and_alpha hN ht ht' hn (mem_filter.mp hp).1 l
  have hdr : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hpp := (original_band_prime (mem_filter.mp hp).1).1.pos
  have hpd : p≤d := Nat.le_of_dvd hd (root_modulus_dvd l)
  have hT : (57/224:ℝ)≤T := by
    have htail := (mem_filter.mp hp).2
    change 57/224 ≤ physicalPrime N p at htail
    exact htail.trans (div_le_div_of_nonneg_right
      (log_le_log (Nat.cast_pos.mpr hpp) (by exact_mod_cast hpd)) hlog.le)
  have hnu : ν≤1/2 :=
    (frozenLevel_bounds (show 1/2-τ∈Set.Icc (0:ℝ) 1 from ⟨by linarith,by linarith⟩) n).1.trans
      (by linarith)
  have hrepr : (N:ℝ)^T=(d:ℝ) := by
    apply (Real.mul_log_eq_log_iff hN0 hdr).mp
    exact div_mul_cancel₀ _ hlog.ne'
  have hres : rootQ N n .U3 τ p/(d:ℝ)=(N:ℝ)^L := by
    rw [classical_Q_exact hp,←hrepr,←rpow_sub hN0]
  have hR : 1<rootQ N n .U3 τ p/(d:ℝ) :=
    (one_lt_rpow hNr frozenResidualFloor_pos).trans_le hscale
  have hL : 0<L := by
    have h := hR
    rw [hres,←rpow_zero (N:ℝ)] at h
    exact (rpow_lt_rpow_left_iff hNr).mp h
  have hmargin : T+3*L≤1-1/112 := by dsimp [L]; linarith only [hT,hnu]
  refine ⟨hd,hR,hscale,?_,?_⟩
  · rw [classical_Q_exact hp,trueAlpha_eq (by omega : 1<N) hd]
    change (3:ℝ)<(1-T)/L
    exact (lt_div_iff₀ hL).mpr (by linarith only [hmargin])
  · change (d:ℝ)*(rootQ N n .U3 τ p/(d:ℝ))^(3:ℝ)≤_
    rw [hres,←rpow_mul hN0.le,←hrepr,←rpow_add hN0]
    exact rpow_le_rpow_of_exponent_le hNr.le (by linarith only [hmargin])

/-- The individual rough tail is allowed all the way to R^(3-r b).
In a triple this is R^(18/11). At r=6 it still includes the unit. -/
theorem low_tail_on_original_word {N n p dep m : ℕ} {τ κ : ℝ}
    (hN : 2≤N) (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p∈classicalBand N) (l : LevelIndex N n .U3 τ p dep)
    {cs qs : List ℕ} (hqs : qs∈labels N (rootQ N n .U3 τ p) (wordProduct l) cs)
    (hk : κ≤1/112)
    (hm : (m:ℝ)≤(rootQ N n .U3 τ p/(wordProduct l:ℝ))^(3-b*(cs.length:ℝ))) :
    ((wordProduct l*qs.prod*m:ℕ):ℝ)≤smallProduct N κ := by
  obtain ⟨hd,hR,_,_,hcap⟩ := actual_cubic_residual hN ht ht' hn hp l
  let R := rootQ N n .U3 τ p/(wordProduct l:ℝ)
  have hR0 : 0<R := zero_lt_one.trans hR
  have hprod := mul_le_mul (label_product_cap hR hqs) hm (Nat.cast_nonneg m)
    (rpow_nonneg hR0.le _)
  have he : R^(b*(cs.length:ℝ))*R^(3-b*(cs.length:ℝ))=R^(3:ℝ) := by
    rw [←rpow_add hR0]; congr 1 <;> ring
  change (qs.prod:ℝ)*(m:ℝ)≤R^(b*(cs.length:ℝ))*R^(3-b*(cs.length:ℝ)) at hprod
  rw [he] at hprod
  calc
    _ = (wordProduct l:ℝ)*((qs.prod:ℝ)*(m:ℝ)) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ ≤ smallProduct N (1/112) := hcap
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega))
      (by linarith only [hk])

theorem every_original_unit_low {N n p dep : ℕ} {τ κ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) (j : Fin 13) {cs qs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hqs : qs∈labels N (rootQ N n .U3 τ p) (wordProduct l) cs) (hk : κ≤1/112) :
    ((wordProduct l*qs.prod:ℕ):ℝ)≤smallProduct N κ := by
  have hr := (actual_cubic_residual hN ht ht' hn hp l).2.1
  have hlen := P2EnhancedExactExceptionTheta.original_word_arity (by omega) (by omega) hc
  have hlen' : (cs.length:ℝ)≤6 := by exact_mod_cast hlen
  have hx : 0≤3-b*(cs.length:ℝ) := by unfold b; linarith only [hlen']
  have hh := low_tail_on_original_word (m:=1) hN ht ht' hn hp l hqs hk
    (by simpa only [Nat.cast_one] using one_le_rpow hr.le hx)
  simpa only [Nat.mul_one] using hh

end
end ImbalancedChen.Part5OriginalH430ClassicalCausalSeedScale
