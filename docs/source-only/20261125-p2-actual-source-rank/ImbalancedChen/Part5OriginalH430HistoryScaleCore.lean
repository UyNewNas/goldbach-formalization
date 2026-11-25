import ImbalancedChen.Part5OriginalH430RequestedMember
import ImbalancedChen.Part5OriginalH430OriginalBandCore
import ImbalancedChen.P2EnhancedSwitchedTrueNormalization

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.
Mechanical relocation of original declarations from ImbalancedChen.Part5OriginalH430SeedHistoryMass.
Public namespace and declaration/proof text are preserved. The original
owner postimage imports this module and removes each moved declaration.
Private helpers, if present, acquire this module owner and need a fresh
complete owned audit. No compiler or kernel acceptance is asserted.
-/

namespace ImbalancedChen.Part5OriginalH430SeedHistoryMass

noncomputable section
open Set Real Finset
open P5OriginalActionMassBound P2EnhancedLowerPrimeChildCarriers
open P2EnhancedSwitchedTrueNormalization (trueAlpha prefixExponent)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers
open scoped Classical BigOperators

def wordProduct {N n p depth : ℕ} {k : Root} {t : ℝ}
    (l : LevelIndex N n k t p depth) : ℕ := parentProduct (levelOccurrence l).current.old

def wordLevel {N n p depth : ℕ} {k : Root} {t : ℝ}
    (l : LevelIndex N n k t p depth) : ℝ :=
  physicalLevel N (rootQ N n k t p) (levelOccurrence l).current.old

theorem scale_and_alpha {N n p dep : ℕ} {k : Root} {t : ℝ}
    (hN : 2≤N) (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hp : p ∈ originalBand N k) (l : LevelIndex N n k t p dep) :
    let Q := rootQ N n k t p
    let d := wordProduct l
    let L := wordLevel l
    0<d ∧ L∈Icc frozenResidualFloor 1 ∧ Q=(d:ℝ)*(N:ℝ)^L ∧
      (N:ℝ)^frozenResidualFloor ≤ Q/d ∧ 2≤trueAlpha N Q d := by
  let d := wordProduct l
  let Q := rootQ N n k t p
  let L := wordLevel l
  have h1 : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans h1
  have hs := rootHistory_support (by omega : 1<N) ht ht' hn
    (original_band_prime hp) (original_band_geometry hN hp) (levelOccurrence_source l).1
  have hd : 0<d := hs.1.2.1
  have hL : frozenResidualFloor ≤ L := hs.2.2.1
  have hL0 := frozenResidualFloor_pos.trans_le hL
  have hQ : Q=(d:ℝ)*(N:ℝ)^L := hs.2.2.2.2.2
  have hres : Q/(d:ℝ)=(N:ℝ)^L := by rw [hQ]; field_simp [(Nat.cast_pos.mpr hd).ne']
  have hβ : 0≤prefixExponent N d := div_nonneg
    (log_nonneg (by exact_mod_cast (show 1≤d by omega))) (log_pos h1).le
  have hα : 2≤(1-prefixExponent N d)/L := hs.2.2.2.2.1
  have htα : trueAlpha N Q d=(1-prefixExponent N d)/L := by
    rw [trueAlpha,P2EnhancedSwitchedTrueNormalization.physical_log (by omega : 1<N) hd,hres,
      log_rpow hN0,mul_comm L]
    exact mul_div_mul_left _ _ (log_pos h1).ne'
  refine ⟨hd,⟨hL,?_⟩,hQ,?_,hα.trans htα.ge⟩
  · linarith only [(le_div_iff₀ hL0).mp hα,hβ]
  · rw [hres]
    exact rpow_le_rpow_of_exponent_le h1.le hL

end
end ImbalancedChen.Part5OriginalH430SeedHistoryMass
