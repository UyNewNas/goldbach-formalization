import ImbalancedChen.P1OriginalSingletonProperPower
import ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData
import ImbalancedChen.P1Full87TrueDUnitBound

/-!
Proper-power deletion on the original true-d historical carrier.
The signed coefficient remains fresh minus old, zero-extended only by
each policy's own support. The original lower cutoff and strict .599
upper cutoff are both retained. No distribution estimate for the
remaining von Mangoldt term is assumed or concluded.
-/

namespace ImbalancedChen.P1OriginalHistoricalProperPower

noncomputable section

open Classical Filter
open scoped Topology
open P1Full87TrueDPolicyDelta P1Full87HistoricalMiddleSmoothing
open P1OriginalSingletonProperPower

/-- The exact VM comparison term for the original historical remainder. -/
def policyVonMangoldtRemaining (B kap : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℂ :=
  vonMangoldtRemaining kap 6 N
    (remainingModuli B N (trueDDeltaSupport old fresh N cap w z))
    (trueDDeltaRho old fresh N cap w z L)

/-- One threshold works for both actual histories, with their respective
old/fresh order and full physical coefficient. In particular, the
comparison uses old=S, fresh=R; the saving uses old=eight, fresh=six. -/
theorem eventually_policyRemaining_sub_vonMangoldt_singularNormalization
    (kap : ℝ) (hkap : kap < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (B : ℝ) (old fresh : List ℕ → Bool)
      (cap : ℕ) (w z L : ℝ),
      ‖(policyRemaining B kap old fresh N cap w z L : ℂ) -
        policyVonMangoldtRemaining B kap old fresh N cap w z L‖ ≤
        eta * singularNormalization N := by
  filter_upwards [eventually_original_singleton_prime_sub_vonMangoldt_singularNormalization
    kap hkap eta heta] with N hN
  intro B old fresh cap w z L
  unfold policyRemaining smoothRemaining policyVonMangoldtRemaining
  apply hN 6
  · intro q hq
    obtain ⟨hm, _, hupper⟩ := Finset.mem_filter.mp hq
    exact ⟨Nat.pos_of_ne_zero
      (trueDDeltaSupport_squarefree old fresh N cap w z hm).ne_zero, hupper⟩
  · intro q _
    exact P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one old fresh N cap q w z L

end
end ImbalancedChen.P1OriginalHistoricalProperPower
