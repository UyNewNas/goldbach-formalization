import ImbalancedChen.P2TwentyOneAllWordTailDecomposition
import ImbalancedChen.P2EnhancedTwentyOneChildCorrection

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bind the actual lower_tail same-Q correction's ENTIRE switchedCount to
the independently constructed original high-arity arithmetic source.
The five original cutoff queries are unchanged. The true good-tail
family and its original small-partner remainder are summed with the
original marked sigma. This is not a K/J/cost-integral estimate.
-/
namespace ImbalancedChen.P2ActualSameQTwentyOnePositiveSourceBinding
noncomputable section
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedTwentyOneChildCorrection (localSwitched switchedCount)
open P2TwentyOneUnsiftedArithmeticSource P2TwentyOneAllWordTailDecomposition

def actualLocalPrimeMass (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  switchedPrimeMass N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
    (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5))

def actualGoodMass (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ d ∈ D,sigma d*goodSwitchedPrimeMass N d N
    (cutoff Q d (227/50)) (cutoff Q d (353/100)) (cutoff Q d (29/10))
    (cutoff Q d (61/25)) (cutoff Q d (11/5)) z

def actualSmallPartnerMass (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∑ d ∈ D,sigma d*smallPartnerSwitchedMass N d N
    (cutoff Q d (227/50)) (cutoff Q d (353/100)) (cutoff Q d (29/10))
    (cutoff Q d (61/25)) (cutoff Q d (11/5)) z

theorem actual_local_source_identity {N d : ℕ} (Q : ℝ)
    (hN : 4≤N) (he : Even N) (hd : 0<d) :
    localSwitched N Q d=actualLocalPrimeMass N Q d := by
  exact quotientSwitched_eq_switchedPrimeMass hN he hd

/-- The existing count in the same-Q negative-child correction is the
actual independent all-word arithmetic prime count, including every
marked occurrence. No expected cost or analytic Sound field is assumed. -/
theorem actual_marked_source_identity {N : ℕ} (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hN : 4≤N) (he : Even N) (hd : ∀ d ∈ D,0<d) :
    switchedCount N Q D sigma=∑ d ∈ D,sigma d*actualLocalPrimeMass N Q d := by
  unfold switchedCount
  apply Finset.sum_congr rfl
  intro d hdD
  rw [actual_local_source_identity Q hN he (hd d hdD)]

/-- Original masked switched count costs an independent genuine
full-tail-floor family AND its explicit actual small-partner count.
All original five cutoff expressions and the same total Q are retained. -/
theorem actual_sameQ_good_source_bound {N z : ℕ} (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hN : 4≤N) (he : Even N) (hd : ∀ d ∈ D,0<d) (hsigma : ∀ d ∈ D,0≤sigma d)
    (hold : ∀ d ∈ D,∀ p : ℕ,p.Prime → p ∣ d → z≤p)
    (hcut : ∀ d ∈ D,(z : ℝ)≤cutoff Q d (227/50)) :
    switchedCount N Q D sigma≤actualGoodMass N Q D sigma z+actualSmallPartnerMass N Q D sigma z := by
  unfold switchedCount actualGoodMass actualSmallPartnerMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hdD
  have h := quotientSwitched_le_good_add_small
    (N:=N) (d:=d) (M:=N) (z:=z)
    (a:=cutoff Q d (227/50)) (b:=cutoff Q d (353/100))
    (c:=cutoff Q d (29/10)) (e:=cutoff Q d (61/25)) (f:=cutoff Q d (11/5))
    hN he (hd d hdD) (hcut d hdD) (hold d hdD)
  have hh := mul_le_mul_of_nonneg_left h (hsigma d hdD)
  simpa only [localSwitched,mul_add] using hh

end
end ImbalancedChen.P2ActualSameQTwentyOnePositiveSourceBinding
