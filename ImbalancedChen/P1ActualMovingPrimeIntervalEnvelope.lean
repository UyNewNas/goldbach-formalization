import ImbalancedChen.P1OriginalFourthMovingPrimeIntervalBound

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

A quantitative exponent-window envelope uniform in both moving endpoints.
The pinned Euler interval theorem is stated for even targets. Above the
fixed lower prime cutoff 3, any target-deleted prime carrier embeds in the
fixed even target-2 carrier. Thus the upper envelope holds for all targets
without erasing their original deletion on the left. On a fixed positive
exponent box [a,b], the resulting bound is
(hi-lo)/a + b*K/(a^2*log N), uniformly for a<=lo<=hi<=b.
-/

namespace ImbalancedChen.P1ActualMovingPrimeIntervalEnvelope

noncomputable section
open scoped Classical BigOperators Topology
open Filter P1OriginalFourthMovingPrimeIntervalBound

def IntervalBound (K : ℝ) : Prop :=
  ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∑ p ∈ roughPrimeFinset N cap w z, 1/((p : ℝ)-1)) ≤
      Real.log z/Real.log w*(1+K/Real.log w)-1

/-- The original target-deleted carrier is retained, while a fixed even
target is used only as a positive upper carrier above the prime 2. -/
theorem reciprocal_interval_le_all_targets (K : ℝ) (hK : IntervalBound K)
    (N cap : ℕ) (w z : ℝ) (hw : 3 ≤ w) (hwz : w ≤ z) :
    (∑ p ∈ roughPrimeFinset N cap w z, 1/((p : ℝ)-1)) ≤
      Real.log z/Real.log w*(1+K/Real.log w)-1 := by
  have hsub : roughPrimeFinset N cap w z ⊆ roughPrimeFinset 2 cap w z := by
    intro p hp
    obtain ⟨hcap,hprime,hnot,hl,hu⟩ := mem_roughPrimeFinset.mp hp
    have hp2 : ¬p ∣ 2 := by
      intro hd
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hd
      have hpleR : (p : ℝ) ≤ 2 := by exact_mod_cast hple
      linarith
    exact mem_roughPrimeFinset.mpr ⟨hcap,hprime,hp2,hl,hu⟩
  have hsum :
      (∑ p ∈ roughPrimeFinset N cap w z, 1/((p : ℝ)-1)) ≤
      ∑ p ∈ roughPrimeFinset 2 cap w z, 1/((p : ℝ)-1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hnot
    have hprime := (mem_roughPrimeFinset.mp hp).2.1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
    exact (one_div_pos.mpr (sub_pos.mpr hp1)).le
  exact hsum.trans (hK 2 cap (by decide) w z (by linarith) hwz)

theorem actual_mass_le_exponent_terms (K : ℝ) (hKpos : 0 ≤ K) (hK : IntervalBound K)
    (N : ℕ) (hN : 1 < N) (a b lo hi : ℝ) (ha : 0 < a)
    (halo : a ≤ lo) (horder : lo ≤ hi) (hhib : hi ≤ b)
    (hA : 3 ≤ (N : ℝ)^a) :
    actualPrimeReciprocalMass N lo hi ≤
      (hi-lo)/a + b*K/(a^2*Real.log (N : ℝ)) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hlo : 0 < lo := ha.trans_le halo
  have hhi : 0 < hi := hlo.trans_le horder
  have hb : 0 < b := hhi.trans_le hhib
  have hlower : 3 ≤ (N : ℝ)^lo := hA.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le halo)
  have hwz := Real.rpow_le_rpow_of_exponent_le hn.le horder
  have hraw := reciprocal_interval_le_all_targets K hK N (Nat.ceil ((N : ℝ)^hi))
    ((N : ℝ)^lo) ((N : ℝ)^hi) hlower hwz
  have heq : Real.log ((N : ℝ)^hi)/Real.log ((N : ℝ)^lo)*
      (1+K/Real.log ((N : ℝ)^lo))-1 =
      (hi-lo)/lo + hi*K/(lo^2*Real.log (N : ℝ)) := by
    rw [Real.log_rpow hn0,Real.log_rpow hn0]
    field_simp [hlo.ne',hlog.ne']
    ring
  rw [heq] at hraw
  have hfirst : (hi-lo)/lo ≤ (hi-lo)/a :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr horder) ha halo
  have hnum : hi*K ≤ b*K := mul_le_mul_of_nonneg_right hhib hKpos
  have hsq : a^2 ≤ lo^2 := by nlinarith
  have hden : a^2*Real.log (N : ℝ) ≤ lo^2*Real.log (N : ℝ) :=
    mul_le_mul_of_nonneg_right hsq hlog.le
  have hsecond1 : hi*K/(lo^2*Real.log (N : ℝ)) ≤
      b*K/(lo^2*Real.log (N : ℝ)) :=
    div_le_div_of_nonneg_right hnum (by positivity)
  have hsecond2 : b*K/(lo^2*Real.log (N : ℝ)) ≤
      b*K/(a^2*Real.log (N : ℝ)) :=
    div_le_div_of_nonneg_left (mul_nonneg hb.le hKpos) (by positivity) hden
  exact hraw.trans (add_le_add hfirst (hsecond1.trans hsecond2))

/-- The endpoint-uniform constant is supplied by the pinned theorem. -/
theorem exists_uniform_exponent_window_envelope :
    ∃ K : ℝ, 1 < K ∧ ∀ (N : ℕ), 1 < N →
      ∀ a b lo hi : ℝ, 0 < a → a ≤ lo → lo ≤ hi → hi ≤ b →
        3 ≤ (N : ℝ)^a →
        actualPrimeReciprocalMass N lo hi ≤
          (hi-lo)/a + b*K/(a^2*Real.log (N : ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_reciprocal_interval_bound
  refine ⟨K,hK,?_⟩
  intro N hN a b lo hi ha halo horder hhib hA
  exact actual_mass_le_exponent_terms K (by linarith) hbound N hN
    a b lo hi ha halo horder hhib hA

end
end ImbalancedChen.P1ActualMovingPrimeIntervalEnvelope
