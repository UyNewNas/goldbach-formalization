import ImbalancedChen.P2OriginalPositiveSameQMassLift
import ImbalancedChen.ChenPrimeHarmonicFinite

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ordinary W1 child window excludes divisors of d*N, whereas the O
prime-mass carrier excludes divisors of N.  This file pays only that
additional prefix deletion.  On a deleted lane the exact multiplier is
1/p, so the cost is bounded by C/A times the distinct-prime count of d.
The signed bounded test need not be continuous and may be chosen after
the threshold.  No old count licence or H247 estimate is an input.

This deletion is not imposed on the restored W2 mother windows, which
already use primeWindow N and intentionally retain repeated-prefix lanes.
-/
namespace ImbalancedChen.P2OriginalPrefixMaskMass

noncomputable section
open Filter Set Wu2008DoubleSieve
open P2OriginalChildPhysicalNormalization P2OriginalPositiveSameQMassLift
open scoped Classical BigOperators Topology

/-- The original mask difference is a literal finite filter, including
the lower endpoint and excluding the upper endpoint on both sides. -/
theorem primeWindow_prefixMask (N d : ℕ) (A U : ℝ) :
    primeWindow (d*N) A U = (primeWindow N A U).filter (fun p => ¬p ∣ d) := by
  ext p
  simp only [Finset.mem_filter,mem_primeWindow]
  constructor
  · rintro ⟨hp,hcop,hlo,hhi⟩
    obtain ⟨hpd,hpN⟩ := Nat.coprime_mul_iff_right.mp hcop
    exact ⟨⟨hp,hpN,hlo,hhi⟩,hp.coprime_iff_not_dvd.mp hpd⟩
  · rintro ⟨⟨hp,hpN,hlo,hhi⟩,hpd⟩
    exact ⟨hp,Nat.coprime_mul_iff_right.mpr
      ⟨hp.coprime_iff_not_dvd.mpr hpd,hpN⟩,hlo,hhi⟩

/-- Exact fresh/repeated arithmetic is retained.  Only the removed
lanes use p | d, and on those lanes localPrimeFactor d p = 1/p. -/
theorem primeWindow_prefixMask_difference_le {N d : ℕ} (hd : 0<d)
    {A U C : ℝ} (hA : 0<A) (hC : 0≤C) (f : ℕ → ℝ)
    (hf : ∀p∈primeWindow N A U,|f p|≤C) :
    |(∑p∈primeWindow (d*N) A U,localPrimeFactor d p*f p)-
      (∑p∈primeWindow N A U,localPrimeFactor d p*f p)| ≤
      (C/A)*(Real.log (d:ℝ)/Real.log 2) := by
  rw [primeWindow_prefixMask]
  apply chen_prime_centre_removal_bound hd (primeWindow N A U)
    (fun p => localPrimeFactor d p*f p) (div_nonneg hC hA.le)
  · intro p hp
    exact (mem_primeWindow.mp hp).1
  · intro p hp hpd
    have hpR : (0:ℝ)<p := Nat.cast_pos.mpr (mem_primeWindow.mp hp).1.pos
    have hAp : A≤(p:ℝ) := (mem_primeWindow.mp hp).2.2.1
    rw [localPrimeFactor,if_pos hpd,abs_mul,
      abs_of_pos (one_div_pos.mpr hpR)]
    calc
      (1/(p:ℝ))*|f p| ≤ (1/(p:ℝ))*C :=
        mul_le_mul_of_nonneg_left (hf p hp) (one_div_pos.mpr hpR).le
      _ = C/(p:ℝ) := by ring
      _ ≤ C/A := div_le_div_of_nonneg_left hC hA hAp

/-- A fixed positive exponent chooses the threshold before the prefix,
both real window endpoints and every signed bounded test.  The physical
prefix bound d≤N is essential here, rather than silently inferred for
the arbitrary prefixes admitted by O's unmasked mass theorem. -/
theorem compact_uniform_prefixMask_difference {a C epsilon : ℝ}
    (ha : 0<a) (hC : 0≤C) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,0<d → d≤N →
      ∀A U : ℝ,(N:ℝ)^a≤A → ∀f : ℕ → ℝ,
      (∀p∈primeWindow N A U,|f p|≤C) →
      |(∑p∈primeWindow (d*N) A U,localPrimeFactor d p*f p)-
        (∑p∈primeWindow N A U,localPrimeFactor d p*f p)| < epsilon := by
  have hlim : Tendsto (fun N : ℕ =>
      (C/(N:ℝ)^a)*(Real.log (N:ℝ)/Real.log 2)) atTop (𝓝 0) := by
    have hh := (tendsto_nat_log_pow_div_rpow 1 ha).const_mul (C/Real.log 2)
    simp only [pow_one,mul_zero] at hh
    convert hh using 1
    ext N
    ring
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds hepsilon))
  refine ⟨max 2 T,?_⟩
  intro N hN d hd hdN A U hfloor f hf
  have hNpos : 0<N := by omega
  have hpow : 0<(N:ℝ)^a := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hNpos) _
  have hA : 0<A := hpow.trans_le hfloor
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogd : 0≤Real.log (d:ℝ)/Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))) hlog2.le
  have hlogs : Real.log (d:ℝ)/Real.log 2≤Real.log (N:ℝ)/Real.log 2 :=
    div_le_div_of_nonneg_right
      (Real.log_le_log (Nat.cast_pos.mpr hd) (by exact_mod_cast hdN)) hlog2.le
  have hcoeff : C/A≤C/(N:ℝ)^a :=
    div_le_div_of_nonneg_left hC hpow hfloor
  exact (primeWindow_prefixMask_difference_le hd hA hC f hf).trans_lt
    ((mul_le_mul hcoeff hlogs hlogd (div_nonneg hC hpow.le)).trans_lt
      (hT N (by omega)))

/-- A common physical Q at most N supplies precisely the extra prefix
bound used above.  No bound on d is claimed from a mass estimate alone. -/
theorem prefix_le_target_of_commonQ {N d : ℕ} {Q : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hQ : Q≤(N:ℝ)) : d≤N := by
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hdQ : (d:ℝ)<Q := by
    simpa only [one_mul] using (lt_div_iff₀ hdR).mp hR
  exact_mod_cast hdQ.le.trans hQ

/-- Direct moving-residual API for all original W1 lower endpoints
(each is at least 1/5).  No limit or bound is assumed for the test. -/
theorem compact_uniform_moving_prefixMask_difference {Lmin C epsilon : ℝ}
    (hmin : 0<Lmin) (hC : 0≤C) (hepsilon : 0<epsilon) :
    ∃T : ℕ,∀N : ℕ,T≤N → ∀d : ℕ,0<d → d≤N →
      ∀L lo hi : ℝ,Lmin≤L → (1/5:ℝ)≤lo → ∀f : ℕ → ℝ,
      (∀p∈primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),|f p|≤C) →
      |(∑p∈primeWindow (d*N) ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
          localPrimeFactor d p*f p)-
        (∑p∈primeWindow N ((N:ℝ)^(L*lo)) ((N:ℝ)^(L*hi)),
          localPrimeFactor d p*f p)| < epsilon := by
  obtain ⟨T,hT⟩ := compact_uniform_prefixMask_difference
    (by positivity : 0<Lmin/5) hC hepsilon
  refine ⟨max 2 T,?_⟩
  intro N hN d hd hdN L lo hi hL hlo f hf
  have hexp : Lmin/5≤L*lo := by
    nlinarith [mul_nonneg (show 0≤L by linarith) (show 0≤lo-1/5 by linarith)]
  exact hT N (by omega) d hd hdN _ _
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1≤N by omega)) hexp) f hf

end
end ImbalancedChen.P2OriginalPrefixMaskMass
