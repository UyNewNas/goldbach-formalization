import ImbalancedChen.Part3SharedFirstFactorCharacterDictionary
import ImbalancedChen.Part3SmoothCoprimeError
import Mathlib.Tactic

/-!
SOURCE ONLY -- UNCOMPILED -- HOLD -- 2026-10-28.

This binds the paper's clean `ell,r,s` CRT zero mode to the *existing*
literal complex residue masses.  The original alpha, finite carrier,
and full coprime mean survive.  The first lemma identifies the paper's
totient coefficient on the clean set; the second transports the existing
finite centered covariance identity through the exact gcd of the two
moduli.  No large-sieve/BDH estimate or medium conclusion is assumed.

Paper: manuscript-body.tex 190--217; distribution-medium-completion-
20261010.txt 191--251, equations (11)--(15).
-/

namespace ImbalancedChen.Part3.OriginalMediumPrincipalFiniteCRT

noncomputable section

open Classical Finset
open scoped BigOperators
open TransposedZeroCovariance

def paperPrincipalCoefficient (ell r s : ℕ) : ℂ :=
  ((ell * r * s).totient : ℂ) /
    (((ell * r * s : ℕ) : ℂ) * ((ell * r).totient : ℂ) *
      ((ell * s).totient : ℂ))

/-- Multiplying by a factor already dividing the modulus multiplies its
totient by that same factor.  This is the exact prime-support step behind
the paper's `c_ell(r,s)` identity. -/
private theorem totient_mul_of_dvd_left
    {a n : ℕ} (ha : 0 < a) (han : a ∣ n) :
    (a * n).totient = a * n.totient := by
  have hg : a.gcd n = a := Nat.gcd_eq_left_iff_dvd.mpr han
  have h := Nat.totient_gcd_mul_totient_mul a n
  rw [hg] at h
  have hp : 0 < a.totient := Nat.totient_pos.mpr ha
  nlinarith

/-- The full-period arithmetic identity behind the coprime Gram
kernel, proved from the existing gcd/product totient identity. -/
private theorem totient_lcm_mul_totient_gcd
    {q t : ℕ} (hq : 0 < q) (ht : 0 < t) :
    (q.lcm t).totient * (q.gcd t).totient =
      q.totient * t.totient := by
  let g := q.gcd t
  let L := q.lcm t
  have hg : 0 < g := Nat.gcd_pos_of_pos_left t hq
  have hgd : g ∣ L :=
    (Nat.gcd_dvd_left q t).trans (Nat.dvd_lcm_left q t)
  have hprod : g * L = q * t := Nat.gcd_mul_lcm q t
  have htot : (q * t).totient = g * L.totient := by
    calc
      _ = (g * L).totient := by rw [hprod]
      _ = g * L.totient := totient_mul_of_dvd_left hg hgd
  have h := Nat.totient_gcd_mul_totient_mul q t
  change g.totient * (q * t).totient = q.totient * t.totient * g at h
  rw [htot] at h
  dsimp [g, L] at h ⊢
  nlinarith

/-- Exact full-period coprime count, including a translated positive
period endpoint.  This uses the already proved finite Mobius divisor
identity; no asymptotic coprime counting estimate enters. -/
private theorem coprimePrefix_multiple
    (n k : ℕ) (hn : 0 < n) :
    coprimePrefix (n * k) n = (k : ℝ) * (n.totient : ℝ) := by
  rw [coprimePrefix_eq_divisor_sum (n * k) hn.ne']
  calc
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (((n * k) / d : ℕ) : ℝ)) =
      (k : ℝ) * ∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdp : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      have hdiv : (n * k) / d = (n / d) * k := by
        calc
          (n * k) / d = ((d * (n / d)) * k) / d := by
            rw [Nat.mul_div_cancel' hdn]
          _ = (d * ((n / d) * k)) / d := by rw [mul_assoc]
          _ = (n / d) * k := Nat.mul_div_cancel_left _ hdp
      rw [hdiv]
      push_cast
      ring
    _ = (k : ℝ) * (n.totient : ℝ) := by
      rw [← coprimePrefix_eq_divisor_sum n hn.ne', coprimePrefix_period]

/-- The exact paper coefficient equals the lcm/gcd CRT density.  No
pairwise coprimality of `ell,r,s` is used. -/
theorem paper_coefficient_eq_lcm_density
    {ell r s : ℕ} (hell : 0 < ell) (hr : 0 < r) (hs : 0 < s) :
    paperPrincipalCoefficient ell r s =
      1 / ((((ell * r).lcm (ell * s) : ℕ) : ℂ) *
        (((ell * r).gcd (ell * s)).totient : ℂ)) := by
  let q := ell * r
  let t := ell * s
  have hq : q ≠ 0 := (mul_pos hell hr).ne'
  have ht : t ≠ 0 := (mul_pos hell hs).ne'
  have hn : ell * r * s ≠ 0 :=
    mul_ne_zero (mul_ne_zero hell.ne' hr.ne') hs.ne'
  have hprod : q * t = ell * (ell * r * s) := by
    dsimp [q, t]
    ring
  have hdvd : ell ∣ ell * r * s := ⟨r * s, by ring⟩
  have htot : (q * t).totient = ell * (ell * r * s).totient := by
    rw [hprod, totient_mul_of_dvd_left hell hdvd]
  have he : (ell : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hell.ne'
  have hnC : ((ell * r * s : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hqphi : (q.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  have htphi : (t.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ht)).ne'
  have hratio : paperPrincipalCoefficient ell r s =
      ((q * t).totient : ℂ) /
        ((q.totient : ℂ) * (t.totient : ℂ) * ((q * t : ℕ) : ℂ)) := by
    unfold paperPrincipalCoefficient
    rw [htot, hprod]
    dsimp [q, t]
    push_cast
    field_simp [he, hnC, hqphi, htphi]
    ring
  rw [hratio]
  exact totient_pair_density_eq_lcm hq ht

/-- The clean CRT normalization is exact even when `r` shares primes
with `ell`; only `s` is required coprime to `ell`. -/
theorem clean_paper_coefficient
    {ell r s : ℕ} (hell : 0 < ell) (hr : 0 < r) (hs : 0 < s)
    (hrs : r.Coprime s) (hsell : s.Coprime ell) :
    ((ell.totient : ℂ) * paperPrincipalCoefficient ell r s) =
      1 / (((ell * r * s : ℕ) : ℂ)) := by
  have hsr : (ell * r).Coprime s := hsell.symm.mul_left hrs
  have hphi1 : ((ell * r * s).totient : ℂ) =
      ((ell * r).totient : ℂ) * (s.totient : ℂ) := by
    exact_mod_cast Nat.totient_mul hsr
  have hphi2 : ((ell * s).totient : ℂ) =
      (ell.totient : ℂ) * (s.totient : ℂ) := by
    exact_mod_cast Nat.totient_mul hsell.symm
  have htotal : (((ell * r * s : ℕ) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (mul_ne_zero (mul_ne_zero hell.ne' hr.ne') hs.ne')
  have hphier : ((ell * r).totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.totient_pos.mpr (mul_pos hell hr)).ne'
  have hphie : (ell.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hell).ne'
  have hphis : (s.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hs).ne'
  unfold paperPrincipalCoefficient
  rw [hphi1, hphi2]
  field_simp [htotal, hphier, hphie, hphis]
  ring

/-- The literal paper masses at `ell*r` and `ell*s` center over exactly
the unit residue classes modulo `ell` on a clean pair.  In particular,
the full coprime means are not replaced by unrestricted means. -/
theorem clean_centered_crt_variance
    (N : Finset ℕ) (alpha : ℕ → ℂ)
    {ell r s : ℕ} (hell : 0 < ell) (hr : 0 < r)
    (hrs : r.Coprime s) :
    compatibleMass N alpha (ell * r) (ell * s) -
      coprimeMass N alpha (ell * r) *
        star (coprimeMass N alpha (ell * s)) / (ell.totient : ℂ) =
      ∑ b ∈ reducedResidues ell,
        (residueMass N alpha (ell * r) ell b -
          coprimeMass N alpha (ell * r) / (ell.totient : ℂ)) *
        star (residueMass N alpha (ell * s) ell b -
          coprimeMass N alpha (ell * s) / (ell.totient : ℂ)) := by
  have hg : (ell * r).gcd (ell * s) = ell := by
    rw [Nat.gcd_mul_left, hrs.gcd_eq_one, mul_one]
  have hq : 0 < ell * r := mul_pos hell hr
  simpa only [hg, covariance] using
    (covariance_identity N alpha (q := ell * r) (r := ell * s) hq)

/-- The centered row has zero residue sum, with the actual auxiliary
coprimality mask inside `residueMass`. -/
theorem centered_row_sum_zero
    (N : Finset ℕ) (alpha : ℕ → ℂ)
    {ell r : ℕ} (hell : 0 < ell) :
    (∑ b ∈ reducedResidues ell,
      (residueMass N alpha (ell * r) ell b -
        coprimeMass N alpha (ell * r) / (ell.totient : ℂ))) = 0 := by
  have hphi : (ell.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hell).ne'
  have hmass := sum_residueMass N alpha hell (dvd_mul_right ell r)
  rw [Finset.sum_sub_distrib, hmass, Finset.sum_const, nsmul_eq_mul,
    card_reducedResidues]
  field_simp [hphi]

/-- The finite unit-class feature used by the paper's principal kernel.
The arbitrary common period is deliberately a parameter, never an error
scale. -/
def principalFeature (ell r v : ℕ) : ℂ :=
  if v.Coprime (ell * r) then
    1 / ((ell * r).totient : ℂ)
  else 0

def principalGramKernel (L ell r s : ℕ) : ℂ :=
  ∑ v ∈ Ioc 0 L,
    principalFeature ell r v * star (principalFeature ell s v)

private theorem coprime_lcm_iff (v q t : ℕ) :
    v.Coprime (q.lcm t) ↔ v.Coprime q ∧ v.Coprime t := by
  constructor
  · intro h
    exact ⟨h.of_dvd_right (Nat.dvd_lcm_left q t),
      h.of_dvd_right (Nat.dvd_lcm_right q t)⟩
  · rintro ⟨hq, ht⟩
    exact (hq.mul_right ht).of_dvd_right (Nat.lcm_dvd_mul q t)

/-- This is equation (11) with an arbitrary positive common period,
not a pair-dependent period and not an asymptotic approximation. -/
theorem principal_kernel_eq_paper_coefficient
    {L ell r s : ℕ} (hell : 0 < ell) (hr : 0 < r) (hs : 0 < s)
    (hLr : ell * r ∣ L) (hLs : ell * s ∣ L) :
    principalGramKernel L ell r s =
      (L : ℂ) * paperPrincipalCoefficient ell r s := by
  let q := ell * r
  let t := ell * s
  let n := q.lcm t
  let g := q.gcd t
  have hq : 0 < q := mul_pos hell hr
  have ht : 0 < t := mul_pos hell hs
  have hn : 0 < n := Nat.lcm_pos hq ht
  have hg : 0 < g := Nat.gcd_pos_of_pos_left t hq
  have hnd : n ∣ L := Nat.lcm_dvd hLr hLs
  have hL : n * (L / n) = L := Nat.mul_div_cancel' hnd
  have hcount : coprimePrefix L n =
      ((L / n : ℕ) : ℝ) * (n.totient : ℝ) := by
    conv_lhs => rw [← hL]
    exact coprimePrefix_multiple n (L / n) hn
  have hphi : n.totient * g.totient = q.totient * t.totient :=
    totient_lcm_mul_totient_gcd hq ht
  have hpair (v : ℕ) :
      principalFeature ell r v * star (principalFeature ell s v) =
        if v.Coprime n then
          (1 / (q.totient : ℂ)) * (1 / (t.totient : ℂ)) else 0 := by
    have hc := coprime_lcm_iff v q t
    by_cases hvq : v.Coprime q <;> by_cases hvt : v.Coprime t <;>
      simp [principalFeature, q, t, n, hc, hvq, hvt]
  have hsum : principalGramKernel L ell r s =
      ((coprimePrefix L n : ℝ) : ℂ) *
        ((1 / (q.totient : ℂ)) * (1 / (t.totient : ℂ))) := by
    unfold principalGramKernel
    simp_rw [hpair]
    calc
      (∑ v ∈ Ioc 0 L,
        if v.Coprime n then
          (1 / (q.totient : ℂ)) * (1 / (t.totient : ℂ)) else 0) =
          (∑ v ∈ Ioc 0 L, if v.Coprime n then (1 : ℂ) else 0) *
            ((1 / (q.totient : ℂ)) * (1 / (t.totient : ℂ))) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v.Coprime n <;> simp [hv]
      _ = _ := by
        congr 1
        unfold coprimePrefix
        push_cast
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v.Coprime n <;> simp [hv]
  rw [hsum, hcount, paper_coefficient_eq_lcm_density hell hr hs]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hgC : (g.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hg).ne'
  have hphiC : (n.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hn).ne'
  have hqC : (q.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq).ne'
  have htC : (t.totient : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr ht).ne'
  have hLcast : (L : ℂ) = (n : ℂ) * ((L / n : ℕ) : ℂ) := by
    exact_mod_cast hL.symm
  have hphiCast : (n.totient : ℂ) * (g.totient : ℂ) =
      (q.totient : ℂ) * (t.totient : ℂ) := by exact_mod_cast hphi
  push_cast
  change (((L / n : ℕ) : ℂ) * (n.totient : ℂ)) *
      ((1 / (q.totient : ℂ)) * (1 / (t.totient : ℂ))) =
      (L : ℂ) * (1 / ((n : ℂ) * (g.totient : ℂ)))
  rw [hLcast]
  field_simp [hnC, hgC, hphiC, hqC, htC]
  linear_combination (((L / n : ℕ) : ℂ) * (n : ℂ)) * hphiCast

def principalGramEnergy (L ell : ℕ) (R : Finset ℕ)
    (coeff : ℕ → ℂ) : ℝ :=
  ∑ v ∈ Ioc 0 L,
    ‖∑ r ∈ R, coeff r * principalFeature ell r v‖ ^ 2

/-- This is the actual finite Gram expansion, with the paper's coprime
feature and arbitrary complex coefficient row.  The normalization by
the positive common period is applied only after this identity. -/
theorem principal_gram_expansion
    (L ell : ℕ) (R : Finset ℕ) (coeff : ℕ → ℂ) :
    ((principalGramEnergy L ell R coeff : ℝ) : ℂ) =
      ∑ r ∈ R, ∑ s ∈ R,
        coeff r * star (coeff s) * principalGramKernel L ell r s := by
  unfold principalGramEnergy principalGramKernel
  rw [Complex.ofReal_sum]
  simp_rw [complex_norm_sq_sum_eq_double_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  simp only [star_mul]
  ring

theorem principal_gram_energy_nonneg
    (L ell : ℕ) (R : Finset ℕ) (coeff : ℕ → ℂ) :
    0 ≤ principalGramEnergy L ell R coeff := by
  unfold principalGramEnergy
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The *paper coefficient itself*, not merely an abstract Gram kernel,
is positive semidefinite on the actual finite rough-factor carrier. -/
theorem paper_principal_quadratic_nonneg
    {L ell : ℕ} (hL : 0 < L) (hell : 0 < ell)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 0 < r)
    (hcommon : ∀ r ∈ R, ell * r ∣ L)
    (coeff : ℕ → ℂ) :
    0 ≤ (∑ r ∈ R, ∑ s ∈ R,
      coeff r * star (coeff s) * paperPrincipalCoefficient ell r s).re := by
  let E := principalGramEnergy L ell R coeff
  let Q : ℂ := ∑ r ∈ R, ∑ s ∈ R,
    coeff r * star (coeff s) * paperPrincipalCoefficient ell r s
  have hidentity : (E : ℂ) = (L : ℂ) * Q := by
    dsimp [E]
    rw [principal_gram_expansion]
    dsimp [Q]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [principal_kernel_eq_paper_coefficient hell (hR r hr) (hR s hs)
      (hcommon r hr) (hcommon s hs)]
    ring
  have hLC : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hQ : Q = (E : ℂ) / (L : ℂ) := by
    apply (eq_div_iff hLC).mpr
    rw [hidentity]
    ring
  rw [show (∑ r ∈ R, ∑ s ∈ R,
      coeff r * star (coeff s) * paperPrincipalCoefficient ell r s) = Q from rfl,
    hQ]
  have hreal : ((E : ℂ) / (L : ℂ)).re = E / (L : ℝ) := by
    rw [← Complex.ofReal_div]
    rfl
  rw [hreal]
  exact div_nonneg (principal_gram_energy_nonneg L ell R coeff) (Nat.cast_nonneg _)

def centeredPaperRow (N : Finset ℕ) (alpha : ℕ → ℂ)
    (ell r b : ℕ) : ℂ :=
  residueMass N alpha (ell * r) ell b -
    coprimeMass N alpha (ell * r) / (ell.totient : ℂ)

def paperPrincipalVariance
    (N : Finset ℕ) (alpha : ℕ → ℂ) (ell : ℕ)
    (R : Finset ℕ) (eta : ℕ → ℂ) : ℝ :=
  ∑ b ∈ reducedResidues ell,
    (∑ r ∈ R, ∑ s ∈ R,
      (eta r * centeredPaperRow N alpha ell r b) *
        star (eta s * centeredPaperRow N alpha ell s b) *
          paperPrincipalCoefficient ell r s).re

theorem paper_principal_variance_nonneg
    (N : Finset ℕ) (alpha : ℕ → ℂ)
    {L ell : ℕ} (hL : 0 < L) (hell : 0 < ell)
    (R : Finset ℕ) (hR : ∀ r ∈ R, 0 < r)
    (hcommon : ∀ r ∈ R, ell * r ∣ L)
    (eta : ℕ → ℂ) :
    0 ≤ paperPrincipalVariance N alpha ell R eta := by
  unfold paperPrincipalVariance
  exact Finset.sum_nonneg (fun b _ =>
    paper_principal_quadratic_nonneg hL hell R hR hcommon
      (fun r => eta r * centeredPaperRow N alpha ell r b))

/-- The positive remainder after the principal S1/S2/S3 cancellation
is a finite Gram energy on each reduced `ell` class.  This definition
retains the exact centered row rather than replacing it by a masked
principal mass. -/
def centeredPrincipalGramEnergy
    (N : Finset ℕ) (alpha : ℕ → ℂ) (L ell : ℕ)
    (R : Finset ℕ) (eta : ℕ → ℂ) : ℝ :=
  ∑ b ∈ reducedResidues ell,
    principalGramEnergy L ell R
      (fun r => eta r * centeredPaperRow N alpha ell r b)

theorem centered_principal_gram_nonneg
    (N : Finset ℕ) (alpha : ℕ → ℂ) (L ell : ℕ)
    (R : Finset ℕ) (eta : ℕ → ℂ) :
    0 ≤ centeredPrincipalGramEnergy N alpha L ell R eta := by
  unfold centeredPrincipalGramEnergy
  exact Finset.sum_nonneg (fun _ _ => principal_gram_energy_nonneg L ell R _)

end

end ImbalancedChen.Part3.OriginalMediumPrincipalFiniteCRT
