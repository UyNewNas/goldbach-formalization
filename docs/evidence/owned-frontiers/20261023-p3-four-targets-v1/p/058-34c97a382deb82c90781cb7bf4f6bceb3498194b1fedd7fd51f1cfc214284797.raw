import ImbalancedChen.Part3ActualP3FourBranch
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCEONLY / UNCOMPILED / HOLD.
Future import Part3ActualP3FourBranch depends on the exact a998 actual carrier.
This file adds finite fibres and pair-gate arithmetic licences only.
It does not prove or repeat the four-branch algebra.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualP3CYZFibresSourceOnly

open Classical Finset
open ImbalancedChen.Part3.ActualP3LabelledReindexSourceOnly
open ImbalancedChen.Part3.ActualP3FourBranchSourceOnly
open scoped BigOperators

/-- The actual signed f from the first original row's constructed gcd. -/
def packetF (l : Label) : ℤ :=
  let o := l.1
  let D := (o.2.1.1 * l.2.1.1).gcd (o.2.1.2.1 * o.2.1.2.2)
  let g := o.1.2.1.gcd o.1.2.2
  let d1 := CanonicalReciprocalData.supportedPart (o.1.2.1 / g) g
  let n1 := CanonicalReciprocalData.coprimePart (o.1.2.1 / g) g
  let n2 := o.1.2.2 / g
  ((d1 : ℤ) * n1 - n2) / (o.1.1 * D : ℕ)

/-- Signed branch frequency changes k and y; b,c,z are unchanged. -/
def branchK (l : Label) (e : Branch) : ℤ :=
  let o := l.1
  let D := (o.2.1.1 * l.2.1.1).gcd (o.2.1.2.1 * o.2.1.2.2)
  let q := D / o.2.1.1.gcd D
  let t := l.2.1.1 / q
  let t' := l.2.2.1 / q
  signedFrequency e.1 l.2.1.2 * (t' : ℤ) -
    signedFrequency e.2 l.2.2.2 * (t : ℤ)

def branchY (l : Label) (e : Branch) : ℤ := packetF l * branchK l e

def rowKey (l : Label) (e : Branch) : ℕ × ℤ × ℕ :=
  (packetC l, branchY l e, packetZ l)

/-- This filters original labels; it never images or deduplicates summands. -/
def rowFibre (d : MediumAtom) (Z : ℝ) (e : Branch) (j : ℕ × ℤ × ℕ) :
    Finset Label :=
  (carrier d Z).filter (fun l => rowKey l e = j)

/-- Exact regrouping for one fixed branch. Its original gates, resonance,
outer coefficient, complex amplitudes and full R*S*T stay inside each term. -/
theorem actual_branch_sum_eq_cyz_fibres (d : MediumAtom)
    (Z Ybeta Ysupport : ℝ) (resonant : Bool) (e : Branch) :
    (∑ l ∈ carrier d Z,
      guardedBranchTerm d Z Ybeta Ysupport resonant l e) =
      ∑ j ∈ (carrier d Z).image (fun l => rowKey l e),
        ∑ l ∈ rowFibre d Z e j,
          guardedBranchTerm d Z Ybeta Ysupport resonant l e := by
  simpa only [rowFibre] using
    (Finset.sum_fiberwise_of_maps_to
      (s := carrier d Z) (t := (carrier d Z).image (fun l => rowKey l e))
      (g := fun l => rowKey l e)
      (fun l hl => Finset.mem_image_of_mem (fun l => rowKey l e) hl)
      (fun l => guardedBranchTerm d Z Ybeta Ysupport resonant l e)).symm

/-- Units from BOTH original gates, not from a nonzero individual branch.
No claim is made that pairedGate implies the old original-product hactive.
Each fixed fibre receives c>0 and z-unit only when an actual allowed pair
witness is supplied; empty/mask-zero fibres do not manufacture such licences. -/
theorem actual_fibre_pair_gate_units (d : MediumAtom) (Z : ℝ)
    (hU : 1 ≤ d.U) (hQ1 : 1 ≤ d.Q1) (hQ2 : 1 ≤ d.Q2) (hQ3 : 1 ≤ d.Q3)
    (e : Branch) (c : ℕ) (y : ℤ) (z : ℕ)
    (l : Label) (hl : l ∈ rowFibre d Z e (c, y, z))
    (hgate : pairedGate l.1 l.2.1 l.2.2) :
    0 < c ∧ (packetB l).Coprime c ∧ z.Coprime c := by
  obtain ⟨hmem, hkey⟩ := Finset.mem_filter.mp hl
  have hunits :
      0 < packetC l ∧ (packetB l).Coprime (packetC l) ∧
        (packetZ l).Coprime (packetC l) := by
    rcases l with ⟨o, u, v⟩
    unfold carrier at hmem
    obtain ⟨ho, huv⟩ := Finset.mem_sigma.mp hmem
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
    have factor_pos {Q : ℝ} (hQ : 1 ≤ Q) {n : ℕ}
        (hn : n ∈ factorCarrier Q) : 0 < n := by
      have hlo := (Finset.mem_Icc.mp hn).1
      have hceil : 1 ≤ Nat.ceil Q := by exact_mod_cast hQ.trans (Nat.le_ceil Q)
      omega
    unfold MediumAtom.smallCoreSquaredOuterCarrier at ho
    dsimp only at ho
    obtain ⟨hpN, hTail⟩ := Finset.mem_product.mp ho
    have hpMem := (Finset.mem_product.mp (Finset.mem_filter.mp hpN).1).1
    have hNs := (Finset.mem_product.mp (Finset.mem_filter.mp hpN).1).2
    have hN1Mem := (Finset.mem_product.mp hNs).1
    have hN2Mem := (Finset.mem_product.mp hNs).2
    change o.1.2.1 ∈ factorCarrier d.U at hN1Mem
    change o.1.2.2 ∈ factorCarrier d.U at hN2Mem
    have hp : 0 < o.1.1 := factor_pos hQ1 (Finset.mem_filter.mp hpMem).1
    have hN1 : 0 < o.1.2.1 := factor_pos hU hN1Mem
    have hN2 : 0 < o.1.2.2 := factor_pos hU hN2Mem
    obtain ⟨t, ht, hImage⟩ := Finset.mem_biUnion.mp hTail
    obtain ⟨D, _hD, he⟩ := Finset.mem_image.mp hImage
    have heTail : t = o.2.1 := congrArg Prod.fst he
    rw [heTail] at ht
    have hr : 0 < o.2.1.1 := factor_pos hQ3 (Finset.mem_product.mp ht).1
    have hr' := factor_pos hQ3 (Finset.mem_product.mp (Finset.mem_product.mp ht).2).1
    have hs0 := factor_pos hQ2 (Finset.mem_product.mp (Finset.mem_product.mp ht).2).2
    have hw : 0 < o.2.1.2.1 * o.2.1.2.2 := Nat.mul_pos hr' hs0
    have hs : 0 < u.1 := factor_pos hQ2 (Finset.mem_product.mp hu).1
    have hs' : 0 < v.1 := factor_pos hQ2 (Finset.mem_product.mp hv).1
    dsimp only [pairedGate] at hgate
    have hdata := sharedGeneralD_paired_fourier hp hr hs hs' hw hN1 hN2
      hgate.1.2 hgate.2.2 (hgate.2.1.trans hgate.1.1.symm) d.residue u.2 v.2
    rcases hdata with ⟨_hK, _hA, hc, _hst, _hst', hb, _hroot,
      htA, htA', _hL, _hL', _hphase⟩
    dsimp only [packetC, packetB, packetZ]
    refine ⟨hc, hb, ?_⟩
    exact (htA.of_dvd_right (dvd_mul_left _ _)).mul_left
      (htA'.of_dvd_right (dvd_mul_left _ _))
  have hc : packetC l = c := congrArg Prod.fst hkey
  have hz : packetZ l = z := congrArg (fun j : ℕ × ℤ × ℕ => j.2.2) hkey
  simpa only [hc, hz] using hunits

end ImbalancedChen.Part3.ActualP3CYZFibresSourceOnly

/-!
CONSUMER INTERFACE, not a third proved theorem:
For fixed e and j=(c,y,z), let s=rowFibre d Z e j and b=packetB.
Use exactly the original resonance predicate AND pairedGate as mask.
Retain all outer coefficients, gamma/4 and signed Poisson amplitudes in amp;
the negative root phase stays in root, the WHOLE N1*K*z phase stays in slow;
the positive reciprocal T stays as fourier1((residue*y)*inv(b*z;c)/c).
A witness l0 in s satisfying pairedGate gives 0<c and z.Coprime c by
actual_fibre_pair_gate_units. Then NeZero c can be introduced from c>0.
For EVERY l in s satisfying mask, its pairedGate component supplies hb
by the same theorem. No unit obligation is imposed on mask-false labels.
This licenses physical_labelled_row_grouping with d=residue*y, hz and hb,
once the exact branch dictionary equality amp*root*slow*T is supplied
from the separately authored branch source / actual packet definition.
That termwise dictionary rewriting and consumer invocation are NOT proved here.

Without a pairedGate witness the mask is false on the whole finite fibre;
the complete masked sum is zero. This observation supplies no global hz,
and no Fourier consumer is to be invoked at c=0 just from an empty sum.
c=1 and y=0 are retained, all ZMod Fourier modes including zero retained.

ORIGINAL hactive remains EXACTLY the old original guarded row-product !=0.
It is never redefined as branch !=0. The original a998 hactive theorem remains
available. No hactive mask was added to branchRowTerm/guardedBranchTerm here.
If an integration chooses that extra mask it MUST prove the aggregate
four-branch zero/cancellation identity before discarding any contributions.
This file takes the safer direct BOTH-gates licence and changes no branch.

OPEN: exact termwise Fourier dictionary integration; no branch sum
commutation/aggregate original-sum theorem is claimed beyond the imported
branch source. No b interval, energy, common completed m interval/phase,
spectral (25), original c-level return, P3, filtered hUpper/K or main closure.
-/
