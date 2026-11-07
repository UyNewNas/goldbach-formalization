import ImbalancedChen.Part3OriginalFrozenReciprocalCauchy

/-!
Source only, uncompiled, zero formal credit.
The remaining inner restriction is made explicit on the original
(s1,h) image. Reconstruction proves multiplicity one in each frozen
outer fibre. This is not a declaration that its mask is removable.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028

namespace ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102

attribute [local instance] Classical.propDecidable

def inner (s : Source) : ℕ × ℤ := (s.2.1.u, s.1.h)

def rebuild (o : Outer) (st st' : ℕ × ℕ) (u : ℕ × ℤ) : Source :=
  ({ q := o.q, w1 := u.1*o.r1, w2 := o.s2*o.r2,
      n1 := o.n1, n2 := o.n2, h := u.2 },
    (⟨st.1, st.2, u.1, o.r1⟩, ⟨st'.1, st'.2, o.s2, o.r2⟩))

/-- This is the inverse map on the ORIGINAL source, not a new
parametrization whose equality with that source is a hypothesis. -/
theorem rebuild_outer_inner (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) {s : Source}
    (hs : s ∈ sourceCarrier B atom z y k small R Br Bs st st') :
    rebuild (outer B s) st st' (inner s) = s := by
  have hg := (Finset.mem_filter.mp hs).2
  have hp := hg.2.2.1
  have hp' := hg.2.2.2.1
  have hst := hg.2.2.2.2.1
  have hst' := hg.2.2.2.2.2
  rw [← hst, ← hst']
  rcases s with ⟨⟨q, w1, w2, n1, n2, h⟩, ⟨ps, pt, pu, pv⟩, ⟨ps', pt', pu', pv'⟩⟩
  dsimp only [rebuild, outer, inner, smoothTag] at *
  rw [hp, hp']

theorem inner_injOn_fibre (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (o : Outer) :
    Set.InjOn inner ↑((sourceCarrier B atom z y k small R Br Bs st st').filter
      (fun s => outer B s = o)) := by
  intro s hs s' hs' he
  have hs0 := (Finset.mem_filter.mp hs).1
  have hs0' := (Finset.mem_filter.mp hs').1
  have ho := (Finset.mem_filter.mp hs).2
  have ho' := (Finset.mem_filter.mp hs').2
  calc
    s = rebuild o st st' (inner s) := by
      rw [← ho]
      exact (rebuild_outer_inner B atom z y k small R Br Bs st st' hs0).symm
    _ = rebuild o st st' (inner s') := by rw [he]
    _ = s' := by
      rw [← ho']
      exact rebuild_outer_inner B atom z y k small R Br Bs st st' hs0'

def innerImage (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br Bs : ℕ) (st st' : ℕ × ℕ)
    (o : Outer) : Finset (ℕ × ℤ) :=
  ((sourceCarrier B atom z y k small R Br Bs st st').filter
    (fun s => outer B s = o)).image inner

def innerAtom (B : FixedBlock) (atom : MediumAtom) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) (u : ℕ × ℤ) : ℂ :=
  (lambdaS atom st st' e u.1 / (u.1 : ℂ)) *
    ActualReciprocalSquarePoissonSourceOnly.phase B.atom.residue o.f
      (packetB o) (packetC o) u

/-- Exact masked reciprocal row. Each (s1,h) occurs once; neither h sign
nor a source-dependent arithmetic mask has been dropped. -/
theorem row_eq_inner_image (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    row B atom z y k small R Br Bs st st' e o =
      ∑ u ∈ innerImage B atom z y k small R Br Bs st st' o,
        innerAtom B atom st st' e o u := by
  unfold innerImage
  rw [Finset.sum_image (inner_injOn_fibre B atom z y k small R Br Bs st st' o)]
  unfold row
  apply Finset.sum_congr rfl
  intro s hs
  have ho := (Finset.mem_filter.mp hs).2
  change innerAtom B atom st st' e (outer B s) (inner s) =
    innerAtom B atom st st' e o (inner s)
  rw [ho]

/-- Membership in the remaining mask has an exact, checkable source
description, including the redundant signed f label. -/
theorem mem_innerImage_iff (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (o : Outer) (u : ℕ × ℤ) :
    u ∈ innerImage B atom z y k small R Br Bs st st' o ↔
      rebuild o st st' u ∈ sourceCarrier B atom z y k small R Br Bs st st' ∧
        outer B (rebuild o st st' u) = o := by
  constructor
  · intro hu
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hu
    have hs0 := (Finset.mem_filter.mp hs).1
    have ho := (Finset.mem_filter.mp hs).2
    have hr : rebuild o st st' u = s := by
      rw [← he, ← ho]
      exact rebuild_outer_inner B atom z y k small R Br Bs st st' hs0
    rw [hr]
    exact ⟨hs0, ho⟩
  · rintro ⟨hs, ho⟩
    apply Finset.mem_image.mpr
    refine ⟨rebuild o st st' u, Finset.mem_filter.mpr ⟨hs, ho⟩, ?_⟩
    rfl

/-- All inverse gates needed by the literal reciprocal phase follow
from the original clean carrier. No (a,c)=1 premise is added. -/
theorem source_packet_inverse_licenses (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) {s : Source}
    (hs : s ∈ sourceCarrier B atom z y k small R Br Bs st st') :
    (packetB (outer B s)).Coprime (packetC (outer B s)) ∧
      s.2.1.u.Coprime (packetC (outer B s)) ∧
      s.2.1.u.Coprime B.atom.residue.natAbs := by
  have hm := Finset.mem_filter.mp hs
  have ht := (Finset.mem_filter.mp (Finset.mem_product.mp hm.1).1).1
  have hc := (Finset.mem_filter.mp ht).2
  have hp := hm.2.2.2.1
  have hp' := hm.2.2.2.2.1
  have hall : (s.1.n2*s.1.w1).Coprime (s.1.n1*s.1.w2) :=
    (E3_clean_inverse_licenses hc).2.2.of_dvd_left ⟨s.1.q*B.d, by ring⟩
  have hred : (packetB (outer B s)*s.2.1.u).Coprime (packetC (outer B s)) := by
    unfold packetB packetC outer
    dsimp only
    rw [← hp, ← hp'] at hall
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hall
  have hsplit := Nat.coprime_mul_iff_left.mp hred
  have hu : s.2.1.u ∣ s.1.w1 := by rw [← hp]; exact dvd_mul_right _ _
  have ha : s.2.1.u.Coprime B.atom.residue.natAbs :=
    (hc.2.1.of_dvd_left hu).of_dvd_right (dvd_mul_right _ _)
  exact ⟨hsplit.1, hsplit.2, ha⟩

/-- The S profile in the row is exactly H's frozen non-Hermitian
profile, and its bound comes from the original coefficient support. -/
theorem lambdaS_norm_le_one {b : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible b sigma kappa c0 atom)
    (st st' : ℕ × ℕ) (e : Fin 4) (s : ℕ) :
    ‖lambdaS atom st st' e s‖ ≤ 1 := by
  have hh := (actual_slots_one_bounded hA).1
  exact diagonal_norm_le_one _ _ e (hh st.1) (hh st'.1) s

end ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
