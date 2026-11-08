import ImbalancedChen.Part5OriginalH430ActualResolvedMarkedPushforward

/-!
P5.6 / h34: discharge the ACTUAL resolved marked-product positivity
and same-physical-Q level gates from the already-proved generated
root-history geometry.

The earlier genuine marked-product pushforward needs d > 0 and Q/d > 1
to invoke the installed Theta_pos. Those are not new assumptions here:
the existing rootHistory_support supplies the literal parentWindow,
the strictly positive frozen residual floor, and Q = d * N^L.
The source remains manuscript-internal, with the existing N, root,
precision, tau, p, selected request position and physical Q.

This establishes only the primitive marked-family gates. It does NOT
identify the original U3/U4 q/tag selected-count source with the
resolved-product family, nor assign any owner or pay the q minus 5 Phi
defect. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualResolvedPhysicalGates

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualResolvedMarkedPushforward
open P2EnhancedTwentyOneSameQWeighted

/-- Every genuine generated level occurrence has a strictly positive
original integer parent product. This uses the literal history window,
not an arbitrary positivity hypothesis on a synthetic marked family. -/
theorem actual_level_parent_product_pos
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 < parentProduct (levelOccurrence l).current.old := by
  have hs := rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1
  have hd : (1:ℝ) ≤
      (parentProduct (levelOccurrence l).current.old : ℝ) :=
    (parentWindow_logs hs.1).2.1
  exact_mod_cast (zero_lt_one.trans_le hd)

/-- The TRUE physical root Q divided by the actual integer product
is strictly above one at every real request-list position. The exact
same-Q factorisation and positive residual are derived from the
original history, not stipulated for the marked family. -/
theorem actual_level_quotient_gt_one
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    1 < rootQ N n root tau p /
      (parentProduct (levelOccurrence l).current.old : ℝ) := by
  let d : ℕ := parentProduct (levelOccurrence l).current.old
  let L : ℝ := physicalLevel N (rootQ N n root tau p)
    (levelOccurrence l).current.old
  have hs := rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1
  have hL : 0 < L := frozenResidualFloor_pos.trans_le hs.2.2.1
  have hd : (0:ℝ) < (d:ℝ) := by
    exact_mod_cast (actual_level_parent_product_pos N n root tau p g l
      hN ht ht' hn hp hband)
  have hbase : (1:ℝ) < (N:ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hpow : (1:ℝ) < (N:ℝ)^L := Real.one_lt_rpow hbase hL
  have hQ : rootQ N n root tau p = (d:ℝ) * (N:ℝ)^L :=
    hs.2.2.2.2.2
  change 1 < rootQ N n root tau p / (d:ℝ)
  calc
    rootQ N n root tau p / (d:ℝ) = (N:ℝ)^L := by
      rw [hQ]
      field_simp [ne_of_gt hd] <;> ring
    _ > 1 := hpow

/-- The previous exact resolved-product Phi/Theta pushforward has a
STRICTLY POSITIVE same-Q Theta whenever the genuine resolved level is
nonempty. No additional ad hoc positivity or Q/d premises remain:
both primitive gates follow from the actual root-history geometry.
The missing q/tag source coverage and selected-count payment remain
distinct internal obligations. -/
theorem activeProduct_Theta_pos_from_root_geometry
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hnonempty : (activePositions N n root tau p g).Nonempty) :
    0 < Theta N (rootQ N n root tau p)
      (activeProductSupport N n root tau p g)
      (activeProductSigma N n root tau p g) := by
  apply activeProduct_Theta_pos N n root tau p g hN hnonempty
  · intro l hl
    change 0 < parentProduct (levelOccurrence l).current.old
    exact actual_level_parent_product_pos N n root tau p g l
      hN ht ht' hn hp hband
  · intro l hl
    change 1 < rootQ N n root tau p /
      (parentProduct (levelOccurrence l).current.old : ℝ)
    exact actual_level_quotient_gt_one N n root tau p g l
      hN ht ht' hn hp hband

end
end ImbalancedChen.Part5OriginalH430ActualResolvedPhysicalGates
