theorem actual_fifth_exponent_le_raw31
    (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (he : 0 ≤ e)
    (hs : supported (e : ℝ) chi m omega N (rosserAncestor 3 pre))
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 5 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hseed := actual_inherited_fourth_le_raw31 e chi m omega N
    rows4 licensed4 c pre hlen hc he hs hgeometry
  exact P2ActualFifthCandidateBelowSixthRaw31.exponent5_le_sixth_oldCap_of_inherited4_le
    e chi m omega N rows4 licensed4 J5 rows5 c pre hlen heR hc hseed

