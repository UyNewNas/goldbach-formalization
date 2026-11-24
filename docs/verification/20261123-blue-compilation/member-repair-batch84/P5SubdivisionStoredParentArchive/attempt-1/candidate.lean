import ImbalancedChen.Data.P5SubdivisionStoredBlock000
import ImbalancedChen.Data.P5SubdivisionStoredBlock001
import ImbalancedChen.Data.P5SubdivisionStoredBlock002
import ImbalancedChen.Data.P5SubdivisionStoredBlock003
import ImbalancedChen.Data.P5SubdivisionStoredBlock004
import ImbalancedChen.Data.P5SubdivisionStoredBlock005
import ImbalancedChen.Data.P5SubdivisionStoredBlock006
import ImbalancedChen.Data.P5SubdivisionStoredBlock007
import ImbalancedChen.Data.P5SubdivisionStoredBlock008
import ImbalancedChen.Data.P5SubdivisionStoredBlock009
import ImbalancedChen.Data.P5SubdivisionStoredBlock010
import ImbalancedChen.Data.P5SubdivisionStoredBlock011
import ImbalancedChen.Data.P5SubdivisionStoredBlock012
import ImbalancedChen.Data.P5SubdivisionStoredBlock013
import ImbalancedChen.Data.P5SubdivisionStoredBlock014
import ImbalancedChen.Data.P5SubdivisionStoredBlock015
import ImbalancedChen.Data.P5SubdivisionStoredBlock016
import ImbalancedChen.Data.P5SubdivisionStoredBlock017
import ImbalancedChen.Data.P5SubdivisionStoredBlock018
import ImbalancedChen.Data.P5SubdivisionStoredBlock019
import ImbalancedChen.Data.P5SubdivisionStoredBlock020
import ImbalancedChen.Data.P5SubdivisionStoredBlock021
import ImbalancedChen.Data.P5SubdivisionStoredBlock022
import ImbalancedChen.Data.P5SubdivisionStoredBlock023
import ImbalancedChen.Data.P5SubdivisionStoredBlock024
import ImbalancedChen.Data.P5SubdivisionStoredBlock025
import ImbalancedChen.Data.P5SubdivisionStoredBlock026
import ImbalancedChen.Data.P5SubdivisionStoredBlock027
import ImbalancedChen.Data.P5SubdivisionStoredBlock028
import ImbalancedChen.Data.P5SubdivisionStoredBlock029
import ImbalancedChen.Data.P5SubdivisionStoredBlock030
import ImbalancedChen.Data.P5SubdivisionStoredBlock031
import ImbalancedChen.Data.P5SubdivisionStoredBlock032
import ImbalancedChen.Data.P5SubdivisionStoredBlock033
import ImbalancedChen.Data.P5SubdivisionStoredBlock034
import ImbalancedChen.Data.P5SubdivisionStoredBlock035
import ImbalancedChen.Data.P5SubdivisionStoredBlock036
import ImbalancedChen.Data.P5SubdivisionStoredBlock037
import ImbalancedChen.Data.P5SubdivisionStoredBlock038
import ImbalancedChen.Data.P5SubdivisionStoredBlock039
import ImbalancedChen.Data.P5SubdivisionStoredBlock040
import ImbalancedChen.Data.P5SubdivisionStoredBlock041
import ImbalancedChen.Data.P5SubdivisionStoredBlock042
import ImbalancedChen.Data.P5SubdivisionStoredBlock043
import ImbalancedChen.Data.P5SubdivisionStoredBlock044
import ImbalancedChen.Data.P5SubdivisionStoredBlock045
import ImbalancedChen.Data.P5SubdivisionStoredBlock046
import ImbalancedChen.Data.P5SubdivisionStoredBlock047
import ImbalancedChen.Data.P5SubdivisionStoredBlock048
import ImbalancedChen.Data.P5SubdivisionStoredBlock049
import ImbalancedChen.Data.P5SubdivisionStoredBlock050
import ImbalancedChen.Data.P5SubdivisionStoredBlock051
import ImbalancedChen.Data.P5SubdivisionStoredBlock052
import ImbalancedChen.Data.P5SubdivisionStoredBlock053
import ImbalancedChen.Data.P5SubdivisionStoredBlock054
import ImbalancedChen.Data.P5SubdivisionStoredBlock055
import ImbalancedChen.Data.P5SubdivisionStoredBlock056
import ImbalancedChen.Data.P5SubdivisionStoredBlock057
import ImbalancedChen.Data.P5SubdivisionStoredBlock058
import ImbalancedChen.Data.P5SubdivisionStoredBlock059
import ImbalancedChen.Data.P5SubdivisionStoredBlock060
import ImbalancedChen.Data.P5SubdivisionStoredBlock061
import ImbalancedChen.Data.P5SubdivisionStoredBlock062
import ImbalancedChen.Data.P5SubdivisionStoredBlock063
import ImbalancedChen.Data.P5SubdivisionStoredBlock064
import ImbalancedChen.Data.P5SubdivisionStoredBlock065
import ImbalancedChen.Data.P5SubdivisionStoredBlock066
import ImbalancedChen.Data.P5SubdivisionStoredBlock067
import ImbalancedChen.Data.P5SubdivisionStoredBlock068
import ImbalancedChen.Data.P5SubdivisionStoredBlock069
import ImbalancedChen.Data.P5SubdivisionStoredBlock070
import ImbalancedChen.Data.P5SubdivisionStoredBlock071

/-! All72 checkpoint blocks in original block/row order. The literals are
not deduplicated, reordered by value, or recomputed. Binary-to-Lean
extraction authenticity remains independently reviewable. -/
namespace ImbalancedChen.P5SubdivisionStoredParentArchive
open P5SubdivisionStoredParentTypes

def rows : Array StoredParent :=
  Data.P5SubdivisionStoredBlock000.rows ++ Data.P5SubdivisionStoredBlock001.rows ++ Data.P5SubdivisionStoredBlock002.rows ++ Data.P5SubdivisionStoredBlock003.rows ++ Data.P5SubdivisionStoredBlock004.rows ++ Data.P5SubdivisionStoredBlock005.rows ++ Data.P5SubdivisionStoredBlock006.rows ++ Data.P5SubdivisionStoredBlock007.rows ++ Data.P5SubdivisionStoredBlock008.rows ++ Data.P5SubdivisionStoredBlock009.rows ++ Data.P5SubdivisionStoredBlock010.rows ++ Data.P5SubdivisionStoredBlock011.rows ++ Data.P5SubdivisionStoredBlock012.rows ++ Data.P5SubdivisionStoredBlock013.rows ++ Data.P5SubdivisionStoredBlock014.rows ++ Data.P5SubdivisionStoredBlock015.rows ++ Data.P5SubdivisionStoredBlock016.rows ++ Data.P5SubdivisionStoredBlock017.rows ++ Data.P5SubdivisionStoredBlock018.rows ++ Data.P5SubdivisionStoredBlock019.rows ++ Data.P5SubdivisionStoredBlock020.rows ++ Data.P5SubdivisionStoredBlock021.rows ++ Data.P5SubdivisionStoredBlock022.rows ++ Data.P5SubdivisionStoredBlock023.rows ++ Data.P5SubdivisionStoredBlock024.rows ++ Data.P5SubdivisionStoredBlock025.rows ++ Data.P5SubdivisionStoredBlock026.rows ++ Data.P5SubdivisionStoredBlock027.rows ++ Data.P5SubdivisionStoredBlock028.rows ++ Data.P5SubdivisionStoredBlock029.rows ++ Data.P5SubdivisionStoredBlock030.rows ++ Data.P5SubdivisionStoredBlock031.rows ++ Data.P5SubdivisionStoredBlock032.rows ++ Data.P5SubdivisionStoredBlock033.rows ++ Data.P5SubdivisionStoredBlock034.rows ++ Data.P5SubdivisionStoredBlock035.rows ++ Data.P5SubdivisionStoredBlock036.rows ++ Data.P5SubdivisionStoredBlock037.rows ++ Data.P5SubdivisionStoredBlock038.rows ++ Data.P5SubdivisionStoredBlock039.rows ++ Data.P5SubdivisionStoredBlock040.rows ++ Data.P5SubdivisionStoredBlock041.rows ++ Data.P5SubdivisionStoredBlock042.rows ++ Data.P5SubdivisionStoredBlock043.rows ++ Data.P5SubdivisionStoredBlock044.rows ++ Data.P5SubdivisionStoredBlock045.rows ++ Data.P5SubdivisionStoredBlock046.rows ++ Data.P5SubdivisionStoredBlock047.rows ++ Data.P5SubdivisionStoredBlock048.rows ++ Data.P5SubdivisionStoredBlock049.rows ++ Data.P5SubdivisionStoredBlock050.rows ++ Data.P5SubdivisionStoredBlock051.rows ++ Data.P5SubdivisionStoredBlock052.rows ++ Data.P5SubdivisionStoredBlock053.rows ++ Data.P5SubdivisionStoredBlock054.rows ++ Data.P5SubdivisionStoredBlock055.rows ++ Data.P5SubdivisionStoredBlock056.rows ++ Data.P5SubdivisionStoredBlock057.rows ++ Data.P5SubdivisionStoredBlock058.rows ++ Data.P5SubdivisionStoredBlock059.rows ++ Data.P5SubdivisionStoredBlock060.rows ++ Data.P5SubdivisionStoredBlock061.rows ++ Data.P5SubdivisionStoredBlock062.rows ++ Data.P5SubdivisionStoredBlock063.rows ++ Data.P5SubdivisionStoredBlock064.rows ++ Data.P5SubdivisionStoredBlock065.rows ++ Data.P5SubdivisionStoredBlock066.rows ++ Data.P5SubdivisionStoredBlock067.rows ++ Data.P5SubdivisionStoredBlock068.rows ++ Data.P5SubdivisionStoredBlock069.rows ++ Data.P5SubdivisionStoredBlock070.rows ++ Data.P5SubdivisionStoredBlock071.rows

theorem rows_size : rows.size = 292633 := by
  simp only [rows, Array.size_append, Data.P5SubdivisionStoredBlock000.rows_size, Data.P5SubdivisionStoredBlock001.rows_size, Data.P5SubdivisionStoredBlock002.rows_size, Data.P5SubdivisionStoredBlock003.rows_size, Data.P5SubdivisionStoredBlock004.rows_size, Data.P5SubdivisionStoredBlock005.rows_size, Data.P5SubdivisionStoredBlock006.rows_size, Data.P5SubdivisionStoredBlock007.rows_size, Data.P5SubdivisionStoredBlock008.rows_size, Data.P5SubdivisionStoredBlock009.rows_size, Data.P5SubdivisionStoredBlock010.rows_size, Data.P5SubdivisionStoredBlock011.rows_size, Data.P5SubdivisionStoredBlock012.rows_size, Data.P5SubdivisionStoredBlock013.rows_size, Data.P5SubdivisionStoredBlock014.rows_size, Data.P5SubdivisionStoredBlock015.rows_size, Data.P5SubdivisionStoredBlock016.rows_size, Data.P5SubdivisionStoredBlock017.rows_size, Data.P5SubdivisionStoredBlock018.rows_size, Data.P5SubdivisionStoredBlock019.rows_size, Data.P5SubdivisionStoredBlock020.rows_size, Data.P5SubdivisionStoredBlock021.rows_size, Data.P5SubdivisionStoredBlock022.rows_size, Data.P5SubdivisionStoredBlock023.rows_size, Data.P5SubdivisionStoredBlock024.rows_size, Data.P5SubdivisionStoredBlock025.rows_size, Data.P5SubdivisionStoredBlock026.rows_size, Data.P5SubdivisionStoredBlock027.rows_size, Data.P5SubdivisionStoredBlock028.rows_size, Data.P5SubdivisionStoredBlock029.rows_size, Data.P5SubdivisionStoredBlock030.rows_size, Data.P5SubdivisionStoredBlock031.rows_size, Data.P5SubdivisionStoredBlock032.rows_size, Data.P5SubdivisionStoredBlock033.rows_size, Data.P5SubdivisionStoredBlock034.rows_size, Data.P5SubdivisionStoredBlock035.rows_size, Data.P5SubdivisionStoredBlock036.rows_size, Data.P5SubdivisionStoredBlock037.rows_size, Data.P5SubdivisionStoredBlock038.rows_size, Data.P5SubdivisionStoredBlock039.rows_size, Data.P5SubdivisionStoredBlock040.rows_size, Data.P5SubdivisionStoredBlock041.rows_size, Data.P5SubdivisionStoredBlock042.rows_size, Data.P5SubdivisionStoredBlock043.rows_size, Data.P5SubdivisionStoredBlock044.rows_size, Data.P5SubdivisionStoredBlock045.rows_size, Data.P5SubdivisionStoredBlock046.rows_size, Data.P5SubdivisionStoredBlock047.rows_size, Data.P5SubdivisionStoredBlock048.rows_size, Data.P5SubdivisionStoredBlock049.rows_size, Data.P5SubdivisionStoredBlock050.rows_size, Data.P5SubdivisionStoredBlock051.rows_size, Data.P5SubdivisionStoredBlock052.rows_size, Data.P5SubdivisionStoredBlock053.rows_size, Data.P5SubdivisionStoredBlock054.rows_size, Data.P5SubdivisionStoredBlock055.rows_size, Data.P5SubdivisionStoredBlock056.rows_size, Data.P5SubdivisionStoredBlock057.rows_size, Data.P5SubdivisionStoredBlock058.rows_size, Data.P5SubdivisionStoredBlock059.rows_size, Data.P5SubdivisionStoredBlock060.rows_size, Data.P5SubdivisionStoredBlock061.rows_size, Data.P5SubdivisionStoredBlock062.rows_size, Data.P5SubdivisionStoredBlock063.rows_size, Data.P5SubdivisionStoredBlock064.rows_size, Data.P5SubdivisionStoredBlock065.rows_size, Data.P5SubdivisionStoredBlock066.rows_size, Data.P5SubdivisionStoredBlock067.rows_size, Data.P5SubdivisionStoredBlock068.rows_size, Data.P5SubdivisionStoredBlock069.rows_size, Data.P5SubdivisionStoredBlock070.rows_size, Data.P5SubdivisionStoredBlock071.rows_size]

private theorem append_source_index
    {xs ys : Array StoredParent} {start n m : ℕ}
    (hx : xs.size = n ∧ ∀ j : Fin xs.size, (xs[j.val]).sourceIndex = start + j.val)
    (hy : ys.size = m ∧ ∀ j : Fin ys.size, (ys[j.val]).sourceIndex = start + n + j.val) :
    (xs ++ ys).size = n + m ∧
      ∀ j : Fin (xs ++ ys).size, ((xs ++ ys)[j.val]).sourceIndex = start + j.val := by
  refine ⟨by rw [Array.size_append, hx.1, hy.1], ?_⟩
  intro j
  by_cases hj : j.val < xs.size
  · rw [Array.getElem_append_left hj]
    exact hx.2 ⟨j.val, hj⟩
  · have hle : xs.size ≤ j.val := Nat.le_of_not_lt hj
    have hlt : j.val - xs.size < ys.size := by
      have hbound := j.isLt
      rw [Array.size_append] at hbound
      omega
    rw [Array.getElem_append_right hle]
    have hind : (ys[j.val - xs.size]).sourceIndex = start + n + (j.val - xs.size) :=
      hy.2 ⟨j.val - xs.size, hlt⟩
    rw [hind]
    have hsize : xs.size = n := hx.1
    omega

/-- Full source positional alignment. This finite source is unexecuted. -/
theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = j.val := by
  have h000 : Data.P5SubdivisionStoredBlock000.rows.size = 4096 ∧
      ∀ j : Fin Data.P5SubdivisionStoredBlock000.rows.size,
        (Data.P5SubdivisionStoredBlock000.rows[j.val]).sourceIndex = 0 + j.val :=
    ⟨Data.P5SubdivisionStoredBlock000.rows_size, Data.P5SubdivisionStoredBlock000.source_index_at⟩
  have h001 := append_source_index h000
    ⟨Data.P5SubdivisionStoredBlock001.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock001.source_index_at⟩
  have h002 := append_source_index h001
    ⟨Data.P5SubdivisionStoredBlock002.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock002.source_index_at⟩
  have h003 := append_source_index h002
    ⟨Data.P5SubdivisionStoredBlock003.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock003.source_index_at⟩
  have h004 := append_source_index h003
    ⟨Data.P5SubdivisionStoredBlock004.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock004.source_index_at⟩
  have h005 := append_source_index h004
    ⟨Data.P5SubdivisionStoredBlock005.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock005.source_index_at⟩
  have h006 := append_source_index h005
    ⟨Data.P5SubdivisionStoredBlock006.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock006.source_index_at⟩
  have h007 := append_source_index h006
    ⟨Data.P5SubdivisionStoredBlock007.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock007.source_index_at⟩
  have h008 := append_source_index h007
    ⟨Data.P5SubdivisionStoredBlock008.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock008.source_index_at⟩
  have h009 := append_source_index h008
    ⟨Data.P5SubdivisionStoredBlock009.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock009.source_index_at⟩
  have h010 := append_source_index h009
    ⟨Data.P5SubdivisionStoredBlock010.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock010.source_index_at⟩
  have h011 := append_source_index h010
    ⟨Data.P5SubdivisionStoredBlock011.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock011.source_index_at⟩
  have h012 := append_source_index h011
    ⟨Data.P5SubdivisionStoredBlock012.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock012.source_index_at⟩
  have h013 := append_source_index h012
    ⟨Data.P5SubdivisionStoredBlock013.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock013.source_index_at⟩
  have h014 := append_source_index h013
    ⟨Data.P5SubdivisionStoredBlock014.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock014.source_index_at⟩
  have h015 := append_source_index h014
    ⟨Data.P5SubdivisionStoredBlock015.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock015.source_index_at⟩
  have h016 := append_source_index h015
    ⟨Data.P5SubdivisionStoredBlock016.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock016.source_index_at⟩
  have h017 := append_source_index h016
    ⟨Data.P5SubdivisionStoredBlock017.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock017.source_index_at⟩
  have h018 := append_source_index h017
    ⟨Data.P5SubdivisionStoredBlock018.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock018.source_index_at⟩
  have h019 := append_source_index h018
    ⟨Data.P5SubdivisionStoredBlock019.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock019.source_index_at⟩
  have h020 := append_source_index h019
    ⟨Data.P5SubdivisionStoredBlock020.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock020.source_index_at⟩
  have h021 := append_source_index h020
    ⟨Data.P5SubdivisionStoredBlock021.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock021.source_index_at⟩
  have h022 := append_source_index h021
    ⟨Data.P5SubdivisionStoredBlock022.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock022.source_index_at⟩
  have h023 := append_source_index h022
    ⟨Data.P5SubdivisionStoredBlock023.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock023.source_index_at⟩
  have h024 := append_source_index h023
    ⟨Data.P5SubdivisionStoredBlock024.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock024.source_index_at⟩
  have h025 := append_source_index h024
    ⟨Data.P5SubdivisionStoredBlock025.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock025.source_index_at⟩
  have h026 := append_source_index h025
    ⟨Data.P5SubdivisionStoredBlock026.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock026.source_index_at⟩
  have h027 := append_source_index h026
    ⟨Data.P5SubdivisionStoredBlock027.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock027.source_index_at⟩
  have h028 := append_source_index h027
    ⟨Data.P5SubdivisionStoredBlock028.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock028.source_index_at⟩
  have h029 := append_source_index h028
    ⟨Data.P5SubdivisionStoredBlock029.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock029.source_index_at⟩
  have h030 := append_source_index h029
    ⟨Data.P5SubdivisionStoredBlock030.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock030.source_index_at⟩
  have h031 := append_source_index h030
    ⟨Data.P5SubdivisionStoredBlock031.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock031.source_index_at⟩
  have h032 := append_source_index h031
    ⟨Data.P5SubdivisionStoredBlock032.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock032.source_index_at⟩
  have h033 := append_source_index h032
    ⟨Data.P5SubdivisionStoredBlock033.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock033.source_index_at⟩
  have h034 := append_source_index h033
    ⟨Data.P5SubdivisionStoredBlock034.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock034.source_index_at⟩
  have h035 := append_source_index h034
    ⟨Data.P5SubdivisionStoredBlock035.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock035.source_index_at⟩
  have h036 := append_source_index h035
    ⟨Data.P5SubdivisionStoredBlock036.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock036.source_index_at⟩
  have h037 := append_source_index h036
    ⟨Data.P5SubdivisionStoredBlock037.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock037.source_index_at⟩
  have h038 := append_source_index h037
    ⟨Data.P5SubdivisionStoredBlock038.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock038.source_index_at⟩
  have h039 := append_source_index h038
    ⟨Data.P5SubdivisionStoredBlock039.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock039.source_index_at⟩
  have h040 := append_source_index h039
    ⟨Data.P5SubdivisionStoredBlock040.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock040.source_index_at⟩
  have h041 := append_source_index h040
    ⟨Data.P5SubdivisionStoredBlock041.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock041.source_index_at⟩
  have h042 := append_source_index h041
    ⟨Data.P5SubdivisionStoredBlock042.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock042.source_index_at⟩
  have h043 := append_source_index h042
    ⟨Data.P5SubdivisionStoredBlock043.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock043.source_index_at⟩
  have h044 := append_source_index h043
    ⟨Data.P5SubdivisionStoredBlock044.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock044.source_index_at⟩
  have h045 := append_source_index h044
    ⟨Data.P5SubdivisionStoredBlock045.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock045.source_index_at⟩
  have h046 := append_source_index h045
    ⟨Data.P5SubdivisionStoredBlock046.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock046.source_index_at⟩
  have h047 := append_source_index h046
    ⟨Data.P5SubdivisionStoredBlock047.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock047.source_index_at⟩
  have h048 := append_source_index h047
    ⟨Data.P5SubdivisionStoredBlock048.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock048.source_index_at⟩
  have h049 := append_source_index h048
    ⟨Data.P5SubdivisionStoredBlock049.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock049.source_index_at⟩
  have h050 := append_source_index h049
    ⟨Data.P5SubdivisionStoredBlock050.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock050.source_index_at⟩
  have h051 := append_source_index h050
    ⟨Data.P5SubdivisionStoredBlock051.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock051.source_index_at⟩
  have h052 := append_source_index h051
    ⟨Data.P5SubdivisionStoredBlock052.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock052.source_index_at⟩
  have h053 := append_source_index h052
    ⟨Data.P5SubdivisionStoredBlock053.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock053.source_index_at⟩
  have h054 := append_source_index h053
    ⟨Data.P5SubdivisionStoredBlock054.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock054.source_index_at⟩
  have h055 := append_source_index h054
    ⟨Data.P5SubdivisionStoredBlock055.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock055.source_index_at⟩
  have h056 := append_source_index h055
    ⟨Data.P5SubdivisionStoredBlock056.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock056.source_index_at⟩
  have h057 := append_source_index h056
    ⟨Data.P5SubdivisionStoredBlock057.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock057.source_index_at⟩
  have h058 := append_source_index h057
    ⟨Data.P5SubdivisionStoredBlock058.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock058.source_index_at⟩
  have h059 := append_source_index h058
    ⟨Data.P5SubdivisionStoredBlock059.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock059.source_index_at⟩
  have h060 := append_source_index h059
    ⟨Data.P5SubdivisionStoredBlock060.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock060.source_index_at⟩
  have h061 := append_source_index h060
    ⟨Data.P5SubdivisionStoredBlock061.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock061.source_index_at⟩
  have h062 := append_source_index h061
    ⟨Data.P5SubdivisionStoredBlock062.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock062.source_index_at⟩
  have h063 := append_source_index h062
    ⟨Data.P5SubdivisionStoredBlock063.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock063.source_index_at⟩
  have h064 := append_source_index h063
    ⟨Data.P5SubdivisionStoredBlock064.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock064.source_index_at⟩
  have h065 := append_source_index h064
    ⟨Data.P5SubdivisionStoredBlock065.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock065.source_index_at⟩
  have h066 := append_source_index h065
    ⟨Data.P5SubdivisionStoredBlock066.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock066.source_index_at⟩
  have h067 := append_source_index h066
    ⟨Data.P5SubdivisionStoredBlock067.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock067.source_index_at⟩
  have h068 := append_source_index h067
    ⟨Data.P5SubdivisionStoredBlock068.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock068.source_index_at⟩
  have h069 := append_source_index h068
    ⟨Data.P5SubdivisionStoredBlock069.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock069.source_index_at⟩
  have h070 := append_source_index h069
    ⟨Data.P5SubdivisionStoredBlock070.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock070.source_index_at⟩
  have h071 := append_source_index h070
    ⟨Data.P5SubdivisionStoredBlock071.rows_size, by
      simpa only [Nat.reduceAdd] using Data.P5SubdivisionStoredBlock071.source_index_at⟩
  simpa only [rows, Nat.zero_add] using h071.2

end ImbalancedChen.P5SubdivisionStoredParentArchive
