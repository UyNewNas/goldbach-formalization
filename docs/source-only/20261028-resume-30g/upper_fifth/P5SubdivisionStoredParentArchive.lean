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

/-- Full source positional alignment. This finite source is unexecuted. -/
theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = j.val := by
  decide

end ImbalancedChen.P5SubdivisionStoredParentArchive
