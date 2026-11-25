import ImbalancedChen.P4AOriginalNewFifthArchiveReader

/-! Original G3 block definitions, retaining their exact fixture paths and names. -/
namespace ImbalancedChen.P4AOriginalNewFifthArchiveData
open P4AOriginalNewFifthArchiveReader

def F0023 : Block := include_new_fifth_pair% "g3-fixtures/F0023-cells.npy" "g3-fixtures/F0023-floors.npy"

end ImbalancedChen.P4AOriginalNewFifthArchiveData
