import ImbalancedChen.P4AOriginalNewFifthArchiveReader

/-! Original G3 block definitions, retaining their exact fixture paths and names. -/
namespace ImbalancedChen.P4AOriginalNewFifthArchiveData
open P4AOriginalNewFifthArchiveReader

def F0009 : Block := include_new_fifth_pair% "g3-fixtures/F0009-cells.npy" "g3-fixtures/F0009-floors.npy"
def F0010 : Block := include_new_fifth_pair% "g3-fixtures/F0010-cells.npy" "g3-fixtures/F0010-floors.npy"

end ImbalancedChen.P4AOriginalNewFifthArchiveData
