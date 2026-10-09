import OrderedMatrixRemoval4.PenultimateRepair

open OrderedMatrixRemoval4
open OrderedMatrixRemoval4.Host.PenultimateRepair

-- Check the public conclusion and its concrete witness without changing HFree.
example : OrderedCopy H4 (repairedMatrix 4) rows cols := orderedCopy_depth4
example : ¬ HFree H4 (repairedMatrix 4) := not_hFree_depth4

#print repairedMatrix
#print repairCell
#print rows
#print cols
#print axioms size_four
#print axioms rows_labelAt
#print axioms cols_labelAt
#print axioms rows_increasing
#print axioms cols_increasing
#print axioms selected_repair_cells
#print axioms original_bottom_row
#print axioms selected_matches
#print axioms orderedCopy_depth4
#print axioms not_hFree_depth4
