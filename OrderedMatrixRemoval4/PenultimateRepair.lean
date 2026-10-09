import OrderedMatrixRemoval4.Host

/-!
A concrete depth-four obstruction to the proposed penultimate-negative-column
repair. Physical indices refer to the pinned release's independent host axes.
The repair covers the full class, with no restriction on node or clone.
-/
namespace OrderedMatrixRemoval4.Host.PenultimateRepair

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Exactly dummy rows crossed with negative variable columns at depth `h - 1`. -/
def repairCell (h : Nat) (r c : Fin (size h)) : Bool :=
  match labelAt false h r, labelAt true h c with
  | .dummy _, .variable depth false _ _ => decide (depth = h - 1)
  | _, _ => false

/-- Set the proposed class to zero; use the actual host everywhere else. -/
def repairedMatrix (h : Nat) : BinaryMatrix (size h) := fun r c =>
  if repairCell h r c then false else matrix h r c

def rows : Fin 4 → Fin (size 4) := fun i =>
  match i.val with
  | 0 => ⟨800, by decide⟩
  | 1 => ⟨802, by decide⟩
  | 2 => ⟨804, by decide⟩
  | _ => ⟨912, by decide⟩

def cols : Fin 4 → Fin (size 4) := fun i =>
  match i.val with
  | 0 => ⟨836, by decide⟩
  | 1 => ⟨864, by decide⟩
  | 2 => ⟨868, by decide⟩
  | _ => ⟨880, by decide⟩

def rowLabels : Fin 4 → Position := fun i =>
  match i.val with
  | 0 => .variable 3 true 0 0
  | 1 => .variable 3 false 1 0
  | 2 => .variable 4 true 2 0
  | _ => .dummy 0

def colLabels : Fin 4 → Position := fun i =>
  match i.val with
  | 0 => .variable 3 false 2 0
  | 1 => .variable 2 true 2 0
  | 2 => .variable 3 true 4 0
  | _ => .variable 2 false 2 0

theorem size_four : size 4 = 928 := by decide

/-- Kernel reduction audits the actual physical row descriptors. -/
theorem rows_labelAt : ∀ i, labelAt false 4 (rows i) = rowLabels i := by decide

/-- Kernel reduction audits the actual physical column descriptors. -/
theorem cols_labelAt : ∀ i, labelAt true 4 (cols i) = colLabels i := by decide

theorem rows_increasing : Increasing rows := by unfold Increasing; decide
theorem cols_increasing : Increasing cols := by unfold Increasing; decide

/-- Among the selected sixteen cells, exactly the bottom-left cell is targeted. -/
theorem selected_repair_cells (r c : Fin 4) :
    repairCell 4 (rows r) (cols c) = decide (r = 3 ∧ c = 0) := by
  simp only [repairCell, rows_labelAt, cols_labelAt]
  revert r c
  decide

/-- Before repair, the selected bottom row is `1111`. -/
theorem original_bottom_row : ∀ c, matrix 4 (rows 3) (cols c) = true := by
  intro c
  simp only [matrix, rows_labelAt, cols_labelAt]
  revert c
  decide

/-- After repair, all sixteen selected bits equal H4: 0110/1001/1010/0111. -/
theorem selected_matches : Matches H4 (repairedMatrix 4) rows cols := by
  intro r c
  simp only [repairedMatrix, selected_repair_cells, matrix, rows_labelAt, cols_labelAt]
  revert r c
  decide

theorem orderedCopy_depth4 : OrderedCopy H4 (repairedMatrix 4) rows cols :=
  ⟨rows_increasing, cols_increasing, selected_matches⟩

theorem not_hFree_depth4 : ¬ HFree H4 (repairedMatrix 4) := by
  intro hf
  exact hf rows cols orderedCopy_depth4

end OrderedMatrixRemoval4.Host.PenultimateRepair
