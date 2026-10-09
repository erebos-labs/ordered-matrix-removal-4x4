import OrderedMatrixRemoval4.PenultimateRepair

open OrderedMatrixRemoval4 OrderedMatrixRemoval4.Host
open OrderedMatrixRemoval4.Host.PenultimateRepair
namespace IndependentDepth4
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

-- No premises: check the literal public semantics and witness independently.
example : ∀ r c : Fin 4, H4 r c =
    (#[#[false,true,true,false], #[true,false,false,true],
       #[true,false,true,false], #[false,true,true,true]][r.val]!)[c.val]! := by decide

theorem support_exact (h : Nat) (r c : Fin (size h)) :
    repairCell h r c = true ↔
      (∃ a, labelAt false h r = Position.dummy a) ∧
      (∃ p b, labelAt true h c = Position.variable (h - 1) false p b) := by
  cases hr : labelAt false h r <;> cases hc : labelAt true h c <;>
    simp_all [repairCell]
  case dummy.variable a depth plus p b =>
    cases plus <;> simp_all

theorem edits_exact (h : Nat) (r c : Fin (size h)) :
    repairedMatrix h r c ≠ matrix h r c ↔ repairCell h r c = true := by
  unfold repairedMatrix
  cases hr : labelAt false h r <;> cases hc : labelAt true h c <;>
    simp [repairCell, hr, hc, matrix, entry]

theorem literal_rows : (rows 0).val = 800 ∧ (rows 1).val = 802 ∧
    (rows 2).val = 804 ∧ (rows 3).val = 912 := by decide
theorem literal_cols : (cols 0).val = 836 ∧ (cols 1).val = 864 ∧
    (cols 2).val = 868 ∧ (cols 3).val = 880 := by decide

-- This rechecks the actual definitions by kernel reduction, without using
-- selected_matches, descriptor lemmas, or orderedCopy_depth4 as premises.
theorem independent_copy : OrderedCopy H4 (repairedMatrix 4) rows cols := by
  unfold OrderedCopy Increasing Matches
  decide

theorem independent_not_free : ¬ HFree H4 (repairedMatrix 4) := by
  intro hf
  exact hf rows cols independent_copy

#print OrderedMatrixRemoval4.H4
#print OrderedMatrixRemoval4.Increasing
#print OrderedMatrixRemoval4.Matches
#print OrderedMatrixRemoval4.OrderedCopy
#print OrderedMatrixRemoval4.HFree
#print OrderedMatrixRemoval4.Host.matrix
#print OrderedMatrixRemoval4.Host.PenultimateRepair.orderedCopy_depth4
#print OrderedMatrixRemoval4.Host.PenultimateRepair.not_hFree_depth4
#print axioms support_exact
#print axioms edits_exact
#print axioms independent_copy
#print axioms independent_not_free
end IndependentDepth4
