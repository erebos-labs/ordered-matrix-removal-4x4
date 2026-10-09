import OrderedMatrixRemoval4.Repairs

open OrderedMatrixRemoval4 OrderedMatrixRemoval4.Host
open OrderedMatrixRemoval4.Host.TerminalAnchorRepair

-- Quantified statements on actual physical axes, with unrestricted alternatives.
example (h : Nat) (hh : 1 ≤ h) :
    HFree H4 (TerminalAnchorRepair.matrix h) ∧
    Host.editCount h (TerminalAnchorRepair.matrix h) = (2^h)^2 ∧
    ∀ B : BinaryMatrix (size h), HFree H4 B → (2^h)^2 ≤ Host.editCount h B :=
  exact_minimum h hh

example (h : Nat) (r c : Fin (size h)) :
    TerminalAnchorRepair.matrix h r c ≠ Host.matrix h r c ↔
    ∃ p a, labelAt false h r = .variable h true p 0 ∧
      labelAt true h c = .anchor h (4+p%2) 0 a := changed_iff_tags h r c

#print TerminalAnchorRepair.TerminalColumn
#print TerminalAnchorRepair.matrix
#print axioms third_row_nonanchor_of_anchor_agreement
#print axioms no_new_copy
#print axioms original_first_column_terminal
#print axioms free
#print axioms changed_iff_tags
#print axioms edit_count
#print axioms exact_minimum
