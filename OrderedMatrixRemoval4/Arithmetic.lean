import Lean

/-!
Unbounded arithmetic obligations used by the ordinary proof. No claim that
these alone prove classification or localization of embeddings in the host.
The actual host/order/incidence reduction remains to be formalized.
-/

namespace OrderedMatrixRemoval4

theorem nonterminal_siblings (p q b : Nat) (hpq : p < q)
    (hqb : q / 2 ≤ b) (hbp : b ≤ p / 2) :
    p = 2 * b ∧ q = 2 * b + 1 := by
  omega

theorem equal_parity_parent_order (p q : Nat)
    (hparity : p % 2 = q % 2) (hparent : p / 2 ≤ q / 2) : p ≤ q := by
  omega

theorem terminal_parent_equal (p q b : Nat) (hpq : p ≤ q)
    (hqb : q / 2 ≤ b) (hbp : b ≤ p / 2) :
    p / 2 = b ∧ q / 2 = b := by
  omega

/-- Flattened mode/group order: six modes per level, then two groups. -/
def anchorRank (level kind group : Nat) : Nat :=
  2 * (6 * level + kind) + group

/-- The inherited order puts W-minus parity 1 after parity 0. -/
theorem minus_one_cannot_precede_minus_zero (level : Nat) :
    ¬ anchorRank level 5 0 < anchorRank level 4 1 := by
  unfold anchorRank
  omega

theorem next_level_anchor_cannot_precede (level next kind group : Nat)
    (hnext : level < next) :
    ¬ anchorRank next kind group < anchorRank level 4 1 := by
  unfold anchorRank
  omega

end OrderedMatrixRemoval4
