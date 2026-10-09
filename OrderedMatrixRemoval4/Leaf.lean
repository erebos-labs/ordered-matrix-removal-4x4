import OrderedMatrixRemoval4.Crown

namespace OrderedMatrixRemoval4.Host

theorem tree_terminal_clone (column : Bool) (rem depth node j : Nat) (s : Bool) (q a : Nat)
    (hm : .variable j s q a ∈ tree column rem depth node)
    (hj : j = depth + rem) : a = 0 := by
  induction rem generalizing depth node with
  | zero =>
    have he := List.eq_of_mem_singleton hm
    cases he
    rfl
  | succ rem ih =>
    simp only [tree, List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨a', _, he⟩
      have hd := (Position.variable.inj he).1
      omega
    · exact ih _ _ hm (by omega)
    · exact ih _ _ hm (by omega)
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨a', _, he⟩
      have hd := (Position.variable.inj he).1
      omega

theorem leaf_tag_clone_zero (column : Bool) (h : Nat) (s : Bool) (q a : Nat)
    (hm : .variable h s q a ∈ axis column h) : a = 0 := by
  rcases List.mem_append.mp hm with hm | hm
  · simp only [anchors, List.mem_map] at hm
    rcases hm with ⟨index, _, he⟩
    unfold anchorLabel at he
    contradiction
  · unfold nonanchors at hm
    cases column <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hm
    · rcases hm with ht | hd
      · exact tree_terminal_clone false h 0 0 h s q a ht (by omega)
      · simp only [dummies, List.mem_map] at hd
        rcases hd with ⟨_, _, he⟩; contradiction
    · rcases hm with hd | ht
      · simp only [dummies, List.mem_map] at hd
        rcases hd with ⟨_, _, he⟩; contradiction
      · exact tree_terminal_clone true h 0 0 h s q a ht (by omega)

end OrderedMatrixRemoval4.Host
