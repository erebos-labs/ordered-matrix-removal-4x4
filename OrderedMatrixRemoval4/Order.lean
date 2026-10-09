import OrderedMatrixRemoval4.Structure

namespace OrderedMatrixRemoval4.Host

def ordinal : Position → Nat
  | .anchor l k g _ => anchorRank (l - 1) k g
  | _ => 0

theorem anchorLabel_ordinal (h index : Nat) :
    ordinal (anchorLabel h index) = index / 2 ^ h := by
  simp only [anchorLabel, ordinal, anchorRank, Nat.add_sub_cancel]
  omega

theorem anchorLabel_valid (h index : Nat) :
    ∃ l k g a, anchorLabel h index = .anchor l k g a ∧
      1 ≤ l ∧ k < 6 ∧ g < 2 := by
  have hu := Nat.zero_le ((index / 2 ^ h) / 12)
  have hm := Nat.mod_lt (index / 2 ^ h) (by decide : 0 < 12)
  have hg := Nat.mod_lt ((index / 2 ^ h) % 12) (by decide : 0 < 2)
  unfold anchorLabel
  refine ⟨_, _, _, _, rfl, ?_, ?_, ?_⟩ <;> omega

theorem anchors_ordered (h : Nat) :
    (anchors h).Pairwise (fun a b => ordinal a ≤ ordinal b) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [anchors, List.getElem_map, List.getElem_range, anchorLabel_ordinal]
  exact Nat.div_le_div_right (Nat.le_of_lt hij)

theorem tree_nonanchor (column : Bool) (rem depth node : Nat)
    (p : Position) (hp : p ∈ tree column rem depth node) : Nonanchor p := by
  induction rem generalizing depth node with
  | zero => have he := List.eq_of_mem_singleton hp; subst p; trivial
  | succ rem ih =>
    simp only [tree, List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · simp only [block, List.mem_map] at hp
      rcases hp with ⟨a, _, rfl⟩; trivial
    · exact ih _ _ hp
    · exact ih _ _ hp
    · simp only [block, List.mem_map] at hp
      rcases hp with ⟨a, _, rfl⟩; trivial

theorem tail_nonanchor (column : Bool) (h : Nat) (p : Position)
    (hp : p ∈ nonanchors column h) : Nonanchor p := by
  unfold nonanchors at hp
  cases column <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hp
  · rcases hp with ht | hd
    · exact tree_nonanchor false h 0 0 p ht
    · simp only [dummies, List.mem_map] at hd
      rcases hd with ⟨a, _, rfl⟩; trivial
  · rcases hp with hd | ht
    · simp only [dummies, List.mem_map] at hd
      rcases hd with ⟨a, _, rfl⟩; trivial
    · exact tree_nonanchor true h 0 0 p ht

theorem anchor_index_lt (column : Bool) (h : Nat) (j : Fin (size h))
    (l k g a : Nat) (he : labelAt column h j = .anchor l k g a) :
    j.val < (anchors h).length := by
  by_cases hj : j.val < (anchors h).length
  · exact hj
  have hle : (anchors h).length ≤ j.val := by omega
  have he' := he
  rw [labelAt_append] at he'
  rw [List.getElem_append_right hle] at he'
  have hm := List.mem_of_getElem he'
  have hf := tail_nonanchor column h (.anchor l k g a) hm
  exact False.elim hf

theorem anchor_index_ordinal (column : Bool) (h : Nat) (j : Fin (size h))
    (l k g a : Nat) (he : labelAt column h j = .anchor l k g a) :
    anchorRank (l - 1) k g = j.val / 2 ^ h := by
  have hj := anchor_index_lt column h j l k g a he
  have he' := he
  rw [labelAt_append] at he'
  rw [List.getElem_append_left hj] at he'
  have ho := congrArg ordinal he'
  simp only [anchors, List.getElem_map, List.getElem_range] at ho
  change ordinal (anchorLabel h j.val) = anchorRank (l - 1) k g at ho
  rw [anchorLabel_ordinal] at ho
  exact ho.symm

theorem anchor_index_valid (column : Bool) (h : Nat) (j : Fin (size h))
    (l k g a : Nat) (he : labelAt column h j = .anchor l k g a) :
    1 ≤ l ∧ k < 6 ∧ g < 2 := by
  have hj := anchor_index_lt column h j l k g a he
  have he' := he
  rw [labelAt_append] at he'
  rw [List.getElem_append_left hj] at he'
  simp only [anchors, List.getElem_map, List.getElem_range] at he'
  have hv := anchorLabel_valid h j.val
  rcases hv with ⟨l', k', g', a', heq, hl, hk, hg⟩
  rw [he'] at heq
  cases heq
  exact ⟨hl, hk, hg⟩

theorem anchor_order_le (column : Bool) (h : Nat) (x y : Fin (size h))
    (l k g a l' k' g' a' : Nat)
    (hx : labelAt column h x = .anchor l k g a)
    (hy : labelAt column h y = .anchor l' k' g' a') (hxy : x.val < y.val) :
    anchorRank (l - 1) k g ≤ anchorRank (l' - 1) k' g' := by
  rw [anchor_index_ordinal column h x l k g a hx,
      anchor_index_ordinal column h y l' k' g' a' hy]
  exact Nat.div_le_div_right (Nat.le_of_lt hxy)

end OrderedMatrixRemoval4.Host
