import OrderedMatrixRemoval4.Order

namespace OrderedMatrixRemoval4.Host

def IsVariable : Position → Prop
  | .variable .. => True
  | _ => False

theorem tree_variable (column : Bool) (rem depth node : Nat)
    (p : Position) (hp : p ∈ tree column rem depth node) : IsVariable p := by
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

def ancestor : Nat → Nat → Nat
  | 0, p => p
  | d + 1, p => ancestor d p / 2

theorem tree_location (column : Bool) (rem depth node j : Nat)
    (s : Bool) (q a : Nat) (hm : .variable j s q a ∈ tree column rem depth node) :
    depth ≤ j ∧ ancestor (j - depth) q = node := by
  induction rem generalizing depth node with
  | zero =>
    have he := List.eq_of_mem_singleton hm
    cases he
    simp [ancestor]
  | succ rem ih =>
    simp only [tree, List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨b, _, he⟩
      cases he
      simp [ancestor]
    · have ht := ih _ _ hm
      have hd : j - depth = (j - (depth + 1)) + 1 := by omega
      rw [hd, ancestor, ht.2]
      constructor <;> omega
    · have ht := ih _ _ hm
      have hd : j - depth = (j - (depth + 1)) + 1 := by omega
      rw [hd, ancestor, ht.2]
      constructor <;> omega
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨b, _, he⟩
      cases he
      simp [ancestor]

theorem block_nodup (depth : Nat) (s : Bool) (node size : Nat) :
    (block depth s node size).Nodup := by
  apply List.Pairwise.map _ _ List.nodup_range
  intro a b hab he
  exact hab (Position.variable.inj he).2.2.2

private theorem block_child_disjoint (column : Bool) (rem depth node child : Nat)
    (s : Bool) (size : Nat) (x : Position)
    (hb : x ∈ block depth s node size)
    (ht : x ∈ tree column rem (depth + 1) child) : False := by
  simp only [block, List.mem_map] at hb
  rcases hb with ⟨a, _, rfl⟩
  have hd := (tree_location column rem (depth + 1) child depth s node a ht).1
  omega

private theorem children_disjoint (column : Bool) (rem depth node : Nat) (x : Position)
    (h0 : x ∈ tree column rem (depth + 1) (2 * node))
    (h1 : x ∈ tree column rem (depth + 1) (2 * node + 1)) : False := by
  have hn := tree_variable column rem (depth + 1) (2 * node) x h0
  cases x with
  | anchor => contradiction
  | dummy => contradiction
  | «variable» j s q a =>
    have hl := (tree_location column rem (depth + 1) (2 * node) j s q a h0).2
    have hr := (tree_location column rem (depth + 1) (2 * node + 1) j s q a h1).2
    omega

theorem tree_nodup (column : Bool) (rem depth node : Nat) :
    (tree column rem depth node).Nodup := by
  induction rem generalizing depth node with
  | zero => simp [tree]
  | succ rem ih =>
    have hab : (block depth column node (2 ^ (rem + 1)) ++
        tree column rem (depth + 1) (2 * node)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨block_nodup .., ih .., ?_⟩
      intro x hx y hy he
      subst y
      exact block_child_disjoint column rem depth node (2 * node) column _ x hx hy
    have habc : ((block depth column node (2 ^ (rem + 1)) ++
        tree column rem (depth + 1) (2 * node)) ++
        tree column rem (depth + 1) (2 * node + 1)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨hab, ih .., ?_⟩
      intro x hx y hy he
      subst y
      rcases List.mem_append.mp hx with hx | hx
      · exact block_child_disjoint column rem depth node (2 * node + 1) column _ x hx hy
      · exact children_disjoint column rem depth node x hx hy
    unfold tree
    apply List.nodup_append.mpr
    refine ⟨habc, block_nodup .., ?_⟩
    intro x hx y hy he
    subst y
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [block, List.mem_map] at hx hy
        rcases hx with ⟨a, _, rfl⟩
        rcases hy with ⟨b, _, he⟩
        cases column <;> simp at he
      · exact block_child_disjoint column rem depth node (2 * node) (!column) _ x hy hx
    · exact block_child_disjoint column rem depth node (2 * node + 1) (!column) _ x hy hx

theorem anchorLabel_injective (h i j : Nat) (he : anchorLabel h i = anchorLabel h j) :
    i = j := by
  have ho := congrArg ordinal he
  rw [anchorLabel_ordinal, anchorLabel_ordinal] at ho
  have ha : i % 2 ^ h = j % 2 ^ h := by
    simp only [anchorLabel, Position.anchor.injEq] at he
    exact he.2.2.2
  have hi := Nat.mod_add_div i (2 ^ h)
  have hj := Nat.mod_add_div j (2 ^ h)
  rw [ho, ha] at hi
  omega

theorem anchors_nodup (h : Nat) : (anchors h).Nodup := by
  apply List.Pairwise.map _ _ List.nodup_range
  intro i j hij he
  exact hij (anchorLabel_injective h i j he)

theorem dummies_nodup (h : Nat) : (dummies h).Nodup := by
  apply List.Pairwise.map _ _ List.nodup_range
  intro i j hij he
  exact hij (Position.dummy.inj he)

private theorem tree_dummy_disjoint (column : Bool) (h : Nat) (x y : Position)
    (hx : x ∈ tree column h 0 0) (hy : y ∈ dummies h) : x ≠ y := by
  intro he
  subst y
  have hv := tree_variable column h 0 0 x hx
  simp only [dummies, List.mem_map] at hy
  rcases hy with ⟨a, _, rfl⟩
  contradiction

theorem nonanchors_nodup (column : Bool) (h : Nat) :
    (nonanchors column h).Nodup := by
  cases column <;> unfold nonanchors <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · apply List.nodup_append.mpr
    refine ⟨tree_nodup .., dummies_nodup h, ?_⟩
    intro x hx y hy
    exact tree_dummy_disjoint false h x y hx hy
  · apply List.nodup_append.mpr
    refine ⟨dummies_nodup h, tree_nodup .., ?_⟩
    intro x hx y hy he
    exact tree_dummy_disjoint true h y x hy hx he.symm

theorem axis_nodup (column : Bool) (h : Nat) : (axis column h).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨anchors_nodup h, nonanchors_nodup column h, ?_⟩
  intro x hx y hy he
  subst y
  have hn := tail_nonanchor column h x hy
  simp only [anchors, List.mem_map] at hx
  rcases hx with ⟨index, _, rfl⟩
  unfold anchorLabel at hn
  contradiction

theorem labelAt_injective (column : Bool) (h : Nat) (i j : Fin (size h))
    (he : labelAt column h i = labelAt column h j) : i = j := by
  apply Fin.ext
  exact (axis_nodup column h).getElem_inj.mp he

end OrderedMatrixRemoval4.Host
