import OrderedMatrixRemoval4.Traversal

namespace OrderedMatrixRemoval4.Host

theorem ancestor_mono (d p q : Nat) (hpq : p ≤ q) : ancestor d p ≤ ancestor d q := by
  induction d with
  | zero => exact hpq
  | succ d ih => exact Nat.div_le_div_right ih

theorem ancestor_div_two (d p : Nat) : ancestor d (p / 2) = ancestor (d + 1) p := by
  induction d with
  | zero => rfl
  | succ d ih => simpa only [ancestor] using congrArg (fun n => n / 2) ih

def MinusParentOrdered (x y : Position) : Prop :=
  ∀ i q b a z, 1 ≤ i → x = .variable i false q a →
    y = .variable (i - 1) false b z → q / 2 ≤ b

private theorem block_data (depth node size j q a : Nat) (s t : Bool)
    (hm : .variable j s q a ∈ block depth t node size) :
    j = depth ∧ s = t ∧ q = node := by
  simp only [block, List.mem_map] at hm
  rcases hm with ⟨b, _, he⟩
  have hd := Position.variable.inj he
  exact ⟨hd.1.symm, hd.2.1.symm, hd.2.2.1.symm⟩

private theorem opening_ordered (depth node size : Nat) (x y : Position)
    (hm : x ∈ block depth true node size) : MinusParentOrdered x y := by
  intro i q b a z hi hx _
  rw [hx] at hm
  have hf := (block_data depth node size i q a false true hm).2.1
  contradiction

private theorem closing_ordered (depth node size : Nat) :
    (block depth false node size).Pairwise MinusParentOrdered := by
  apply List.pairwise_iff_getElem.mpr
  intro a b ha hb _ i q p x z hi hx hy
  have hx' := List.getElem_mem ha
  have hy' := List.getElem_mem hb
  rw [hx] at hx'
  rw [hy] at hy'
  have hd0 := (block_data depth node size i q x false false hx').1
  have hd1 := (block_data depth node size (i - 1) p z false false hy').1
  omega

private theorem siblings_ordered (rem depth node : Nat) (x y : Position)
    (hx : x ∈ tree true rem (depth + 1) (2 * node))
    (hy : y ∈ tree true rem (depth + 1) (2 * node + 1)) : MinusParentOrdered x y := by
  intro i q b a z hi he0 he1
  rw [he0] at hx
  rw [he1] at hy
  have h0 := tree_location true rem (depth + 1) (2 * node) i false q a hx
  have h1 := tree_location true rem (depth + 1) (2 * node + 1) (i - 1) false b z hy
  have hd : i - (depth + 1) = (i - 1 - (depth + 1)) + 1 := by omega
  have he : ancestor (i - 1 - (depth + 1)) (q / 2) = 2 * node := by
    rw [ancestor_div_two, ← hd]
    exact h0.2
  by_cases hb : q / 2 ≤ b
  · exact hb
  · have hmono := ancestor_mono (i - 1 - (depth + 1)) b (q / 2) (by omega)
    rw [he, h1.2] at hmono
    omega

private theorem child_closing_ordered (rem depth node child size : Nat)
    (hchild : child = 2 * node ∨ child = 2 * node + 1) (x y : Position)
    (hx : x ∈ tree true rem (depth + 1) child)
    (hy : y ∈ block depth false node size) : MinusParentOrdered x y := by
  intro i q b a z hi he0 he1
  rw [he0] at hx
  rw [he1] at hy
  have h0 := tree_location true rem (depth + 1) child i false q a hx
  have h1 := block_data depth node size (i - 1) b z false false hy
  have hd : i = depth + 1 := by omega
  have hq : q = child := by simpa [hd, ancestor] using h0.2
  omega

theorem tree_minus_parent_ordered (rem depth node : Nat) :
    (tree true rem depth node).Pairwise MinusParentOrdered := by
  induction rem generalizing depth node with
  | zero => simp [tree]
  | succ rem ih =>
    have hop : (block depth true node (2 ^ (rem + 1))).Pairwise MinusParentOrdered := by
      apply List.pairwise_iff_getElem.mpr
      intro i j hi hj hij
      exact opening_ordered depth node _ _ _ (List.getElem_mem hi)
    have hab : (block depth true node (2 ^ (rem + 1)) ++
        tree true rem (depth + 1) (2 * node)).Pairwise MinusParentOrdered := by
      apply List.pairwise_append.mpr
      refine ⟨hop, ih .., ?_⟩
      intro x hx y _
      exact opening_ordered depth node _ x y hx
    have habc : ((block depth true node (2 ^ (rem + 1)) ++
        tree true rem (depth + 1) (2 * node)) ++
        tree true rem (depth + 1) (2 * node + 1)).Pairwise MinusParentOrdered := by
      apply List.pairwise_append.mpr
      refine ⟨hab, ih .., ?_⟩
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact opening_ordered depth node _ x y hx
      · exact siblings_ordered rem depth node x y hx hy
    unfold tree
    apply List.pairwise_append.mpr
    refine ⟨habc, closing_ordered .., ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact opening_ordered depth node _ x y hx
      · exact child_closing_ordered rem depth node _ _ (Or.inl rfl) x y hx hy
    · exact child_closing_ordered rem depth node _ _ (Or.inr rfl) x y hx hy

private theorem anchor_ordered_any (h : Nat) (x y : Position) (hx : x ∈ anchors h) :
    MinusParentOrdered x y := by
  simp only [anchors, List.mem_map] at hx
  rcases hx with ⟨index, _, rfl⟩
  intro i q b a z hi he _
  unfold anchorLabel at he
  contradiction

private theorem dummy_ordered_any (h : Nat) (x y : Position) (hx : x ∈ dummies h) :
    MinusParentOrdered x y := by
  simp only [dummies, List.mem_map] at hx
  rcases hx with ⟨index, _, rfl⟩
  intro i q b a z hi he _
  contradiction

theorem axis_minus_parent_ordered (h : Nat) : (axis true h).Pairwise MinusParentOrdered := by
  have ha : (anchors h).Pairwise MinusParentOrdered := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    exact anchor_ordered_any h _ _ (List.getElem_mem hi)
  have hd : (dummies h).Pairwise MinusParentOrdered := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    exact dummy_ordered_any h _ _ (List.getElem_mem hi)
  have hn : (dummies h ++ tree true h 0 0).Pairwise MinusParentOrdered := by
    apply List.pairwise_append.mpr
    refine ⟨hd, tree_minus_parent_ordered .., ?_⟩
    intro x hx y _
    exact dummy_ordered_any h x y hx
  apply List.pairwise_append.mpr
  refine ⟨ha, hn, ?_⟩
  intro x hx y _
  exact anchor_ordered_any h x y hx

theorem column_minus_child_parent (h i q b a z : Nat) (x y : Fin (size h))
    (hi : 1 ≤ i) (hxy : x.val < y.val)
    (hx : labelAt true h x = .variable i false q a)
    (hy : labelAt true h y = .variable (i - 1) false b z) : q / 2 ≤ b := by
  have hxlen : x.val < (axis true h).length := by rw [axis_length]; exact x.isLt
  have hylen : y.val < (axis true h).length := by rw [axis_length]; exact y.isLt
  have hr := (axis_minus_parent_ordered h).rel_getElem_of_lt hxlen hylen hxy
  exact hr i q b a z hi hx hy

end OrderedMatrixRemoval4.Host
