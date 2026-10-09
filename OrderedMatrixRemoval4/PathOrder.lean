import OrderedMatrixRemoval4.Sparse

namespace OrderedMatrixRemoval4.Host

private theorem traversal_refl (column : Bool) (p : Position) : TraversalOrdered column p p := by
  cases p <;> simp [TraversalOrdered]

private theorem index_lt_of_no_reverse (column : Bool) (h : Nat) (x y : Fin (size h))
    (hn : ¬ TraversalOrdered column (labelAt column h y) (labelAt column h x)) : x.val < y.val := by
  by_cases hl : x.val < y.val
  · exact hl
  · by_cases he : x = y
    · subst y; exact False.elim (hn (traversal_refl column _))
    · exact False.elim (hn (indexed_traversal_ordered column h y x (by omega)))

theorem opening_parent_before_child (column : Bool) (h i p q a b : Nat) (s : Bool)
    (x y : Fin (size h)) (hx : labelAt column h x = .variable i column p a)
    (hy : labelAt column h y = .variable (i + 1) s q b) (hp : q / 2 = p) :
    x.val < y.val := by
  apply index_lt_of_no_reverse column h x y
  rw [hx,hy]
  simp [TraversalOrdered,ancestor]
  omega

theorem child_before_closing_parent (column : Bool) (h i p q a b : Nat) (s : Bool)
    (x y : Fin (size h)) (hx : labelAt column h x = .variable (i + 1) s q a)
    (hy : labelAt column h y = .variable i (!column) p b) (hp : q / 2 = p) :
    x.val < y.val := by
  apply index_lt_of_no_reverse column h x y
  rw [hx,hy]
  cases column <;> simp [TraversalOrdered,ancestor] <;> omega

theorem opening_before_closing (column : Bool) (h i p a b : Nat)
    (x y : Fin (size h)) (hx : labelAt column h x = .variable i column p a)
    (hy : labelAt column h y = .variable i (!column) p b) : x.val < y.val := by
  apply index_lt_of_no_reverse column h x y
  rw [hx,hy]
  cases column <;> simp [TraversalOrdered]

theorem anchor_before_nonanchor (column : Bool) (h : Nat) (x y : Fin (size h))
    (hx : Anchor (labelAt column h x)) (hy : Nonanchor (labelAt column h y)) : x.val < y.val := by
  have hxi := (anchor_iff_index_lt column h x).mp hx
  have hyi : ¬ y.val < (anchors h).length := by
    intro he; exact (anchor_iff_not_nonanchor _).mp (anchor_of_index_lt column h y he) hy
  omega

theorem anchor_group_order (column : Bool) (h l k a b : Nat)
    (x y : Fin (size h)) (hx : labelAt column h x = .anchor l k 0 a)
    (hy : labelAt column h y = .anchor l k 1 b) : x.val < y.val := by
  have h0 := anchor_index_ordinal column h x l k 0 a hx
  have h1 := anchor_index_ordinal column h y l k 1 b hy
  unfold anchorRank at h0 h1
  by_cases hlt : x.val < y.val
  · exact hlt
  · have hmono := Nat.div_le_div_right (c := 2 ^ h) (show y.val ≤ x.val from by omega)
    omega

def phase (column : Bool) : Position → Nat
  | .anchor .. => 0
  | .dummy _ => if column then 1 else 2
  | .variable .. => if column then 2 else 1

private theorem constant_phase_pairwise (column : Bool) (xs : List Position) (k : Nat)
    (hk : ∀ x ∈ xs, phase column x = k) :
    xs.Pairwise (fun x y => phase column x ≤ phase column y) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  rw [hk _ (List.getElem_mem hi),hk _ (List.getElem_mem hj)]
  exact Nat.le_refl k

private theorem phase_pairwise_append (column : Bool) (xs ys : List Position) (a b : Nat)
    (ha : ∀ x ∈ xs, phase column x = a) (hb : ∀ y ∈ ys, phase column y = b)
    (hab : a ≤ b) : (xs ++ ys).Pairwise (fun x y => phase column x ≤ phase column y) := by
  apply List.pairwise_append.mpr
  refine ⟨constant_phase_pairwise column xs a ha,constant_phase_pairwise column ys b hb,?_⟩
  intro x hx y hy
  rw [ha x hx,hb y hy]
  exact hab

theorem axis_phase_ordered (column : Bool) (h : Nat) :
    (axis column h).Pairwise (fun x y => phase column x ≤ phase column y) := by
  have ha : ∀ x ∈ anchors h, phase column x = 0 := by
    intro x hx
    simp only [anchors,List.mem_map] at hx
    rcases hx with ⟨i,hi,rfl⟩
    rfl
  have hd : ∀ x ∈ dummies h, phase column x = (if column then 1 else 2) := by
    intro x hx
    simp only [dummies,List.mem_map] at hx
    rcases hx with ⟨i,hi,rfl⟩
    rfl
  have ht : ∀ x ∈ tree column h 0 0, phase column x = (if column then 2 else 1) := by
    intro x hx
    have hv := tree_variable column h 0 0 x hx
    cases x <;> simp_all [phase,IsVariable]
  have hn : (nonanchors column h).Pairwise (fun x y => phase column x ≤ phase column y) := by
    cases column
    · exact phase_pairwise_append false _ _ 1 2 ht hd (by decide)
    · exact phase_pairwise_append true _ _ 1 2 hd ht (by decide)
  apply List.pairwise_append.mpr
  refine ⟨constant_phase_pairwise column _ 0 ha,hn,?_⟩
  intro x hx y hy
  rw [ha x hx]
  exact Nat.zero_le _

private theorem index_lt_of_phase_lt (column : Bool) (h : Nat) (x y : Fin (size h))
    (hp : phase column (labelAt column h x) < phase column (labelAt column h y)) : x.val < y.val := by
  by_cases hlt : x.val < y.val
  · exact hlt
  · by_cases he : x = y
    · subst y; omega
    · have hrev : y.val < x.val := by omega
      have hx : x.val < (axis column h).length := by rw [axis_length]; exact x.isLt
      have hy : y.val < (axis column h).length := by rw [axis_length]; exact y.isLt
      have ho := (axis_phase_ordered column h).rel_getElem_of_lt hy hx hrev
      change phase column (labelAt column h y) ≤ phase column (labelAt column h x) at ho
      omega

theorem variable_before_row_dummy (h i p a b : Nat) (s : Bool) (x y : Fin (size h))
    (hx : labelAt false h x = .variable i s p a) (hy : labelAt false h y = .dummy b) :
    x.val < y.val := by
  apply index_lt_of_phase_lt false h x y
  simp [hx,hy,phase]

theorem column_dummy_before_variable (h i p a b : Nat) (s : Bool) (x y : Fin (size h))
    (hx : labelAt true h x = .dummy a) (hy : labelAt true h y = .variable i s p b) :
    x.val < y.val := by
  apply index_lt_of_phase_lt true h x y
  simp [hx,hy,phase]

end OrderedMatrixRemoval4.Host
