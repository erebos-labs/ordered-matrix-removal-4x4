import OrderedMatrixRemoval4.Traversal

namespace OrderedMatrixRemoval4.Host

theorem labelAt_surjective (column : Bool) (h : Nat) (p : Position)
    (hp : p ∈ axis column h) : ∃ j : Fin (size h), labelAt column h j = p := by
  rcases List.mem_iff_getElem.mp hp with ⟨j, hj, he⟩
  have hj' : j < size h := by rw [← axis_length column h]; exact hj
  exact ⟨⟨j, hj'⟩, he⟩

def Before (column : Bool) (h : Nat) (p q : Position) : Prop :=
  ∃ i j : Fin (size h), labelAt column h i = p ∧ labelAt column h j = q ∧ i.val < j.val

/-- Copies on the physical tags, with independent traversal orders. -/
def TagCopy (h : Nat) (rows cols : Fin 4 → Position) : Prop :=
  (∀ i, rows i ∈ axis false h) ∧ (∀ i, cols i ∈ axis true h) ∧
  (∀ i j, i.val < j.val → Before false h (rows i) (rows j)) ∧
  (∀ i j, i.val < j.val → Before true h (cols i) (cols j)) ∧
  (∀ i j, entry h (rows i) (cols j) = H4 i j)

theorem tagCopy_of_copy (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : Copy h rows cols) :
    TagCopy h (fun i => labelAt false h (rows i)) (fun i => labelAt true h (cols i)) := by
  refine ⟨?_, ?_, ?_, ?_, hc.2.2⟩
  · intro i; exact List.getElem_mem _
  · intro i; exact List.getElem_mem _
  · intro i j hij; exact ⟨rows i, rows j, rfl, rfl, hc.1 i j hij⟩
  · intro i j hij; exact ⟨cols i, cols j, rfl, rfl, hc.2.1 i j hij⟩

/-- Exact equivalence with ordinary independent increasing embeddings on Fin n. -/
theorem tagCopy_iff_exists_copy (h : Nat) (rr cc : Fin 4 → Position) :
    TagCopy h rr cc ↔ ∃ rows cols : Fin 4 → Fin (size h),
      Copy h rows cols ∧ (∀ i, labelAt false h (rows i) = rr i) ∧
      (∀ i, labelAt true h (cols i) = cc i) := by
  constructor
  · intro ht
    have hr : ∀ i, ∃ j, labelAt false h j = rr i := fun i => labelAt_surjective false h _ (ht.1 i)
    have hc : ∀ i, ∃ j, labelAt true h j = cc i := fun i => labelAt_surjective true h _ (ht.2.1 i)
    let rows := fun i => Classical.choose (hr i)
    let cols := fun i => Classical.choose (hc i)
    have her : ∀ i, labelAt false h (rows i) = rr i := fun i => Classical.choose_spec (hr i)
    have hec : ∀ i, labelAt true h (cols i) = cc i := fun i => Classical.choose_spec (hc i)
    refine ⟨rows, cols, ⟨?_, ?_, ?_⟩, her, hec⟩
    · intro i j hij
      rcases ht.2.2.1 i j hij with ⟨x, y, hx, hy, hxy⟩
      have hxi := labelAt_injective false h x (rows i) (hx.trans (her i).symm)
      have hyj := labelAt_injective false h y (rows j) (hy.trans (her j).symm)
      simpa [hxi, hyj] using hxy
    · intro i j hij
      rcases ht.2.2.2.1 i j hij with ⟨x, y, hx, hy, hxy⟩
      have hxi := labelAt_injective true h x (cols i) (hx.trans (hec i).symm)
      have hyj := labelAt_injective true h y (cols j) (hy.trans (hec j).symm)
      simpa [hxi, hyj] using hxy
    · intro i j
      simp only [matrix, her, hec]
      exact ht.2.2.2.2 i j
  · rintro ⟨rows, cols, hc, hr, he⟩
    have ht := tagCopy_of_copy h rows cols hc
    have er : (fun i => labelAt false h (rows i)) = rr := funext hr
    have ec : (fun i => labelAt true h (cols i)) = cc := funext he
    rw [er, ec] at ht
    exact ht

end OrderedMatrixRemoval4.Host
