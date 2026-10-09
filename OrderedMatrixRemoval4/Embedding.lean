import OrderedMatrixRemoval4.ParentOrder
import OrderedMatrixRemoval4.Incidence

namespace OrderedMatrixRemoval4.Host

/-- Pattern row distinction makes the nondecreasing concrete anchor order strict. -/
theorem first_two_anchor_order_strict (h : Nat)
    (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols)
    (l k g a l' k' g' a' : Nat)
    (h0 : labelAt false h (rows 0) = .anchor l k g a)
    (h1 : labelAt false h (rows 1) = .anchor l' k' g' a') :
    anchorRank (l - 1) k g < anchorRank (l' - 1) k' g' := by
  have hv0 := anchor_index_valid false h (rows 0) l k g a h0
  have hv1 := anchor_index_valid false h (rows 1) l' k' g' a' h1
  have hord := anchor_order_le false h (rows 0) (rows 1) l k g a l' k' g' a'
    h0 h1 (hc.1 0 1 (by decide))
  by_cases heq : anchorRank (l - 1) k g = anchorRank (l' - 1) k' g'
  · have hsame : l = l' ∧ k = k' ∧ g = g' := by
      unfold anchorRank at heq
      omega
    rcases hsame with ⟨rfl, rfl, rfl⟩
    have hm0 := hc.2.2 0 0
    have hm1 := hc.2.2 1 0
    simp only [matrix, h0, h1] at hm0 hm1
    rw [anchor_row_twins (b := a')] at hm0
    rw [hm1] at hm0
    contradiction
  · omega

/-- A concrete embedding cannot realize the even-minus sibling branch.
The parent inequality follows from the actual independent column order. -/
theorem no_even_minus_nonterminal_shape (h i l k g a a' p q b x z w : Nat)
    (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols)
    (hi : i < h) (hpos : 1 ≤ i)
    (hr0 : labelAt false h (rows 0) = .anchor l k g a)
    (hr1 : labelAt false h (rows 1) = .anchor i 4 1 a')
    (hr2 : labelAt false h (rows 2) = .variable i false p x)
    (hc2 : labelAt true h (cols 2) = .variable i false q z)
    (hc3 : labelAt true h (cols 3) = .variable (i - 1) false b w) : False := by
  have hparent := column_minus_child_parent h i q b z w (cols 2) (cols 3)
    hpos (hc.2.1 2 3 (by decide)) hc2 hc3
  have hl := (anchor_index_valid false h (rows 0) l k g a hr0).1
  have hord := first_two_anchor_order_strict h rows cols hc l k g a i 4 1 a' hr0 hr1
  have hone := hc.2.2 2 2
  simp [matrix, hr2, hc2, entry, H4, signed, Nat.ne_of_lt hi] at hone
  have hzero := hc.2.2 2 3
  have hd : i ≠ i - 1 := by omega
  have hs : i = i - 1 + 1 := by omega
  simp [matrix, hr2, hc3, entry, H4, signed, Nat.ne_of_lt hi, hd] at hzero
  have hinc := hc.2.2 0 2
  simp only [matrix, hr0, hc2] at hinc
  exact nonterminal_sibling_exception_impossible h i l k g p q b a z
    hi hpos hl hord hinc hone.2 (by omega) (by omega)

/-- Both parity modes are excluded for the actual nonterminal unpinned shape.
All hypotheses are literal coordinate identities for an ordinary ordered copy;
there are no extra numerical order or parity assumptions. -/
theorem no_nonterminal_unpinned_minus_shape
    (h i t l k g a a' c p q b x z w : Nat)
    (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols)
    (hi : i < h) (hpos : 1 ≤ i) (ht : t = 4 ∨ t = 5)
    (hr0 : labelAt false h (rows 0) = .anchor l k g a)
    (hr1 : labelAt false h (rows 1) = .anchor i t 1 a')
    (hr2 : labelAt false h (rows 2) = .variable i false p x)
    (hc0 : labelAt true h (cols 0) = .anchor i t 0 c)
    (hc2 : labelAt true h (cols 2) = .variable i false q z)
    (hc3 : labelAt true h (cols 3) = .variable (i - 1) false b w) : False := by
  have hparent := column_minus_child_parent h i q b z w (cols 2) (cols 3)
    hpos (hc.2.1 2 3 (by decide)) hc2 hc3
  have hone := hc.2.2 2 2
  simp [matrix, hr2, hc2, entry, H4, signed, Nat.ne_of_lt hi] at hone
  have hzero := hc.2.2 2 3
  have hd : i ≠ i - 1 := by omega
  have hs : i = i - 1 + 1 := by omega
  simp [matrix, hr2, hc3, entry, H4, signed, Nat.ne_of_lt hi, hd] at hzero
  have hsib := OrderedMatrixRemoval4.nonterminal_siblings p q b hone.2 hparent (by omega)
  have hpar := hc.2.2 2 0
  simp [matrix, hr2, hc0, entry, H4, rowRole, signed, Nat.ne_of_lt hi] at hpar
  have ht4 : t = 4 := by omega
  subst t
  exact no_even_minus_nonterminal_shape h i l k g a a' p q b x z w rows cols hc
    hi hpos hr0 hr1 hr2 hc2 hc3

end OrderedMatrixRemoval4.Host
