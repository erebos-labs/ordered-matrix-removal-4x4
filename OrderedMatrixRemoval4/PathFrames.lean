import OrderedMatrixRemoval4.HostGuard

namespace OrderedMatrixRemoval4.Host

def viewSign (h i : Nat) (s : Bool) : Bool := if i = h then true else s

/-- Actual representatives on one binary-tree path. No guards or body bits
are included in this structure. All positions are ordinary physical indices. -/
structure PathSelection (h : Nat) where
  node : Nat → Nat
  root : node 0 = 0
  parent : ∀ i, i < h → node (i + 1) / 2 = node i
  row : Nat → Bool → Fin (size h)
  col : Nat → Bool → Fin (size h)
  rowClone : Nat → Bool → Nat
  colClone : Nat → Bool → Nat
  rowLabel : ∀ i, i ≤ h → ∀ s,
    labelAt false h (row i s) = .variable i (viewSign h i s) (node i) (rowClone i s)
  colLabel : ∀ i, i ≤ h → ∀ s,
    labelAt true h (col i s) = .variable i (viewSign h i s) (node i) (colClone i s)
  ra : Nat → Nat → Nat → Fin (size h)
  ca : Nat → Nat → Nat → Fin (size h)
  raClone : Nat → Nat → Nat → Nat
  caClone : Nat → Nat → Nat → Nat
  raLabel : ∀ l, 1 ≤ l → l ≤ h → ∀ k, k < 6 → ∀ g, g < 2 →
    labelAt false h (ra l k g) = .anchor l k g (raClone l k g)
  caLabel : ∀ l, 1 ≤ l → l ≤ h → ∀ k, k < 6 → ∀ g, g < 2 →
    labelAt true h (ca l k g) = .anchor l k g (caClone l k g)
  rd : Fin (size h)
  cd : Fin (size h)
  rdClone : Nat
  cdClone : Nat
  rdLabel : labelAt false h rd = .dummy rdClone
  cdLabel : labelAt true h cd = .dummy cdClone

private theorem selected_guard (h i k : Nat) (s : PathSelection h) (hi : i < h) (hk : k < 6)
    (r2 r3 c2 c3 : Fin (size h))
    (rr0 : rowRole h (i+1) k 0 (labelAt false h r2))
    (rr1 : rowRole h (i+1) k 1 (labelAt false h r3))
    (cc0 : columnRole h (i+1) k 0 (labelAt true h c2))
    (cc1 : columnRole h (i+1) k 1 (labelAt true h c3))
    (hro : r2.val < r3.val) (hco : c2.val < c3.val) :
    FrameGuard (matrix h)
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) r2 r3)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) c2 c3) :=
  canonical_host_guard h (i+1) k _ _ _ _ _ _ _ _ _ _ _ _
    (s.raLabel _ (by omega) (by omega) _ hk _ (by decide))
    (s.raLabel _ (by omega) (by omega) _ hk _ (by decide))
    (s.caLabel _ (by omega) (by omega) _ hk _ (by decide))
    (s.caLabel _ (by omega) (by omega) _ hk _ (by decide)) rr0 rr1 cc0 cc1 hro hco

theorem path_vertical_plus_guard (h i : Nat) (s : PathSelection h) (hi : i < h) :
    FrameGuard (matrix h)
      (four (s.ra (i+1) 0 0) (s.ra (i+1) 0 1) (s.row (i+1) true) (s.row i true))
      (four (s.ca (i+1) 0 0) (s.ca (i+1) 0 1) s.cd (s.col i true)) := by
  have rchild := s.rowLabel (i+1) (by omega) true
  have rparent := s.rowLabel i (by omega) true
  have cparent := s.colLabel i (by omega) true
  simp only [viewSign,ite_self] at rchild rparent cparent
  apply selected_guard h i 0 s hi (by decide)
  · simp [rchild,rowRole,signed]
  · simp [rparent,rowRole,signed]
  · simp [s.cdLabel,columnRole]
  · simp [cparent,columnRole,signed]
  · exact child_before_closing_parent false h i _ _ _ _ true _ _ rchild rparent (s.parent i hi)
  · exact column_dummy_before_variable h i _ _ _ true _ _ s.cdLabel cparent

theorem path_vertical_minus_guard (h i : Nat) (s : PathSelection h) (hi : i < h) :
    FrameGuard (matrix h)
      (four (s.ra (i+1) 1 0) (s.ra (i+1) 1 1) (s.row i false) (s.row (i+1) false))
      (four (s.ca (i+1) 1 0) (s.ca (i+1) 1 1) s.cd (s.col i false)) := by
  have rchild := s.rowLabel (i+1) (by omega) false
  have rparent := s.rowLabel i (by omega) false
  have cparent := s.colLabel i (by omega) false
  simp only [viewSign,if_neg (Nat.ne_of_lt hi)] at rparent cparent
  apply selected_guard h i 1 s hi (by decide)
  · simp [rparent,rowRole,signed]
  · simp [rchild,rowRole,signed,viewSign] <;> omega
  · simp [s.cdLabel,columnRole]
  · simp [cparent,columnRole,signed]
  · exact opening_parent_before_child false h i _ _ _ _ _ _ _ rparent rchild (s.parent i hi)
  · exact column_dummy_before_variable h i _ _ _ false _ _ s.cdLabel cparent

theorem path_horizontal_plus_guard (h i : Nat) (s : PathSelection h) (hi : i < h) :
    let k := 2 + s.node (i+1) % 2
    FrameGuard (matrix h)
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) (s.row (i+1) true) s.rd)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) (s.col i true) (s.col (i+1) true)) := by
  dsimp only
  have rchild := s.rowLabel (i+1) (by omega) true
  have cparent := s.colLabel i (by omega) true
  have cchild := s.colLabel (i+1) (by omega) true
  simp only [viewSign,ite_self] at rchild cparent cchild
  have hm : s.node (i+1) % 2 = 0 ∨ s.node (i+1) % 2 = 1 := by omega
  apply selected_guard h i _ s hi (by omega)
  · rcases hm with hm | hm <;> simp [rchild,rowRole,signed,hm]
  · rcases hm with hm | hm <;> simp [s.rdLabel,rowRole,hm]
  · rcases hm with hm | hm <;> simp [cparent,columnRole,signed,hm]
  · rcases hm with hm | hm <;> simp [cchild,columnRole,signed,hm]
  · exact variable_before_row_dummy h (i+1) _ _ _ true _ _ rchild s.rdLabel
  · exact opening_parent_before_child true h i _ _ _ _ true _ _ cparent cchild (s.parent i hi)

theorem path_horizontal_minus_guard (h i : Nat) (s : PathSelection h) (hi : i < h) :
    let k := 4 + s.node (i+1) % 2
    FrameGuard (matrix h)
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) (s.row (i+1) false) s.rd)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) (s.col (i+1) false) (s.col i false)) := by
  dsimp only
  have rchild := s.rowLabel (i+1) (by omega) false
  have cparent := s.colLabel i (by omega) false
  have cchild := s.colLabel (i+1) (by omega) false
  simp only [viewSign,if_neg (Nat.ne_of_lt hi)] at cparent
  have hm : s.node (i+1) % 2 = 0 ∨ s.node (i+1) % 2 = 1 := by omega
  apply selected_guard h i _ s hi (by omega)
  · rcases hm with hm | hm <;> simp [rchild,rowRole,signed,viewSign,hm] <;> omega
  · rcases hm with hm | hm <;> simp [s.rdLabel,rowRole,hm]
  · rcases hm with hm | hm <;> simp [cchild,columnRole,signed,viewSign,hm] <;> omega
  · rcases hm with hm | hm <;> simp [cparent,columnRole,signed,hm]
  · exact variable_before_row_dummy h (i+1) _ _ _ _ _ _ rchild s.rdLabel
  · exact child_before_closing_parent true h i _ _ _ _ _ _ _ cchild cparent (s.parent i hi)

end OrderedMatrixRemoval4.Host
