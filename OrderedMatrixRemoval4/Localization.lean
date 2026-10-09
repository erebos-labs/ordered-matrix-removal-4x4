import OrderedMatrixRemoval4.UnpinnedBody

namespace OrderedMatrixRemoval4.Host

private theorem same_class_variable (r c : Position) (hr : IsVariable r)
    (hclass : SameClass r c) : IsVariable c := by
  cases r <;> cases c <;> simp_all [IsVariable, SameClass]

theorem unpinned_copy_localization (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : Copy h rows cols) (hn1 : Nonanchor (labelAt true h (cols 1))) :
    sparseZero h (rows 2) (cols 3) := by
  have hs := copy_anchor_shape h rows cols hc
  rcases anchor_exists _ hs.1 with ⟨l0,k0,g0,a0,hr0⟩
  rcases anchor_exists _ hs.2.1 with ⟨l,k,g,a1,hr1⟩
  rcases anchor_exists _ hs.2.2.2.2.1 with ⟨j0,t0,z0,b0,hc0⟩
  rcases second_row_first_column_groups h rows cols hc l k g a1 j0 t0 z0 b0 hr1 hc0 with
    ⟨hlj,hkt,hg,hz⟩
  subst j0
  subst t0
  subst g
  subst z0
  have hv0 := anchor_index_valid false h (rows 0) l0 k0 g0 a0 hr0
  have hv1 := anchor_index_valid false h (rows 1) l k 1 a1 hr1
  have hlh := anchor_index_level_bound false h (rows 1) l k 1 a1 hr1
  have hvar := zero_nonanchors_variable h _ _ hs.2.2.1 hs.2.2.2.2.2.2
    (hc.2.2 2 3)
  rcases variable_data_exists _ hvar.1 with ⟨⟨i,s,p,a⟩,hr⟩
  rcases variable_data_exists _ hvar.2 with ⟨⟨j,t,b,w⟩,hlast⟩
  change .variable i s p a = labelAt false h (rows 2) at hr
  change .variable j t b w = labelAt true h (cols 3) at hlast
  have hclass := anchor_row_connects h (rows 0) (cols 1) (cols 2) hs.1 hn1
    hs.2.2.2.2.2.1 (hc.2.2 0 1) (hc.2.2 0 2)
  have hvar1 := (zero_nonanchors_variable h _ _ hs.2.2.1 hn1 (hc.2.2 2 1)).2
  rcases variable_data_exists _ (same_class_variable _ _ hvar1 hclass) with
    ⟨⟨d,u,q,z⟩,hmiddle⟩
  change .variable d u q z = labelAt true h (cols 2) at hmiddle
  have hdiff : d ≠ j ∨ u ≠ t := by
    by_cases hd : d = j
    · by_cases hu : u = t
      · subst d
        subst u
        have hqb := same_class_node_order true h j q b z w t (cols 2) (cols 3)
          (hc.2.1 2 3 (by decide)) hmiddle.symm hlast.symm
        have hone : entry h (labelAt false h (rows 2)) (.variable j t q z) = true := by
          simpa only [matrix, ← hmiddle] using (show matrix h (rows 2) (cols 2) = true from hc.2.2 2 2)
        have hbad := variable_column_nested h j t q b z w hqb _ hs.2.2.1 hone
        have hzero : entry h (labelAt false h (rows 2)) (.variable j t b w) = false := by
          simpa only [matrix, ← hlast] using (show matrix h (rows 2) (cols 3) = false from hc.2.2 2 3)
        rw [hzero] at hbad
        contradiction
      · exact Or.inr hu
    · exact Or.inl hd
  have vi : i ≤ h ∧ (i = h → s = true) := by
    have hv := labelAt_valid false h (rows 2)
    simpa only [← hr, Valid] using hv
  have vd : d ≤ h ∧ (d = h → u = true) := by
    have hv := labelAt_valid true h (cols 2)
    simpa only [← hmiddle, Valid] using hv
  have vj : j ≤ h ∧ (j = h → t = true) := by
    have hv := labelAt_valid true h (cols 3)
    simpa only [← hlast, Valid] using hv
  have rr : rowRole h l k 0 (.variable i s p a) := by
    have he : entry h (labelAt false h (rows 2)) (.anchor l k 0 b0) = true := by
      simpa only [matrix, hc0] using (show matrix h (rows 2) (cols 0) = true from hc.2.2 2 0)
    simpa only [← hr] using nonanchor_row_role_of_entry h l k 0 b0 _ hs.2.2.1 he
  have cc : columnRole h l k 1 (.variable j t b w) := by
    have he : entry h (.anchor l k 1 a1) (labelAt true h (cols 3)) = true := by
      simpa only [matrix, hr1] using (show matrix h (rows 1) (cols 3) = true from hc.2.2 1 3)
    simpa only [← hlast] using nonanchor_column_role_of_entry h l k 1 a1 _ hs.2.2.2.2.2.2 he
  have hinc : columnRole h l0 k0 g0 (.variable d u q z) := by
    have he : entry h (.anchor l0 k0 g0 a0) (labelAt true h (cols 2)) = true := by
      simpa only [matrix, hr0] using (show matrix h (rows 0) (cols 2) = true from hc.2.2 0 2)
    simpa only [← hmiddle] using nonanchor_column_role_of_entry h l0 k0 g0 a0 _ hs.2.2.2.2.2.1 he
  have co : TraversalOrdered true (.variable d u q z) (.variable j t b w) := by
    simpa only [← hmiddle, ← hlast] using
      indexed_traversal_ordered true h (cols 2) (cols 3) (hc.2.1 2 3 (by decide))
  have hone : entry h (.variable i s p a) (.variable d u q z) = true := by
    simpa only [matrix, ← hr, ← hmiddle] using (show matrix h (rows 2) (cols 2) = true from hc.2.2 2 2)
  have hzero : entry h (.variable i s p a) (.variable j t b w) = false := by
    simpa only [matrix, ← hr, ← hlast] using (show matrix h (rows 2) (cols 3) = false from hc.2.2 2 3)
  have hord := first_two_anchor_order_strict h rows cols hc l0 k0 g0 a0 l k 1 a1 hr0 hr1
  rcases unpinned_body_localizes h l k l0 k0 g0 b0 i p a d q z j b w s u t
    hv1.1 hlh hv1.2.1 hv0.1 hv0.2.1 hv0.2.2 vi vd vj rr cc hdiff co hone hzero hord hinc with
    ⟨hi,hsign,hj,ht,hb⟩
  subst i
  subst s
  subst j
  subst t
  subst b
  have hm : .variable h true p a ∈ axis false h := by rw [hr]; exact List.getElem_mem _
  have ha := leaf_tag_clone_zero false h true p a hm
  subst a
  exact ⟨p,w,hr.symm,hlast.symm⟩

/-- Every ordinary ordered H4 embedding in the actual host at every depth
localizes the fixed zero in pattern row 2, column 3 to the sparse set. -/
theorem all_copy_localization (h : Nat) (_hh : 1 ≤ h)
    (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    sparseZero h (rows 2) (cols 3) := by
  by_cases ha : Anchor (labelAt true h (cols 1))
  · exact canonical_copy_localization h rows cols hc ha
  · have hn : Nonanchor (labelAt true h (cols 1)) := by
      cases he : labelAt true h (cols 1) <;> simp_all [Anchor, Nonanchor]
    exact unpinned_copy_localization h rows cols hc hn

end OrderedMatrixRemoval4.Host
