import OrderedMatrixRemoval4.Traversal

namespace OrderedMatrixRemoval4.Host

theorem tree_depth_sign (column : Bool) (rem depth node j : Nat) (s : Bool) (q a : Nat)
    (hm : .variable j s q a ∈ tree column rem depth node) :
    j ≤ depth + rem ∧ (j = depth + rem → s = true) := by
  induction rem generalizing depth node with
  | zero =>
    have he := List.eq_of_mem_singleton hm
    cases he
    simp
  | succ rem ih =>
    simp only [tree, List.mem_append] at hm
    rcases hm with ((hm | hm) | hm) | hm
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨a, _, he⟩
      cases he
      constructor
      · omega
      · intro hbad; exact False.elim (by omega)
    · have ht := ih _ _ hm; constructor
      · omega
      · intro he; exact ht.2 (by omega)
    · have ht := ih _ _ hm; constructor
      · omega
      · intro he; exact ht.2 (by omega)
    · simp only [block, List.mem_map] at hm
      rcases hm with ⟨a, _, he⟩
      cases he
      constructor
      · omega
      · intro hbad; exact False.elim (by omega)

theorem variable_tag_valid (column : Bool) (h j : Nat) (s : Bool) (q a : Nat)
    (hm : .variable j s q a ∈ axis column h) : j ≤ h ∧ (j = h → s = true) := by
  rcases List.mem_append.mp hm with hm | hm
  · simp only [anchors, List.mem_map] at hm
    rcases hm with ⟨index, _, he⟩
    unfold anchorLabel at he
    contradiction
  · unfold nonanchors at hm
    cases column <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hm
    · rcases hm with ht | hd
      · simpa using tree_depth_sign false h 0 0 j s q a ht
      · simp only [dummies, List.mem_map] at hd
        rcases hd with ⟨_, _, he⟩; contradiction
    · rcases hm with hd | ht
      · simp only [dummies, List.mem_map] at hd
        rcases hd with ⟨_, _, he⟩; contradiction
      · simpa using tree_depth_sign true h 0 0 j s q a ht

/-- The containing graph: two signed paths and the terminal triangle. -/
def ClassEdge (h d e : Nat) (s t : Bool) : Prop :=
  (s = t ∧ (d + 1 = e ∨ e + 1 = d)) ∨
  (d + 1 = h ∧ e + 1 = h) ∨
  (d = h ∧ e + 1 = h) ∨ (e = h ∧ d + 1 = h)

theorem class_triangle_terminal (h d e f : Nat) (s t u : Bool)
    (hde : d ≠ e ∨ s ≠ t) (hef : e ≠ f ∨ t ≠ u) (hdf : d ≠ f ∨ s ≠ u)
    (hd : d ≤ h) (he : e ≤ h) (hf : f ≤ h)
    (hs : d = h → s = true) (ht : e = h → t = true) (hu : f = h → u = true)
    (h01 : ClassEdge h d e s t) (h12 : ClassEdge h e f t u)
    (h02 : ClassEdge h d f s u) :
    (d = h ∨ d + 1 = h) ∧ (e = h ∨ e + 1 = h) ∧ (f = h ∨ f + 1 = h) := by
  cases s <;> cases t <;> cases u <;> simp_all [ClassEdge] <;> omega

def Supports (h i j : Nat) (s t : Bool) : Prop :=
  (i = j ∨ i = j + 1) ∧ (s = t ∨ i = h)

theorem entry_support (h i j p q a b : Nat) (s t : Bool)
    (_hr : i ≤ h) (_hc : j ≤ h) (hs : i = h → s = true) (ht : j = h → t = true)
    (he : entry h (.variable i s p a) (.variable j t q b) = true) :
    Supports h i j s t := by
  cases s <;> cases t <;> simp_all [entry, signed, Supports] <;> omega

theorem support_pair_edge (h i d e : Nat) (r s t : Bool)
    (hi : i ≤ h) (hd : d ≤ h) (he : e ≤ h)
    (hs : d = h → s = true) (ht : e = h → t = true)
    (hdiff : d ≠ e ∨ s ≠ t)
    (h0 : Supports h i d r s) (h1 : Supports h i e r t) : ClassEdge h d e s t := by
  cases r <;> cases s <;> cases t <;> simp_all [Supports, ClassEdge] <;> omega

theorem terminal_pair_forces_leaf (h i d e : Nat) (r s t : Bool)
    (hi : i ≤ h) (hd : d = h ∨ d + 1 = h) (he : e = h ∨ e + 1 = h)
    (hdiff : d ≠ e ∨ s ≠ t)
    (h0 : Supports h i d r s) (h1 : Supports h i e r t) : i = h := by
  cases r <;> cases s <;> cases t <;> simp_all [Supports] <;> omega

theorem crown_columns_distinct_classes (h : Nat) (rows : Fin 3 → Position)
    (cd cn ca : Fin 3 → Nat) (cs : Fin 3 → Bool)
    (hr : ∀ i, Nonanchor (rows i))
    (hm : ∀ i j, entry h (rows i) (.variable (cd j) (cs j) (cn j) (ca j)) = decide (i ≠ j)) :
    ∀ i j, i ≠ j → cd i ≠ cd j ∨ cs i ≠ cs j := by
  intro i j hij
  by_cases hd : cd i = cd j
  · by_cases hs : cs i = cs j
    · have hji : j ≠ i := fun he => hij he.symm
      rcases Nat.le_total (cn i) (cn j) with hle | hle
      · have he : entry h (rows j) (.variable (cd j) (cs j) (cn i) (ca i)) = true := by
          simpa only [hd, hs] using (hm j i).trans (decide_eq_true_iff.mpr hji)
        have ht := variable_column_nested h (cd j) (cs j) (cn i) (cn j) (ca i) (ca j)
          hle (rows j) (hr j) he
        rw [hm j j] at ht
        simp at ht
      · have he : entry h (rows i) (.variable (cd i) (cs i) (cn j) (ca j)) = true := by
          simpa only [← hd, ← hs] using (hm i j).trans (decide_eq_true_iff.mpr hij)
        have ht := variable_column_nested h (cd i) (cs i) (cn j) (cn i) (ca j) (ca i)
          hle (rows i) (hr i) he
        rw [hm i i] at ht
        simp at ht
    · exact Or.inr hs
  · exact Or.inl hd

theorem no_variable_crown (h : Nat) (rd rn ra cd cn ca : Fin 3 → Nat)
    (rs cs : Fin 3 → Bool)
    (hr : ∀ i, rd i ≤ h ∧ (rd i = h → rs i = true))
    (hc : ∀ i, cd i ≤ h ∧ (cd i = h → cs i = true))
    (hm : ∀ i j, entry h (.variable (rd i) (rs i) (rn i) (ra i))
      (.variable (cd j) (cs j) (cn j) (ca j)) = decide (i ≠ j)) : False := by
  have hd := crown_columns_distinct_classes h
    (fun i => .variable (rd i) (rs i) (rn i) (ra i)) cd cn ca cs (fun _ => trivial) hm
  have hd01 := hd 0 1 (by decide)
  have hd12 := hd 1 2 (by decide)
  have hd02 := hd 0 2 (by decide)
  have support : ∀ i j : Fin 3, i ≠ j → Supports h (rd i) (cd j) (rs i) (cs j) := by
    intro i j hij
    apply entry_support h (rd i) (cd j) (rn i) (cn j) (ra i) (ca j) (rs i) (cs j)
      (hr i).1 (hc j).1 (hr i).2 (hc j).2
    exact (hm i j).trans (decide_eq_true_iff.mpr hij)
  have h01 := support_pair_edge h (rd 2) (cd 0) (cd 1) (rs 2) (cs 0) (cs 1)
    (hr 2).1 (hc 0).1 (hc 1).1 (hc 0).2 (hc 1).2 hd01
    (support 2 0 (by decide)) (support 2 1 (by decide))
  have h12 := support_pair_edge h (rd 0) (cd 1) (cd 2) (rs 0) (cs 1) (cs 2)
    (hr 0).1 (hc 1).1 (hc 2).1 (hc 1).2 (hc 2).2 hd12
    (support 0 1 (by decide)) (support 0 2 (by decide))
  have h02 := support_pair_edge h (rd 1) (cd 0) (cd 2) (rs 1) (cs 0) (cs 2)
    (hr 1).1 (hc 0).1 (hc 2).1 (hc 0).2 (hc 2).2 hd02
    (support 1 0 (by decide)) (support 1 2 (by decide))
  have ht := class_triangle_terminal h (cd 0) (cd 1) (cd 2) (cs 0) (cs 1) (cs 2)
    hd01 hd12 hd02 (hc 0).1 (hc 1).1 (hc 2).1 (hc 0).2 (hc 1).2 (hc 2).2 h01 h12 h02
  have hleaf0 := terminal_pair_forces_leaf h (rd 0) (cd 1) (cd 2) (rs 0) (cs 1) (cs 2)
    (hr 0).1 ht.2.1 ht.2.2 hd12 (support 0 1 (by decide)) (support 0 2 (by decide))
  have hleaf1 := terminal_pair_forces_leaf h (rd 1) (cd 0) (cd 2) (rs 1) (cs 0) (cs 2)
    (hr 1).1 ht.1 ht.2.2 hd02 (support 1 0 (by decide)) (support 1 2 (by decide))
  have hs0 := (hr 0).2 hleaf0
  have hs1 := (hr 1).2 hleaf1
  rcases Nat.le_total (rn 0) (rn 1) with hle | hle
  · have he := hm 1 0
    simp only [hleaf1, hs1] at he
    have hn := variable_row_nested h h true (rn 0) (rn 1) (ra 0) (ra 1) hle
      (.variable (cd 0) (cs 0) (cn 0) (ca 0)) (by trivial) he
    have hz := hm 0 0
    simp only [hleaf0, hs0] at hz
    rw [hz] at hn
    contradiction
  · have he := hm 0 1
    simp only [hleaf0, hs0] at he
    have hn := variable_row_nested h h true (rn 1) (rn 0) (ra 1) (ra 0) hle
      (.variable (cd 1) (cs 1) (cn 1) (ca 1)) (by trivial) he
    have hz := hm 1 1
    simp only [hleaf1, hs1] at hz
    rw [hz] at hn
    contradiction

structure VariableData where
  depth : Nat
  plus : Bool
  node : Nat
  clone : Nat

def VariableData.position (v : VariableData) : Position :=
  .variable v.depth v.plus v.node v.clone

theorem variable_data_exists (p : Position) (hp : IsVariable p) :
    ∃ v : VariableData, v.position = p := by
  cases p with
  | anchor => contradiction
  | dummy => contradiction
  | «variable» d s q a => exact ⟨⟨d, s, q, a⟩, rfl⟩

theorem zero_nonanchors_variable (h : Nat) (r c : Position)
    (hr : Nonanchor r) (hc : Nonanchor c) (he : entry h r c = false) :
    IsVariable r ∧ IsVariable c := by
  cases r <;> cases c <;> simp_all [Nonanchor, IsVariable, entry]

/-- No permuted 3-crown in the actual nonanchor host, at every depth.
No ordering assumption on these six positions is needed. -/
theorem nonanchor_crown_exclusion (h : Nat) (rows cols : Fin 3 → Fin (size h))
    (hr : ∀ i, Nonanchor (labelAt false h (rows i)))
    (hc : ∀ i, Nonanchor (labelAt true h (cols i)))
    (hm : ∀ i j, matrix h (rows i) (cols j) = decide (i ≠ j)) : False := by
  have hv : ∀ i, IsVariable (labelAt false h (rows i)) ∧
      IsVariable (labelAt true h (cols i)) := by
    intro i
    apply zero_nonanchors_variable h _ _ (hr i) (hc i)
    simpa [matrix] using hm i i
  have hrd := fun i => variable_data_exists _ (hv i).1
  have hcd := fun i => variable_data_exists _ (hv i).2
  let rr := fun i => Classical.choose (hrd i)
  let cc := fun i => Classical.choose (hcd i)
  have her : ∀ i, (rr i).position = labelAt false h (rows i) :=
    fun i => Classical.choose_spec (hrd i)
  have hec : ∀ i, (cc i).position = labelAt true h (cols i) :=
    fun i => Classical.choose_spec (hcd i)
  apply no_variable_crown h (fun i => (rr i).depth) (fun i => (rr i).node)
    (fun i => (rr i).clone) (fun i => (cc i).depth) (fun i => (cc i).node)
    (fun i => (cc i).clone) (fun i => (rr i).plus) (fun i => (cc i).plus)
  · intro i
    apply variable_tag_valid false h
    rw [← VariableData.position, her i]
    exact List.getElem_mem _
  · intro i
    apply variable_tag_valid true h
    rw [← VariableData.position, hec i]
    exact List.getElem_mem _
  · intro i j
    change entry h (rr i).position (cc j).position = _
    rw [her i, hec j]
    exact hm i j

end OrderedMatrixRemoval4.Host
