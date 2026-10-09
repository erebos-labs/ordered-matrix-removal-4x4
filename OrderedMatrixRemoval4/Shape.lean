import OrderedMatrixRemoval4.Classes
import OrderedMatrixRemoval4.Embedding

namespace OrderedMatrixRemoval4.Host

def Anchor : Position → Prop
  | .anchor .. => True
  | _ => False

instance (p : Position) : Decidable (Anchor p) := by cases p <;> unfold Anchor <;> infer_instance
instance (p : Position) : Decidable (Nonanchor p) := by cases p <;> unfold Nonanchor <;> infer_instance

theorem anchor_exists (p : Position) (hp : Anchor p) :
    ∃ l k g a, p = .anchor l k g a := by
  cases p with
  | anchor l k g a => exact ⟨l,k,g,a,rfl⟩
  | dummy => contradiction
  | «variable» => contradiction

theorem anchor_iff_not_nonanchor (p : Position) : Anchor p ↔ ¬ Nonanchor p := by
  cases p <;> simp [Anchor, Nonanchor]

theorem anchor_of_index_lt (column : Bool) (h : Nat) (j : Fin (size h))
    (hj : j.val < (anchors h).length) : Anchor (labelAt column h j) := by
  rw [labelAt_append, List.getElem_append_left hj]
  simp only [anchors, List.getElem_map, List.getElem_range, anchorLabel, Anchor]

theorem anchor_iff_index_lt (column : Bool) (h : Nat) (j : Fin (size h)) :
    Anchor (labelAt column h j) ↔ j.val < (anchors h).length := by
  constructor
  · intro ha
    rcases anchor_exists _ ha with ⟨l,k,g,a,he⟩
    exact anchor_index_lt column h j l k g a he
  · exact anchor_of_index_lt column h j

theorem nonanchor_later (column : Bool) (h : Nat) (x y : Fin (size h))
    (hxy : x.val < y.val) (hx : Nonanchor (labelAt column h x)) :
    Nonanchor (labelAt column h y) := by
  by_cases hy : Anchor (labelAt column h y)
  · have hj := (anchor_iff_index_lt column h y).mp hy
    have hxi := anchor_of_index_lt column h x (by omega)
    exact False.elim ((anchor_iff_not_nonanchor _).mp hxi hx)
  · cases he : labelAt column h y <;> simp_all [Anchor, Nonanchor]

theorem anchor_column_connects (h : Nat) (x y c : Fin (size h))
    (ha : Anchor (labelAt true h c))
    (hx : Nonanchor (labelAt false h x)) (hy : Nonanchor (labelAt false h y))
    (h0 : matrix h x c = true) (h1 : matrix h y c = true) :
    SameClass (labelAt false h x) (labelAt false h y) := by
  rcases anchor_exists _ ha with ⟨l,k,g,a,he⟩
  apply row_role_same_class h l k g _ _ (labelAt_valid false h x) (labelAt_valid false h y)
  · have hbit : entry h (labelAt false h x) (.anchor l k g a) = true := by
      simpa only [matrix, he] using h0
    cases hp : labelAt false h x <;> simp_all [Nonanchor, entry] 
  · have hbit : entry h (labelAt false h y) (.anchor l k g a) = true := by
      simpa only [matrix, he] using h1
    cases hp : labelAt false h y <;> simp_all [Nonanchor, entry]

theorem anchor_row_connects (h : Nat) (r x y : Fin (size h))
    (ha : Anchor (labelAt false h r))
    (hx : Nonanchor (labelAt true h x)) (hy : Nonanchor (labelAt true h y))
    (h0 : matrix h r x = true) (h1 : matrix h r y = true) :
    SameClass (labelAt true h x) (labelAt true h y) := by
  rcases anchor_exists _ ha with ⟨l,k,g,a,he⟩
  apply column_role_same_class h l k g _ _ (labelAt_valid true h x) (labelAt_valid true h y)
  · have hbit : entry h (.anchor l k g a) (labelAt true h x) = true := by
      simpa only [matrix, he] using h0
    cases hp : labelAt true h x <;> simp_all [Nonanchor, entry]
  · have hbit : entry h (.anchor l k g a) (labelAt true h y) = true := by
      simpa only [matrix, he] using h1
    cases hp : labelAt true h y <;> simp_all [Nonanchor, entry]

/-- Every ordinary H4 copy has at least two anchor rows. -/
theorem second_row_anchor (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Anchor (labelAt false h (rows 1)) := by
  by_cases ha : Anchor (labelAt false h (rows 1))
  · exact ha
  · have hn1 : Nonanchor (labelAt false h (rows 1)) := by
      cases he : labelAt false h (rows 1) <;> simp_all [Anchor, Nonanchor]
    have hn2 := nonanchor_later false h (rows 1) (rows 2) (hc.1 1 2 (by decide)) hn1
    have hn3 := nonanchor_later false h (rows 1) (rows 3) (hc.1 1 3 (by decide)) hn1
    by_cases hb0 : Anchor (labelAt true h (cols 0))
    · have hs12 := anchor_column_connects h (rows 1) (rows 2) (cols 0) hb0 hn1 hn2 (hc.2.2 1 0) (hc.2.2 2 0)
      by_cases hb2 : Anchor (labelAt true h (cols 2))
      · have hs23 := anchor_column_connects h (rows 2) (rows 3) (cols 2) hb2 hn2 hn3 (hc.2.2 2 2) (hc.2.2 3 2)
        have hs13 := sameClass_trans _ _ _ hs12 hs23
        have ht := same_class_three_row_signatures h _ _ _ hs12 hs13 hs23
        rcases anchor_exists _ hb0 with ⟨l0,k0,g0,a0,he0⟩
        rcases anchor_exists _ hb2 with ⟨l2,k2,g2,a2,he2⟩
        rcases ht with ht | ht | ht
        · have he := ht l2 k2 g2 a2
          have hm1 := hc.2.2 1 2
          have hm2 := hc.2.2 2 2
          simp only [matrix, he2] at hm1 hm2
          rw [hm1, hm2] at he
          contradiction
        · have he := ht l0 k0 g0 a0
          have hm1 := hc.2.2 1 0
          have hm3 := hc.2.2 3 0
          simp only [matrix, he0] at hm1 hm3
          rw [hm1, hm3] at he
          contradiction
        · have he := ht l0 k0 g0 a0
          have hm2 := hc.2.2 2 0
          have hm3 := hc.2.2 3 0
          simp only [matrix, he0] at hm2 hm3
          rw [hm2, hm3] at he
          contradiction
      · have hncol2 : Nonanchor (labelAt true h (cols 2)) := by
          cases he : labelAt true h (cols 2) <;> simp_all [Anchor, Nonanchor]
        have hncol3 := nonanchor_later true h (cols 2) (cols 3) (hc.2.1 2 3 (by decide)) hncol2
        exact False.elim (same_class_rows_no_cross h _ _ _ _ hs12 hncol3 hncol2
          (hc.2.2 1 3) (hc.2.2 2 3) (hc.2.2 1 2) (hc.2.2 2 2))
    · have hncol0 : Nonanchor (labelAt true h (cols 0)) := by
        cases he : labelAt true h (cols 0) <;> simp_all [Anchor, Nonanchor]
      have hcols : ∀ i : Fin 4, Nonanchor (labelAt true h (cols i)) := by
        intro i
        by_cases hi : i = 0
        · simpa [hi] using hncol0
        · exact nonanchor_later true h (cols 0) (cols i) (hc.2.1 0 i (by omega)) hncol0
      let rr : Fin 3 → Fin 4 := fun i => ⟨i.val + 1, by omega⟩
      let cc : Fin 3 → Fin 4 := fun i =>
        if i = 0 then 2 else if i = 1 then 3 else 0
      apply False.elim
      apply nonanchor_crown_exclusion h (fun i => rows (rr i)) (fun i => cols (cc i))
      · intro i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl
        · exact hn1
        · exact hn2
        · exact hn3
      · intro i; exact hcols _
      · intro i j
        have hm := hc.2.2 (rr i) (cc j)
        have hpattern : H4 (rr i) (cc j) = decide (i ≠ j) := by
          have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
          rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> decide
        exact hm.trans hpattern

theorem first_row_anchor (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Anchor (labelAt false h (rows 0)) := by
  have h1 := (anchor_iff_index_lt false h (rows 1)).mp (second_row_anchor h rows cols hc)
  apply anchor_of_index_lt
  have hi := hc.1 0 1 (by decide)
  omega

theorem first_column_anchor (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Anchor (labelAt true h (cols 0)) := by
  by_cases ha : Anchor (labelAt true h (cols 0))
  · exact ha
  have hn0 : Nonanchor (labelAt true h (cols 0)) := by
    cases he : labelAt true h (cols 0) <;> simp_all [Anchor, Nonanchor]
  have hncols : ∀ i : Fin 4, Nonanchor (labelAt true h (cols i)) := by
    intro i
    by_cases hi : i = 0
    · simpa [hi] using hn0
    · exact nonanchor_later true h (cols 0) (cols i) (hc.2.1 0 i (by omega)) hn0
  have hr0 := first_row_anchor h rows cols hc
  have hr1 := second_row_anchor h rows cols hc
  by_cases hr2 : Anchor (labelAt false h (rows 2))
  · have h12 := anchor_row_connects h (rows 0) (cols 1) (cols 2) hr0
      (hncols 1) (hncols 2) (hc.2.2 0 1) (hc.2.2 0 2)
    have h02 := anchor_row_connects h (rows 2) (cols 0) (cols 2) hr2
      (hncols 0) (hncols 2) (hc.2.2 2 0) (hc.2.2 2 2)
    have h01 := sameClass_trans _ _ _ h02 (sameClass_symm _ _ h12)
    have ht := same_class_three_column_signatures h _ _ _ h01 h02 h12
    rcases anchor_exists _ hr0 with ⟨l0,k0,g0,a0,he0⟩
    rcases anchor_exists _ hr2 with ⟨l2,k2,g2,a2,he2⟩
    apply False.elim
    rcases ht with ht | ht | ht
    · have he := ht l0 k0 g0 a0
      have hm0 := hc.2.2 0 0
      have hm1 := hc.2.2 0 1
      simp only [matrix, he0] at hm0 hm1
      rw [hm0, hm1] at he
      contradiction
    · have he := ht l0 k0 g0 a0
      have hm0 := hc.2.2 0 0
      have hm2 := hc.2.2 0 2
      simp only [matrix, he0] at hm0 hm2
      rw [hm0, hm2] at he
      contradiction
    · have he := ht l2 k2 g2 a2
      have hm1 := hc.2.2 2 1
      have hm2 := hc.2.2 2 2
      simp only [matrix, he2] at hm1 hm2
      rw [hm1, hm2] at he
      contradiction
  · have hn2 : Nonanchor (labelAt false h (rows 2)) := by
      cases he : labelAt false h (rows 2) <;> simp_all [Anchor, Nonanchor]
    have hn3 := nonanchor_later false h (rows 2) (rows 3) (hc.1 2 3 (by decide)) hn2
    have hclass := anchor_row_connects h (rows 1) (cols 0) (cols 3) hr1
      (hncols 0) (hncols 3) (hc.2.2 1 0) (hc.2.2 1 3)
    exact False.elim (same_class_columns_no_cross h _ _ _ _ hclass hn2 hn3
      (hc.2.2 2 0) (hc.2.2 2 3) (hc.2.2 3 0) (hc.2.2 3 3))

theorem anchor_rows_common_one_twins (h : Nat) (x y c : Fin (size h))
    (hx : Anchor (labelAt false h x)) (hy : Anchor (labelAt false h y))
    (hc : Anchor (labelAt true h c)) (h0 : matrix h x c = true) (h1 : matrix h y c = true) :
    ∀ z, matrix h x z = matrix h y z := by
  rcases anchor_exists _ hx with ⟨l,k,g,a,he0⟩
  rcases anchor_exists _ hy with ⟨l',k',g',a',he1⟩
  rcases anchor_exists _ hc with ⟨u,v,w,b,hec⟩
  have hv0 := anchor_index_valid false h x l k g a he0
  have hv1 := anchor_index_valid false h y l' k' g' a' he1
  have hvc := anchor_index_valid true h c u v w b hec
  simp only [matrix, he0, he1, hec, entry, decide_eq_true_eq] at h0 h1
  have heq : l = l' ∧ k = k' ∧ g = g' := by omega
  rcases heq with ⟨rfl,rfl,rfl⟩
  intro z
  simp only [matrix, he0, he1]
  exact anchor_row_twins ..

theorem anchor_columns_common_one_twins (h : Nat) (r x y : Fin (size h))
    (hr : Anchor (labelAt false h r)) (hx : Anchor (labelAt true h x))
    (hy : Anchor (labelAt true h y)) (h0 : matrix h r x = true) (h1 : matrix h r y = true) :
    ∀ z, matrix h z x = matrix h z y := by
  rcases anchor_exists _ hx with ⟨l,k,g,a,he0⟩
  rcases anchor_exists _ hy with ⟨l',k',g',a',he1⟩
  rcases anchor_exists _ hr with ⟨u,v,w,b,her⟩
  have hv0 := anchor_index_valid true h x l k g a he0
  have hv1 := anchor_index_valid true h y l' k' g' a' he1
  have hvr := anchor_index_valid false h r u v w b her
  simp only [matrix, he0, he1, her, entry, decide_eq_true_eq] at h0 h1
  have heq : l = l' ∧ k = k' ∧ g = g' := by omega
  rcases heq with ⟨rfl,rfl,rfl⟩
  intro z
  simp only [matrix, he0, he1]
  exact anchor_column_twins ..

theorem third_row_nonanchor (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Nonanchor (labelAt false h (rows 2)) := by
  by_cases ha : Anchor (labelAt false h (rows 2))
  · have ht := anchor_rows_common_one_twins h (rows 1) (rows 2) (cols 0)
      (second_row_anchor h rows cols hc) ha (first_column_anchor h rows cols hc)
      (hc.2.2 1 0) (hc.2.2 2 0) (cols 3)
    rw [hc.2.2 1 3, hc.2.2 2 3] at ht
    contradiction
  · cases he : labelAt false h (rows 2) <;> simp_all [Anchor, Nonanchor]

theorem third_column_nonanchor (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Nonanchor (labelAt true h (cols 2)) := by
  by_cases ha : Anchor (labelAt true h (cols 2))
  · have hj := (anchor_iff_index_lt true h (cols 2)).mp ha
    have hinc := hc.2.1 1 2 (by decide)
    have ha1 := anchor_of_index_lt true h (cols 1) (by omega)
    have ht := anchor_columns_common_one_twins h (rows 0) (cols 1) (cols 2)
      (first_row_anchor h rows cols hc) ha1 ha (hc.2.2 0 1) (hc.2.2 0 2) (rows 2)
    rw [hc.2.2 2 1, hc.2.2 2 2] at ht
    contradiction
  · cases he : labelAt true h (cols 2) <;> simp_all [Anchor, Nonanchor]

/-- Complete anchor-count reduction for every ordinary copy: exactly two row
anchors, and either one or two column anchors. No shape hypothesis is assumed. -/
theorem copy_anchor_shape (h : Nat) (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    Anchor (labelAt false h (rows 0)) ∧ Anchor (labelAt false h (rows 1)) ∧
    Nonanchor (labelAt false h (rows 2)) ∧ Nonanchor (labelAt false h (rows 3)) ∧
    Anchor (labelAt true h (cols 0)) ∧ Nonanchor (labelAt true h (cols 2)) ∧
    Nonanchor (labelAt true h (cols 3)) := by
  have hr2 := third_row_nonanchor h rows cols hc
  have hc2 := third_column_nonanchor h rows cols hc
  exact ⟨first_row_anchor h rows cols hc, second_row_anchor h rows cols hc, hr2,
    nonanchor_later false h (rows 2) (rows 3) (hc.1 2 3 (by decide)) hr2,
    first_column_anchor h rows cols hc, hc2,
    nonanchor_later true h (cols 2) (cols 3) (hc.2.1 2 3 (by decide)) hc2⟩

theorem nonanchor_row_role_of_entry (h l k g a : Nat) (r : Position)
    (hr : Nonanchor r) (he : entry h r (.anchor l k g a) = true) : rowRole h l k g r := by
  cases r <;> simp_all [Nonanchor, entry]

theorem nonanchor_column_role_of_entry (h l k g a : Nat) (c : Position)
    (hc : Nonanchor c) (he : entry h (.anchor l k g a) c = true) : columnRole h l k g c := by
  cases c <;> simp_all [Nonanchor, entry]

theorem reversed_body_roles_one (h l k : Nat) (r c : Position)
    (hr : rowRole h l k 1 r) (hc : columnRole h l k 0 c) : entry h r c = true := by
  cases r <;> cases c <;> simp_all [rowRole, columnRole, entry] <;> omega

/-- The first anchor column is group one, and the second anchor row group two,
in one common mode. This is derived for every ordinary copy. -/
theorem second_row_first_column_groups (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : Copy h rows cols) (l k g a u v w b : Nat)
    (hr1 : labelAt false h (rows 1) = .anchor l k g a)
    (hc0 : labelAt true h (cols 0) = .anchor u v w b) :
    l = u ∧ k = v ∧ g = 1 ∧ w = 0 := by
  have hvg := (anchor_index_valid false h (rows 1) l k g a hr1).2.2
  have hvw := (anchor_index_valid true h (cols 0) u v w b hc0).2.2
  have hm : matrix h (rows 1) (cols 0) = true := hc.2.2 1 0
  simp only [matrix, hr1, hc0, entry, decide_eq_true_eq] at hm
  have hlu := hm.1
  have hkv := hm.2.1
  subst u
  subst v
  by_cases hw : w = 0
  · exact ⟨rfl,rfl,by omega,hw⟩
  · have hw1 : w = 1 := by omega
    have hg0 : g = 0 := by omega
    subst w
    subst g
    have hshape := copy_anchor_shape h rows cols hc
    have hrbit := hc.2.2 2 0
    have hcbit := hc.2.2 1 3
    simp only [matrix, hr1, hc0] at hrbit hcbit
    have hrr := nonanchor_row_role_of_entry h l k 1 b _ hshape.2.2.1 hrbit
    have hcc := nonanchor_column_role_of_entry h l k 0 a _ hshape.2.2.2.2.2.2 hcbit
    have hone := reversed_body_roles_one h l k _ _ hrr hcc
    have hzero := hc.2.2 2 3
    change entry h (labelAt false h (rows 2)) (labelAt true h (cols 3)) = false at hzero
    rw [hzero] at hone
    contradiction

end OrderedMatrixRemoval4.Host
