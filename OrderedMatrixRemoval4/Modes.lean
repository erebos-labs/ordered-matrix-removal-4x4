import OrderedMatrixRemoval4.Shape
import OrderedMatrixRemoval4.GeneralOrder

namespace OrderedMatrixRemoval4.Host

theorem anchor_index_level_bound (column : Bool) (h : Nat) (x : Fin (size h))
    (l k g a : Nat) (hx : labelAt column h x = .anchor l k g a) : l ≤ h := by
  have hv := anchor_index_valid column h x l k g a hx
  have hi := anchor_index_lt column h x l k g a hx
  rw [anchors_length] at hi
  have hq : x.val / 2 ^ h < 12 * h :=
    (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).mpr hi
  have ho := anchor_index_ordinal column h x l k g a hx
  unfold anchorRank at ho
  omega

def CanonicalFrame (h : Nat) (rows cols : Fin 4 → Fin (size h)) : Prop :=
  ∃ l k a0 a1 b0 b1,
    1 ≤ l ∧ l ≤ h ∧ k < 6 ∧
    labelAt false h (rows 0) = .anchor l k 0 a0 ∧
    labelAt false h (rows 1) = .anchor l k 1 a1 ∧
    labelAt true h (cols 0) = .anchor l k 0 b0 ∧
    labelAt true h (cols 1) = .anchor l k 1 b1 ∧
    rowRole h l k 0 (labelAt false h (rows 2)) ∧
    rowRole h l k 1 (labelAt false h (rows 3)) ∧
    columnRole h l k 0 (labelAt true h (cols 2)) ∧
    columnRole h l k 1 (labelAt true h (cols 3))

theorem canonical_frame_of_copy (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : Copy h rows cols) (hc1 : Anchor (labelAt true h (cols 1))) : CanonicalFrame h rows cols := by
  have hshape := copy_anchor_shape h rows cols hc
  rcases anchor_exists _ hshape.1 with ⟨u,v,w,a0,hr0⟩
  rcases anchor_exists _ hshape.2.1 with ⟨l,k,g,a1,hr1⟩
  rcases anchor_exists _ hshape.2.2.2.2.1 with ⟨j,t,z,b0,hc0⟩
  rcases anchor_exists _ hc1 with ⟨j',t',z',b1,hc1'⟩
  have hgroups := second_row_first_column_groups h rows cols hc l k g a1 j t z b0 hr1 hc0
  rcases hgroups with ⟨hlj,hkt,hg,hz⟩
  subst j
  subst t
  subst g
  subst z
  have hv0 := anchor_index_valid false h (rows 0) u v w a0 hr0
  have hvc := anchor_index_valid true h (cols 1) j' t' z' b1 hc1'
  have hrord := first_two_anchor_order_strict h rows cols hc u v w a0 l k 1 a1 hr0 hr1
  have hcord := anchor_order_le true h (cols 0) (cols 1) l k 0 b0 j' t' z' b1
    hc0 hc1' (hc.2.1 0 1 (by decide))
  have hbit : matrix h (rows 0) (cols 1) = true := hc.2.2 0 1
  simp only [matrix, hr0, hc1', entry, decide_eq_true_eq] at hbit
  have hvl := anchor_index_valid false h (rows 1) l k 1 a1 hr1
  have heq : u = l ∧ v = k ∧ w = 0 ∧ j' = l ∧ t' = k ∧ z' = 1 := by
    unfold anchorRank at hrord hcord
    omega
  rcases heq with ⟨hu,hv,hw,hj,ht,hz⟩
  subst u
  subst v
  subst w
  subst j'
  subst t'
  subst z'
  refine ⟨l,k,a0,a1,b0,b1,hvl.1,anchor_index_level_bound false h (rows 1) l k 1 a1 hr1,
    hvl.2.1,hr0,hr1,hc0,hc1',?_,?_,?_,?_⟩
  · have he : entry h (labelAt false h (rows 2)) (.anchor l k 0 b0) = true := by
      simpa only [matrix, hc0] using (show matrix h (rows 2) (cols 0) = true from hc.2.2 2 0)
    exact nonanchor_row_role_of_entry h l k 0 b0 _ hshape.2.2.1 he
  · have he : entry h (labelAt false h (rows 3)) (.anchor l k 1 b1) = true := by
      simpa only [matrix, hc1'] using (show matrix h (rows 3) (cols 1) = true from hc.2.2 3 1)
    exact nonanchor_row_role_of_entry h l k 1 b1 _ hshape.2.2.2.1 he
  · have he : entry h (.anchor l k 0 a0) (labelAt true h (cols 2)) = true := by
      simpa only [matrix, hr0] using (show matrix h (rows 0) (cols 2) = true from hc.2.2 0 2)
    exact nonanchor_column_role_of_entry h l k 0 a0 _ hshape.2.2.2.2.2.1 he
  · have he : entry h (.anchor l k 1 a1) (labelAt true h (cols 3)) = true := by
      simpa only [matrix, hr1] using (show matrix h (rows 1) (cols 3) = true from hc.2.2 1 3)
    exact nonanchor_column_role_of_entry h l k 1 a1 _ hshape.2.2.2.2.2.2 he

end OrderedMatrixRemoval4.Host
