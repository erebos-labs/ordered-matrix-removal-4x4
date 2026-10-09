import OrderedMatrixRemoval4.Sparse
import OrderedMatrixRemoval4.SelectionFamily

/- Terminal-anchor repair extension to the pinned host.
   Ordinary argument: paper/terminal-anchor-proof.md. All indices and edits are physical. -/
namespace OrderedMatrixRemoval4.Host
namespace TerminalAnchorRepair

def TerminalColumn (h : Nat) : Position → Prop
  | .anchor l k g _ => l = h ∧ (k = 4 ∨ k = 5) ∧ g = 0
  | _ => False

instance (h : Nat) (p : Position) : Decidable (TerminalColumn h p) := by
  cases p <;> unfold TerminalColumn <;> infer_instance

def matrix (h : Nat) : BinaryMatrix (size h) := fun r c =>
  if TerminalColumn h (labelAt true h c) ∧ Nonanchor (labelAt false h r)
  then false else Host.matrix h r c

theorem anchor_agreement (h : Nat) (r c : Fin (size h))
    (hr : Anchor (labelAt false h r)) : matrix h r c = Host.matrix h r c := by
  have hn := (anchor_iff_not_nonanchor _).mp hr
  simp [matrix,hn]

theorem outside_agreement (h : Nat) (r c : Fin (size h))
    (hc : ¬ TerminalColumn h (labelAt true h c)) :
    matrix h r c = Host.matrix h r c := by simp [matrix,hc]

theorem terminal_nonanchor_zero (h : Nat) (r c : Fin (size h))
    (hr : Nonanchor (labelAt false h r)) (hc : TerminalColumn h (labelAt true h c)) :
    matrix h r c = false := by simp [matrix,hr,hc]

theorem third_row_nonanchor_of_anchor_agreement (h : Nat)
    (B : BinaryMatrix (size h))
    (hag : ∀ r c, Anchor (labelAt false h r) → B r c = Host.matrix h r c)
    (rows cols : Fin 4 → Fin (size h)) (hc : OrderedCopy H4 B rows cols) :
    Nonanchor (labelAt false h (rows 2)) := by
  by_cases hr2 : Anchor (labelAt false h (rows 2))
  · have hi2 := (anchor_iff_index_lt false h (rows 2)).mp hr2
    have hr0 : Anchor (labelAt false h (rows 0)) :=
      anchor_of_index_lt false h (rows 0) (by have ho := hc.1 0 2 (by decide); omega)
    have hr1 : Anchor (labelAt false h (rows 1)) :=
      anchor_of_index_lt false h (rows 1) (by have ho := hc.1 1 2 (by decide); omega)
    have bit0 : ∀ j, Host.matrix h (rows 0) (cols j) = H4 0 j := by
      intro j; rw [← hag _ _ hr0]; exact hc.2.2 0 j
    have bit1 : ∀ j, Host.matrix h (rows 1) (cols j) = H4 1 j := by
      intro j; rw [← hag _ _ hr1]; exact hc.2.2 1 j
    have bit2 : ∀ j, Host.matrix h (rows 2) (cols j) = H4 2 j := by
      intro j; rw [← hag _ _ hr2]; exact hc.2.2 2 j
    apply False.elim
    by_cases hc0 : Anchor (labelAt true h (cols 0))
    · have ht := anchor_rows_common_one_twins h (rows 1) (rows 2) (cols 0)
        hr1 hr2 hc0 (bit1 0) (bit2 0) (cols 3)
      rw [bit1 3,bit2 3] at ht
      contradiction
    · have hn0 : Nonanchor (labelAt true h (cols 0)) := by
        cases he : labelAt true h (cols 0) <;> simp_all [Anchor,Nonanchor]
      have hn1 := nonanchor_later true h (cols 0) (cols 1) (hc.2.1 0 1 (by decide)) hn0
      have hn2 := nonanchor_later true h (cols 0) (cols 2) (hc.2.1 0 2 (by decide)) hn0
      have h12 := anchor_row_connects h (rows 0) (cols 1) (cols 2) hr0 hn1 hn2 (bit0 1) (bit0 2)
      have h02 := anchor_row_connects h (rows 2) (cols 0) (cols 2) hr2 hn0 hn2 (bit2 0) (bit2 2)
      have h01 := sameClass_trans _ _ _ h02 (sameClass_symm _ _ h12)
      have ht := same_class_three_column_signatures h _ _ _ h01 h02 h12
      rcases anchor_exists _ hr0 with ⟨l0,k0,g0,a0,he0⟩
      rcases anchor_exists _ hr2 with ⟨l2,k2,g2,a2,he2⟩
      rcases ht with ht | ht | ht
      · have he := ht l0 k0 g0 a0
        have hm0 := bit0 0; have hm1 := bit0 1
        simp only [Host.matrix,he0] at hm0 hm1
        rw [hm0,hm1] at he
        contradiction
      · have he := ht l0 k0 g0 a0
        have hm0 := bit0 0; have hm2 := bit0 2
        simp only [Host.matrix,he0] at hm0 hm2
        rw [hm0,hm2] at he
        contradiction
      · have he := ht l2 k2 g2 a2
        have hm1 := bit2 1; have hm2 := bit2 2
        simp only [Host.matrix,he2] at hm1 hm2
        rw [hm1,hm2] at he
        contradiction
  · cases he : labelAt false h (rows 2) <;> simp_all [Anchor,Nonanchor]

theorem no_new_copy (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : OrderedCopy H4 (matrix h) rows cols) : Copy h rows cols := by
  have hr2 := third_row_nonanchor_of_anchor_agreement h (matrix h)
    (anchor_agreement h) rows cols hc
  have hr3 := nonanchor_later false h (rows 2) (rows 3) (hc.1 2 3 (by decide)) hr2
  have hcols : ∀ j, ¬ TerminalColumn h (labelAt true h (cols j)) := by
    intro j hj
    have hz2 := terminal_nonanchor_zero h (rows 2) (cols j) hr2 hj
    have hz3 := terminal_nonanchor_zero h (rows 3) (cols j) hr3 hj
    have hb2 := hc.2.2 2 j
    have hb3 := hc.2.2 3 j
    rw [hz2] at hb2
    rw [hz3] at hb3
    have hjcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjcases with rfl | rfl | rfl | rfl <;> contradiction
  refine ⟨hc.1,hc.2.1,?_⟩
  intro i j
  rw [← outside_agreement h (rows i) (cols j) (hcols j)]
  exact hc.2.2 i j

theorem original_first_column_terminal (h : Nat) (hh : 1 ≤ h)
    (rows cols : Fin 4 → Fin (size h)) (hc : Copy h rows cols) :
    TerminalColumn h (labelAt true h (cols 0)) := by
  rcases anchor_exists _ (second_row_anchor h rows cols hc) with ⟨l,k,g,a,hr1⟩
  rcases anchor_exists _ (first_column_anchor h rows cols hc) with ⟨u,v,w,b,hc0⟩
  rcases second_row_first_column_groups h rows cols hc l k g a u v w b hr1 hc0 with
    ⟨rfl,rfl,rfl,rfl⟩
  rcases all_copy_localization h hh rows cols hc with ⟨p,z,hr2,hc3⟩
  have hlh := anchor_index_level_bound false h (rows 1) l k 1 a hr1
  have hk := (anchor_index_valid false h (rows 1) l k 1 a hr1).2.1
  have hone : entry h (.variable h true p 0) (.anchor l k 0 b) = true := by
    have he : Host.matrix h (rows 2) (cols 0) = true := hc.2.2 2 0
    simpa only [Host.matrix,hr2,hc0] using he
  have hlast : entry h (.anchor l k 1 a) (.variable (h-1) false (p/2) z) = true := by
    have he : Host.matrix h (rows 1) (cols 3) = true := hc.2.2 1 3
    simpa only [Host.matrix,hr1,hc3] using he
  have hm : l = h ∧ (k = 4 ∨ k = 5) := by
    have hks : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    rcases hks with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [entry,rowRole,columnRole,signed] at hone hlast <;> omega
  simp [hc0,TerminalColumn,hm.1,hm.2]

theorem free (h : Nat) (hh : 1 ≤ h) : HFree H4 (matrix h) := by
  intro rows cols hc
  have old := no_new_copy h rows cols hc
  have ht := original_first_column_terminal h hh rows cols old
  have hr := third_row_nonanchor h rows cols old
  have hz := terminal_nonanchor_zero h (rows 2) (cols 0) hr ht
  have hb := hc.2.2 2 0
  rw [hz] at hb
  contradiction

#print axioms no_new_copy
#print axioms free

end TerminalAnchorRepair
end OrderedMatrixRemoval4.Host
