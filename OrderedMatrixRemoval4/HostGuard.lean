import OrderedMatrixRemoval4.PathOrder
import OrderedMatrixRemoval4.Frame

namespace OrderedMatrixRemoval4.Host

def four {α : Type} (a b c d : α) : Fin 4 → α :=
  fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d

theorem four_increasing {n : Nat} (a b c d : Fin n)
    (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val) :
    Increasing (four a b c d) := by
  intro i j hij
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
  all_goals simp [four] at * <;> omega

private theorem row_roles_disjoint (h l k : Nat) (r : Position)
    (h0 : rowRole h l k 0 r) (h1 : rowRole h l k 1 r) : False := by
  cases r <;> simp [rowRole] at h0 h1 <;> omega

private theorem column_roles_disjoint (h l k : Nat) (c : Position)
    (h0 : columnRole h l k 0 c) (h1 : columnRole h l k 1 c) : False := by
  cases c <;> simp [columnRole] at h0 h1 <;> omega

private theorem row_role_nonanchor (h l k g : Nat) (r : Position)
    (hr : rowRole h l k g r) : Nonanchor r := by
  cases r <;> simp_all [rowRole,Nonanchor]

private theorem column_role_nonanchor (h l k g : Nat) (c : Position)
    (hc : columnRole h l k g c) : Nonanchor c := by
  cases c <;> simp_all [columnRole,Nonanchor]

private theorem row_role_entries (h l k a b : Nat) (r : Position) (g : Fin 2)
    (hr : rowRole h l k g.val r) :
    entry h r (.anchor l k 0 a) = decide (g.val = 0) ∧
    entry h r (.anchor l k 1 b) = decide (g.val = 1) := by
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · have hn : ¬ rowRole h l k 1 r := row_roles_disjoint h l k r hr
    cases r <;> simp_all [entry,rowRole]
  · have hn : ¬ rowRole h l k 0 r := fun h0 => row_roles_disjoint h l k r h0 hr
    cases r <;> simp_all [entry,rowRole]

private theorem column_role_entries (h l k a b : Nat) (c : Position) (g : Fin 2)
    (hc : columnRole h l k g.val c) :
    entry h (.anchor l k 0 a) c = decide (g.val = 0) ∧
    entry h (.anchor l k 1 b) c = decide (g.val = 1) := by
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · have hn : ¬ columnRole h l k 1 c := column_roles_disjoint h l k c hc
    cases c <;> simp_all [entry,columnRole]
  · have hn : ¬ columnRole h l k 0 c := fun h0 => column_roles_disjoint h l k c h0 hc
    cases c <;> simp_all [entry,columnRole]

/-- The twelve host guard cells for one actual mode. Body bits remain arbitrary. -/
theorem canonical_host_guard (h l k a b c d : Nat)
    (r0 r1 r2 r3 c0 c1 c2 c3 : Fin (size h))
    (hr0 : labelAt false h r0 = .anchor l k 0 a)
    (hr1 : labelAt false h r1 = .anchor l k 1 b)
    (hc0 : labelAt true h c0 = .anchor l k 0 c)
    (hc1 : labelAt true h c1 = .anchor l k 1 d)
    (rr0 : rowRole h l k 0 (labelAt false h r2))
    (rr1 : rowRole h l k 1 (labelAt false h r3))
    (cc0 : columnRole h l k 0 (labelAt true h c2))
    (cc1 : columnRole h l k 1 (labelAt true h c3))
    (hro : r2.val < r3.val) (hco : c2.val < c3.val) :
    FrameGuard (matrix h) (four r0 r1 r2 r3) (four c0 c1 c2 c3) := by
  have r0a : Anchor (labelAt false h r0) := by simp [hr0,Anchor]
  have r1a : Anchor (labelAt false h r1) := by simp [hr1,Anchor]
  have c0a : Anchor (labelAt true h c0) := by simp [hc0,Anchor]
  have c1a : Anchor (labelAt true h c1) := by simp [hc1,Anchor]
  have rb0 := row_role_entries h l k c d _ 0 rr0
  have rb1 := row_role_entries h l k c d _ 1 rr1
  have cb0 := column_role_entries h l k a b _ 0 cc0
  have cb1 := column_role_entries h l k a b _ 1 cc1
  refine ⟨four_increasing _ _ _ _ (anchor_group_order false h l k a b r0 r1 hr0 hr1)
    (anchor_before_nonanchor false h r1 r2 r1a (row_role_nonanchor h l k 0 _ rr0)) hro,
    four_increasing _ _ _ _ (anchor_group_order true h l k c d c0 c1 hc0 hc1)
    (anchor_before_nonanchor true h c1 c2 c1a (column_role_nonanchor h l k 0 _ cc0)) hco,?_⟩
  intro i j ha
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals simp [four]
  all_goals simp only [matrix,hr0,hr1,hc0,hc1]
  all_goals try simp only [rb0.1,rb0.2,rb1.1,rb1.2,cb0.1,cb0.2,cb1.1,cb1.2]
  all_goals try simp [entry,H4]
  all_goals rfl

end OrderedMatrixRemoval4.Host
