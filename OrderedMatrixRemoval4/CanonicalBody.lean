import OrderedMatrixRemoval4.Modes
import OrderedMatrixRemoval4.Leaf

namespace OrderedMatrixRemoval4.Host

private theorem ancestor_sub_one (i j p : Nat) (he : i + 1 = j) :
    ancestor (j - i) p = p / 2 := by
  have hs : j - i = 1 := by omega
  rw [hs]
  rfl

theorem canonical_body_localizes (h l k : Nat) (r0 r1 c0 c1 : Position)
    (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6)
    (vr0 : Valid h r0) (vr1 : Valid h r1) (vc0 : Valid h c0) (vc1 : Valid h c1)
    (nr0 : Nonanchor r0) (nr1 : Nonanchor r1) (nc0 : Nonanchor c0) (nc1 : Nonanchor c1)
    (rr0 : rowRole h l k 0 r0) (rr1 : rowRole h l k 1 r1)
    (cc0 : columnRole h l k 0 c0) (cc1 : columnRole h l k 1 c1)
    (ro : TraversalOrdered false r0 r1) (co : TraversalOrdered true c0 c1)
    (b00 : entry h r0 c0 = true) (b01 : entry h r0 c1 = false)
    (b10 : entry h r1 c0 = true) (b11 : entry h r1 c1 = true) :
    ∃ p a b, r0 = .variable h true p a ∧ c1 = .variable (h - 1) false (p / 2) b := by
  cases r0 with
  | anchor => contradiction
  | dummy => simp [rowRole] at rr0
  | «variable» i s p a =>
    cases c1 with
    | anchor => contradiction
    | dummy => simp [columnRole] at cc1
    | «variable» j t q b =>
      have htarget : i = h ∧ s = true ∧ j = h - 1 ∧ t = false ∧ q = p / 2 := by
        have hks : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
        rcases hks with rfl | rfl | rfl | rfl | rfl | rfl <;>
          cases r1 <;> cases c0 <;> cases s <;> cases t
        all_goals try cases ‹Bool›
        all_goals try cases ‹Bool›
        all_goals simp [Valid, Nonanchor, rowRole, columnRole, signed, entry, TraversalOrdered] at *
        all_goals try simp (disch := omega) only [ancestor_sub_one] at ro
        all_goals try simp (disch := omega) only [ancestor_sub_one] at co
        all_goals omega
      rcases htarget with ⟨rfl, rfl, hj, rfl, hq⟩
      exact ⟨p,a,b,rfl,by simp only [hj,hq]⟩

theorem canonical_copy_localization (h : Nat) (rows cols : Fin 4 → Fin (size h))
    (hc : Copy h rows cols) (hc1 : Anchor (labelAt true h (cols 1))) :
    sparseZero h (rows 2) (cols 3) := by
  rcases canonical_frame_of_copy h rows cols hc hc1 with
    ⟨l,k,a0,a1,b0,b1,hl,hlh,hk,hr0,hr1,hc0,hc1,rr0,rr1,cc0,cc1⟩
  have hs := copy_anchor_shape h rows cols hc
  have hbody := canonical_body_localizes h l k
    (labelAt false h (rows 2)) (labelAt false h (rows 3))
    (labelAt true h (cols 2)) (labelAt true h (cols 3)) hl hlh hk
    (labelAt_valid false h (rows 2)) (labelAt_valid false h (rows 3))
    (labelAt_valid true h (cols 2)) (labelAt_valid true h (cols 3))
    hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2 rr0 rr1 cc0 cc1
    (indexed_traversal_ordered false h (rows 2) (rows 3) (hc.1 2 3 (by decide)))
    (indexed_traversal_ordered true h (cols 2) (cols 3) (hc.2.1 2 3 (by decide)))
    (hc.2.2 2 2) (hc.2.2 2 3) (hc.2.2 3 2) (hc.2.2 3 3)
  rcases hbody with ⟨p,a,b,hr,hc'⟩
  have hm : .variable h true p a ∈ axis false h := by rw [← hr]; exact List.getElem_mem _
  have ha := leaf_tag_clone_zero false h true p a hm
  subst a
  exact ⟨p,b,hr,hc'⟩

end OrderedMatrixRemoval4.Host
