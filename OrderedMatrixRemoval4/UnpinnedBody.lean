import OrderedMatrixRemoval4.UnpinnedCases

namespace OrderedMatrixRemoval4.Host

private theorem ancestor_sub_one (i j p : Nat) (he : i + 1 = j) :
    ancestor (j - i) p = p / 2 := by
  have hs : j - i = 1 := by omega
  rw [hs]
  rfl

set_option maxHeartbeats 400000 in
private theorem unpinned_minus (h l k l0 k0 g0 c i p a d q z j b w : Nat)
    (s u t : Bool) (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6)
    (hl0 : 1 ≤ l0) (hk0 : k0 < 6) (hg0 : g0 < 2)
    (vi : i ≤ h ∧ (i = h → s = true))
    (vd : d ≤ h ∧ (d = h → u = true))
    (vj : j ≤ h ∧ (j = h → t = true))
    (rr : rowRole h l k 0 (.variable i s p a))
    (cc : columnRole h l k 1 (.variable j t b w))
    (hdiff : d ≠ j ∨ u ≠ t)
    (co : TraversalOrdered true (.variable d u q z) (.variable j t b w))
    (hone : entry h (.variable i s p a) (.variable d u q z) = true)
    (hzero : entry h (.variable i s p a) (.variable j t b w) = false)
    (horder : anchorRank (l0 - 1) k0 g0 < anchorRank (l - 1) k 1)
    (hinc : columnRole h l0 k0 g0 (.variable d u q z))
    (hcase : k = 4 ∨ k = 5) :
    i = h ∧ s = true ∧ j = h - 1 ∧ t = false ∧ b = p / 2 := by
  rcases hcase with rfl | rfl <;> cases s <;> cases u <;> cases t
  all_goals simp [rowRole, columnRole, signed, entry, TraversalOrdered, anchorRank]
    at rr cc vi vd vj hdiff co hone hzero horder
  all_goals try simp (disch := omega) only [ancestor_sub_one] at co
  all_goals try simp only [ancestor] at co
  all_goals try simp
  all_goals try omega
  all_goals first
    | have heven : q % 2 = 0 := earlier_minus_role_even h d l0 k0 g0 q z
        (by omega) (by omega) hl0 (by unfold anchorRank; omega) hinc
      have hpq : p < q := by omega
      have hqb : q / 2 ≤ b := by omega
      have hbp : b ≤ p / 2 := by omega
      have hsib := OrderedMatrixRemoval4.nonterminal_siblings p q b hpq hqb hbp
      omega
    | rcases hone with hown | hparent
      · have hdiv : p / 2 ≤ q / 2 := Nat.div_le_div_right hown.2
        try simp (disch := omega) only [ancestor_sub_one] at co
        omega
      · omega


theorem unpinned_body_localizes (h l k l0 k0 g0 c i p a d q z j b w : Nat)
    (s u t : Bool) (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6)
    (hl0 : 1 ≤ l0) (hk0 : k0 < 6) (hg0 : g0 < 2)
    (vi : i ≤ h ∧ (i = h → s = true))
    (vd : d ≤ h ∧ (d = h → u = true))
    (vj : j ≤ h ∧ (j = h → t = true))
    (rr : rowRole h l k 0 (.variable i s p a))
    (cc : columnRole h l k 1 (.variable j t b w))
    (hdiff : d ≠ j ∨ u ≠ t)
    (co : TraversalOrdered true (.variable d u q z) (.variable j t b w))
    (hone : entry h (.variable i s p a) (.variable d u q z) = true)
    (hzero : entry h (.variable i s p a) (.variable j t b w) = false)
    (horder : anchorRank (l0 - 1) k0 g0 < anchorRank (l - 1) k 1)
    (hinc : columnRole h l0 k0 g0 (.variable d u q z)) :
    i = h ∧ s = true ∧ j = h - 1 ∧ t = false ∧ b = p / 2 := by
  have hks : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases hks with hk0' | hk1' | hk2' | hk3' | hk4' | hk5'
  · exact unpinned_vertical_body_localizes h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inl hk0')
  · exact unpinned_vertical_body_localizes h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inr hk1')
  · exact unpinned_positive_body_localizes h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inl hk2')
  · exact unpinned_positive_body_localizes h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inr hk3')
  · exact unpinned_minus h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inl hk4')
  · exact unpinned_minus h l k l0 k0 g0 c i p a d q z j b w s u t hl hlh hk hl0 hk0 hg0 vi vd vj rr cc hdiff co hone hzero horder hinc (Or.inr hk5')

end OrderedMatrixRemoval4.Host
