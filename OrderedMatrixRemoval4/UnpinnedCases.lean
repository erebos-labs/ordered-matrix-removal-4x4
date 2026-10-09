import OrderedMatrixRemoval4.CanonicalBody

namespace OrderedMatrixRemoval4.Host

private theorem ancestor_sub_one (i j p : Nat) (he : i + 1 = j) :
    ancestor (j - i) p = p / 2 := by
  have hs : j - i = 1 := by omega
  rw [hs]
  rfl

/-- The unpinned mode calculation, including the exceptional earlier-anchor
incidence. The middle column class is different from the last column class. -/
theorem unpinned_vertical_body_localizes (h l k l0 k0 g0 c i p a d q z j b w : Nat)
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
    (hcase : k = 0 ∨ k = 1) :
    i = h ∧ s = true ∧ j = h - 1 ∧ t = false ∧ b = p / 2 := by
  rcases hcase with rfl | rfl <;> cases s <;> cases u <;> cases t
  all_goals simp [rowRole, columnRole, signed, entry, TraversalOrdered, anchorRank]
    at rr cc vi vd vj hdiff co hone hzero horder
  all_goals try simp (disch := omega) only [ancestor_sub_one] at co
  all_goals try simp only [ancestor] at co
  all_goals first
    | omega
    | have heven : q % 2 = 0 := earlier_minus_role_even h d l0 k0 g0 q z
        (by omega) (by omega) hl0 (by unfold anchorRank; omega) hinc
      omega


theorem unpinned_positive_body_localizes (h l k l0 k0 g0 c i p a d q z j b w : Nat)
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
    (hcase : k = 2 ∨ k = 3) :
    i = h ∧ s = true ∧ j = h - 1 ∧ t = false ∧ b = p / 2 := by
  rcases hcase with rfl | rfl <;> cases s <;> cases u <;> cases t
  all_goals simp [rowRole, columnRole, signed, entry, TraversalOrdered, anchorRank]
    at rr cc vi vd vj hdiff co hone hzero horder
  all_goals try simp (disch := omega) only [ancestor_sub_one] at co
  all_goals try simp only [ancestor] at co
  all_goals first
    | omega
    | have heven : q % 2 = 0 := earlier_minus_role_even h d l0 k0 g0 q z
        (by omega) (by omega) hl0 (by unfold anchorRank; omega) hinc
      omega



end OrderedMatrixRemoval4.Host
