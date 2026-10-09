import OrderedMatrixRemoval4.Localization

namespace OrderedMatrixRemoval4.Host

theorem ancestor_eq_div_pow (d p : Nat) : ancestor d p = p / 2 ^ d := by
  induction d with
  | zero => simp [ancestor]
  | succ d ih => rw [ancestor, ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem tree_variable_mem_iff (column : Bool) (rem depth node j : Nat)
    (s : Bool) (q a : Nat) :
    .variable j s q a ∈ tree column rem depth node ↔
      depth ≤ j ∧ j ≤ depth + rem ∧ ancestor (j - depth) q = node ∧
      a < 2 ^ (depth + rem - j) ∧ (j = depth + rem → s = true) := by
  induction rem generalizing depth node with
  | zero =>
    constructor
    · intro hm
      have he := List.eq_of_mem_singleton hm
      cases he
      simp [ancestor]
    · rintro ⟨hd,hj,hn,ha,hs⟩
      have he : j = depth := by omega
      subst j
      simp [ancestor] at hn
      have hsa := hs (by omega)
      have haa : a = 0 := by simpa using ha
      subst q
      subst s
      subst a
      simp [tree]
  | succ rem ih =>
    by_cases hd : depth ≤ j
    · by_cases hj : j = depth
      · subst j
        cases column <;> cases s <;>
          simp [tree, block, ancestor, ih] <;> omega
      · have he : j - depth = (j - (depth + 1)) + 1 := by omega
        have ht : depth + (rem + 1) = depth + 1 + rem := by omega
        have hanc : ancestor (j - depth) q = ancestor (j - (depth + 1)) q / 2 := by
          rw [he, ancestor]
        simp only [tree, List.mem_append, block, List.mem_map, List.mem_range,
          Position.variable.injEq, ih]
        constructor
        · intro hm
          rcases hm with ((hm | hm) | hm) | hm
          · rcases hm with ⟨a',ha',hd,_,_,_⟩; exact False.elim (hj hd.symm)
          · rcases hm with ⟨hd,hj',hn,ha,hs⟩
            refine ⟨by omega, by omega, ?_, by simpa only [ht] using ha, ?_⟩
            · rw [hanc, hn]; omega
            · intro hj'; exact hs (by omega)
          · rcases hm with ⟨hd,hj',hn,ha,hs⟩
            refine ⟨by omega, by omega, ?_, by simpa only [ht] using ha, ?_⟩
            · rw [hanc, hn]; omega
            · intro hj'; exact hs (by omega)
          · rcases hm with ⟨a',ha',hd,_,_,_⟩; exact False.elim (hj hd.symm)
        · rintro ⟨hd,hj',hn,ha,hs⟩
          have hd' : depth + 1 ≤ j := by omega
          rw [hanc] at hn
          have hb : ancestor (j - (depth + 1)) q = 2 * node ∨
              ancestor (j - (depth + 1)) q = 2 * node + 1 := by omega
          rcases hb with hb | hb
          · exact Or.inl (Or.inl (Or.inr ⟨hd',by omega,hb,by simpa only [ht] using ha,
              fun ht' => hs (by omega)⟩))
          · exact Or.inl (Or.inr ⟨hd',by omega,hb,by simpa only [ht] using ha,
              fun ht' => hs (by omega)⟩)
    · constructor
      · intro hm
        exact False.elim (hd (tree_location column (rem + 1) depth node j s q a hm).1)
      · intro hm; exact False.elim (hd hm.1)

theorem variable_axis_mem_iff (column : Bool) (h j : Nat) (s : Bool) (q a : Nat) :
    .variable j s q a ∈ axis column h ↔
      j ≤ h ∧ q < 2 ^ j ∧ a < 2 ^ (h - j) ∧ (j = h → s = true) := by
  have ht : .variable j s q a ∈ tree column h 0 0 ↔
      j ≤ h ∧ q < 2 ^ j ∧ a < 2 ^ (h - j) ∧ (j = h → s = true) := by
    rw [tree_variable_mem_iff]
    simp [ancestor_eq_div_pow, Nat.div_eq_zero_iff_lt (Nat.pow_pos (by decide : 0 < 2))]
  unfold axis nonanchors
  cases column <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append]
  all_goals simp [anchors, anchorLabel, dummies, ht]

end OrderedMatrixRemoval4.Host
