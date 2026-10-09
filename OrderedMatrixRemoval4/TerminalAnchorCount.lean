import OrderedMatrixRemoval4.TerminalAnchorRepair

namespace OrderedMatrixRemoval4.Host.TerminalAnchorRepair

theorem changed_iff_tags (h : Nat) (r c : Fin (size h)) :
    matrix h r c ≠ Host.matrix h r c ↔
    ∃ p a, labelAt false h r = .variable h true p 0 ∧
      labelAt true h c = .anchor h (4+p%2) 0 a := by
  constructor
  · intro he
    have hp : TerminalColumn h (labelAt true h c) ∧ Nonanchor (labelAt false h r) := by
      by_cases hn : TerminalColumn h (labelAt true h c) ∧ Nonanchor (labelAt false h r)
      · exact hn
      · simp [matrix,hn] at he
    have hz := terminal_nonanchor_zero h r c hp.2 hp.1
    have ho : Host.matrix h r c = true := by
      cases hh : Host.matrix h r c <;> simp_all
    cases hc : labelAt true h c with
    | «variable» => simp [hc,TerminalColumn] at hp
    | dummy => simp [hc,TerminalColumn] at hp
    | anchor l k g a =>
      have ht : l=h ∧ (k=4 ∨ k=5) ∧ g=0 := by simpa [hc,TerminalColumn] using hp.1
      rcases ht with ⟨hl,hk,hg⟩
      subst l
      subst g
      cases hr : labelAt false h r with
      | anchor => simp [hr,Nonanchor] at hp
      | dummy =>
        rcases hk with rfl | rfl <;> simp [Host.matrix,hr,hc,entry,rowRole] at ho
      | «variable» j s p b =>
        have hm : j=h ∧ p%2=k-4 := by
          rcases hk with rfl | rfl <;> cases s <;>
            simp [Host.matrix,hr,hc,entry,rowRole,signed] at ho <;> omega
        rcases hm with ⟨hj,hmod⟩
        subst j
        have hv := labelAt_valid false h r
        have hs : s=true := by simpa [hr,Valid] using hv
        subst s
        have hb := leaf_tag_clone_zero false h true p b
          (hr ▸ List.getElem_mem (labelAt._proof_1 false h r))
        subst b
        have heq : k=4+p%2 := by rcases hk with hk | hk <;> omega
        exact ⟨p,a,rfl,by simp [heq]⟩
  · rintro ⟨p,a,hr,hc⟩
    have hp : p%2=0 ∨ p%2=1 := by omega
    have hz : matrix h r c = false := by
      rcases hp with hp | hp <;> simp [matrix,hr,hc,TerminalColumn,Nonanchor,hp]
    have ho : Host.matrix h r c = true := by
      rcases hp with hp | hp <;> simp [Host.matrix,hr,hc,entry,rowRole,signed,hp]
    rw [hz,ho]
    decide

theorem anchor_clone_bound (h : Nat) (c : Fin (size h)) (l k g a : Nat)
    (hc : labelAt true h c = .anchor l k g a) : a < 2^h := by
  have hj := anchor_index_lt true h c l k g a hc
  have he := hc
  rw [labelAt_append,List.getElem_append_left hj] at he
  simp only [anchors,List.getElem_map,List.getElem_range,anchorLabel] at he
  have hea : c.val%2^h=a := (Position.anchor.inj he).2.2.2
  rw [← hea]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem cell_tag_members (h : Nat) (hh : 1 ≤ h) (p a : Fin (2^h)) :
    .variable h true p.val 0 ∈ axis false h ∧
    .anchor h (4+p.val%2) 0 a.val ∈ axis true h := by
  constructor
  · rw [variable_axis_mem_iff]
    exact ⟨by omega,p.isLt,by simp,by simp⟩
  · exact anchor_tag_mem true h h (4+p.val%2) 0 a.val hh (by omega)
      (by omega) (by omega) a.isLt

noncomputable def cell (h : Nat) (p a : Fin (2^h)) : Fin (size h) × Fin (size h) :=
  (pick false h (.variable h true p.val 0),
   pick true h (.anchor h (4+p.val%2) 0 a.val))

theorem cell_labels (h : Nat) (hh : 1 ≤ h) (p a : Fin (2^h)) :
    labelAt false h (cell h p a).1 = .variable h true p.val 0 ∧
    labelAt true h (cell h p a).2 = .anchor h (4+p.val%2) 0 a.val :=
  ⟨pick_label false h _ (cell_tag_members h hh p a).1,
   pick_label true h _ (cell_tag_members h hh p a).2⟩

noncomputable def candidates (h : Nat) : List (Fin (size h) × Fin (size h)) :=
  (cartesian (List.finRange (2^h)) (List.finRange (2^h))).map fun x => cell h x.1 x.2

theorem candidates_length (h : Nat) : (candidates h).length = (2^h)^2 := by
  simp [candidates,cartesian_length,Nat.pow_succ]

theorem edits_subset (h : Nat) (hh : 1 ≤ h) : Host.edits h (matrix h) ⊆ candidates h := by
  intro e he
  rcases e with ⟨r,c⟩
  have hd := (Host.mem_edits h (matrix h) r c).mp he
  rcases (changed_iff_tags h r c).mp hd with ⟨p,a,hr,hc⟩
  have hp := (variable_axis_mem_iff false h h true p 0).mp
    (hr ▸ List.getElem_mem (labelAt._proof_1 false h r))
  have ha := anchor_clone_bound h c h (4+p%2) 0 a hc
  let pp : Fin (2^h) := ⟨p,hp.2.1⟩
  let aa : Fin (2^h) := ⟨a,ha⟩
  have hl := cell_labels h hh pp aa
  have heq : cell h pp aa = (r,c) := Prod.ext
    (labelAt_injective false h _ _ (hl.1.trans hr.symm))
    (labelAt_injective true h _ _ (hl.2.trans hc.symm))
  exact List.mem_map.mpr ⟨(pp,aa),(mem_cartesian _ _ _ _).mpr
    ⟨List.mem_finRange _,List.mem_finRange _⟩,heq⟩

theorem edit_count (h : Nat) (hh : 1 ≤ h) : Host.editCount h (matrix h) = (2^h)^2 := by
  apply Nat.le_antisymm
  · have he := (Host.edits_nodup h (matrix h)).length_le_of_subset (edits_subset h hh)
    simpa [Host.editCount,candidates_length] using he
  · exact arbitrary_edit_distance h hh (matrix h) (free h hh)

theorem exact_minimum (h : Nat) (hh : 1 ≤ h) :
    HFree H4 (matrix h) ∧ Host.editCount h (matrix h) = (2^h)^2 ∧
    ∀ B : BinaryMatrix (size h), HFree H4 B → (2^h)^2 ≤ Host.editCount h B :=
  ⟨free h hh,edit_count h hh,fun B hf => arbitrary_edit_distance h hh B hf⟩

#print axioms changed_iff_tags
#print axioms edit_count
#print axioms exact_minimum

end OrderedMatrixRemoval4.Host.TerminalAnchorRepair
