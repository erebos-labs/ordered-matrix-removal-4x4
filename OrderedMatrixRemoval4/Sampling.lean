import OrderedMatrixRemoval4.IntactPath
import OrderedMatrixRemoval4.FiniteCounting

namespace OrderedMatrixRemoval4

/-- Finite injection bound, with injectivity needed only on the listed inputs. -/
theorem count_le_of_witness {α β : Type} (xs : List α) (ys : List β)
    (hx : xs.Nodup) (f : α → β) (hf : ∀ a ∈ xs, f a ∈ ys)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : xs.length ≤ ys.length := by
  have hm : (xs.map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne,List.pairwise_map]
    apply hx.imp_of_mem
    intro a b ha hb hab he
    exact hab (hinj a ha b hb he)
  have hs : xs.map f ⊆ ys := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨a,ha,rfl⟩
    exact hf a ha
  simpa using hm.length_le_of_subset hs

namespace Host

noncomputable def edits (h : Nat) (B : BinaryMatrix (size h)) :
    List (Fin (size h) × Fin (size h)) := by
  classical
  exact (cartesian (List.finRange (size h)) (List.finRange (size h))).filter
    fun e => decide (B e.1 e.2 ≠ matrix h e.1 e.2)

noncomputable def editCount (h : Nat) (B : BinaryMatrix (size h)) : Nat := (edits h B).length

theorem mem_edits (h : Nat) (B : BinaryMatrix (size h)) (r c : Fin (size h)) :
    (r,c) ∈ edits h B ↔ B r c ≠ matrix h r c := by
  classical
  simp [edits,mem_cartesian,List.mem_finRange]

theorem edits_nodup (h : Nat) (B : BinaryMatrix (size h)) : (edits h B).Nodup := by
  classical
  exact List.Pairwise.filter _ (cartesian_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))

/-- General finite protected-selection counting. The injectivity hypothesis is
an explicit incidence property still to be established for an actual family;
this theorem alone is not the host distance lower bound. -/
theorem edit_count_of_separating_paths (h : Nat) (hh : 1 ≤ h)
    (B : BinaryMatrix (size h)) (hf : HFree H4 B)
    {α : Type} (samples : List α) (hn : samples.Nodup) (paths : α → PathSelection h)
    (hsep : ∀ a ∈ samples, ∀ b ∈ samples, ∀ r c,
      (paths a).Selected false r → (paths a).Selected true c →
      (paths b).Selected false r → (paths b).Selected true c →
      Protected h r c → a = b) : samples.length ≤ editCount h B := by
  classical
  have hex : ∀ a ∈ samples, ∃ cell : Fin (size h) × Fin (size h),
      cell ∈ edits h B ∧ (paths a).Selected false cell.1 ∧
      (paths a).Selected true cell.2 ∧ Protected h cell.1 cell.2 := by
    intro a ha
    apply Classical.byContradiction
    intro hbad
    have hint : IntactPath h B (paths a) := by
      intro r c hr hc hp
      apply Classical.byContradiction
      intro he
      exact hbad ⟨(r,c),(mem_edits h B r c).mpr he,hr,hc,hp⟩
    rcases intact_path_contains_copy h hh B (paths a) hint with ⟨rows,cols,hcopy⟩
    exact hf rows cols hcopy
  let witness : α → Fin (size h) × Fin (size h) := fun a =>
    if ha : a ∈ samples then Classical.choose (hex a ha) else
      (⟨0,by unfold size; exact Nat.mul_pos (by omega) (Nat.pow_pos (by decide : 0 < 2))⟩,
       ⟨0,by unfold size; exact Nat.mul_pos (by omega) (Nat.pow_pos (by decide : 0 < 2))⟩)
  have hw : ∀ a (ha : a ∈ samples),
      witness a ∈ edits h B ∧ (paths a).Selected false (witness a).1 ∧
      (paths a).Selected true (witness a).2 ∧ Protected h (witness a).1 (witness a).2 := by
    intro a ha
    simpa only [witness,dif_pos ha] using Classical.choose_spec (hex a ha)
  apply count_le_of_witness samples (edits h B) hn witness
  · intro a ha; exact (hw a ha).1
  · intro a ha b hb he
    have hb' := hw b hb
    rw [← he] at hb'
    exact hsep a ha b hb (witness a).1 (witness a).2 (hw a ha).2.1 (hw a ha).2.2.1
      hb'.2.1 hb'.2.2.1 (hw a ha).2.2.2

end Host
end OrderedMatrixRemoval4
