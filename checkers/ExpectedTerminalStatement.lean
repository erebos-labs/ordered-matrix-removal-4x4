import OrderedMatrixRemoval4.TerminalAnchorCount
import OrderedMatrixRemoval4.Removal
import Mathlib.Data.Finset.Card

namespace IndependentAudit
open OrderedMatrixRemoval4
open OrderedMatrixRemoval4.Host

/-- Literal requested pattern; equality below checks all sixteen entries. -/
def expectedH4 : BinaryMatrix 4 := fun r c =>
  match r.val with
  | 0 => c.val = 1 || c.val = 2
  | 1 => c.val = 0 || c.val = 3
  | 2 => c.val = 0 || c.val = 2
  | _ => c.val = 1 || c.val = 2 || c.val = 3

theorem pattern_exact : H4 = expectedH4 := by
  funext r c
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  have hc : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  rcases hr with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-- Actual physical leaf-to-parity-terminal-anchor mask, stated separately. -/
def repairCell (h : Nat) (r c : Fin (size h)) : Prop :=
  ∃ p a, labelAt false h r = .variable h true p 0 ∧
    labelAt true h c = .anchor h (4 + p % 2) 0 a

noncomputable def expectedRepair (h : Nat) : BinaryMatrix (size h) := by
  classical
  exact fun r c => if repairCell h r c then false else Host.matrix h r c

theorem repair_exact (h : Nat) : TerminalAnchorRepair.matrix h = expectedRepair h := by
  classical
  funext r c
  by_cases hc : repairCell h r c
  · rcases hc with ⟨p,a,hr,hcol⟩
    have hm : p % 2 = 0 ∨ p % 2 = 1 := by omega
    have hz : TerminalAnchorRepair.matrix h r c = false := by
      rcases hm with hm | hm <;>
        simp [TerminalAnchorRepair.matrix,TerminalAnchorRepair.TerminalColumn,hr,hcol,Nonanchor,hm]
    have hcell : repairCell h r c := ⟨p,a,hr,hcol⟩
    simpa [expectedRepair,hcell] using hz
  · have he : TerminalAnchorRepair.matrix h r c = Host.matrix h r c := by
      by_contra hn
      exact hc ((TerminalAnchorRepair.changed_iff_tags h r c).mp hn)
    simpa [expectedRepair,hc] using he

/-- Independent axes strictly increase, and every zero and every one is matched. -/
def actualFree {n : Nat} (B : BinaryMatrix n) : Prop :=
  ∀ rows cols : Fin 4 → Fin n,
    (∀ i j, i.val < j.val → (rows i).val < (rows j).val) →
    (∀ i j, i.val < j.val → (cols i).val < (cols j).val) →
    ¬ (∀ i j, B (rows i) (cols j) = expectedH4 i j)

theorem free_semantics {n : Nat} (B : BinaryMatrix n) :
    HFree H4 B ↔ actualFree B := by
  rw [pattern_exact]
  constructor
  · intro hf rows cols hr hc hm
    exact hf rows cols ⟨hr,hc,hm⟩
  · intro hf rows cols hm
    exact hf rows cols hm.1 hm.2.1 hm.2.2

/-- Counts ALL differing physical binary entries, in either direction. -/
noncomputable def physicalEdits (h : Nat) (B : BinaryMatrix (size h)) :
    Finset (Fin (size h) × Fin (size h)) := by
  classical
  exact Finset.univ.filter fun e => B e.1 e.2 ≠ Host.matrix h e.1 e.2

theorem physical_count_exact (h : Nat) (B : BinaryMatrix (size h)) :
    (physicalEdits h B).card = Host.editCount h B := by
  classical
  have he : physicalEdits h B = (Host.edits h B).toFinset := by
    ext e
    rcases e with ⟨r,c⟩
    simp [physicalEdits,Host.mem_edits]
  rw [he,List.toFinset_card_of_nodup (Host.edits_nodup h B)]
  rfl

theorem explicit_expected_statement : ∀ h : Nat, 1 ≤ h →
    actualFree (expectedRepair h) ∧
    (physicalEdits h (expectedRepair h)).card = (2 ^ h) ^ 2 ∧
    (∀ B : Fin (size h) → Fin (size h) → Bool,
      actualFree B → (2 ^ h) ^ 2 ≤ (physicalEdits h B).card) := by
  intro h hh
  obtain ⟨hf,he,hmin⟩ := TerminalAnchorRepair.exact_minimum h hh
  rw [repair_exact] at hf he
  refine ⟨(free_semantics _).mp hf,?_,?_⟩
  · rw [physical_count_exact,he]
  · intro B hb
    rw [physical_count_exact]
    exact hmin B ((free_semantics _).mpr hb)

/-- Bridges the release's literal attained minimum to the physical edit counter. -/
theorem edit_counter_bridge (h : Nat) (B : BinaryMatrix (size h)) :
    Blowup.editCount (Host.matrix h) B = Host.editCount h B := rfl

theorem actual_minimum (h : Nat) (hh : 1 ≤ h) :
    Removal.repairCount (Host.matrix h) = (2 ^ h) ^ 2 := by
  apply Nat.le_antisymm
  · have hu := Removal.repair_minimal (Host.matrix h) (TerminalAnchorRepair.matrix h)
      (TerminalAnchorRepair.free h hh)
    rw [edit_counter_bridge,TerminalAnchorRepair.edit_count h hh] at hu
    exact hu
  · obtain ⟨B,hf,hB⟩ := Removal.repair_attained (Host.matrix h)
    have hl := Host.arbitrary_edit_distance h hh B hf
    rw [← edit_counter_bridge,hB] at hl
    exact hl

theorem normalized_actual_minimum (h : Nat) (hh : 1 ≤ h) :
    Removal.distance (Host.matrix h) = 1 / (14 * (h : ℝ) + 2) ^ 2 := by
  unfold Removal.distance
  rw [actual_minimum h hh]
  unfold Host.size
  push_cast
  have hm : (2 : ℝ) ^ h ≠ 0 := by positivity
  have hd : 14 * (h : ℝ) + 2 ≠ 0 := by positivity
  field_simp

#print axioms explicit_expected_statement
#print axioms actual_minimum
#print axioms normalized_actual_minimum
#check TerminalAnchorRepair.exact_minimum
#check actual_minimum
#check normalized_actual_minimum
end IndependentAudit
