import OrderedMatrixRemoval4.TerminalAnchorCount
import OrderedMatrixRemoval4.Removal
namespace IndependentAudit
open OrderedMatrixRemoval4
open OrderedMatrixRemoval4.Host

theorem original_not_free (h : Nat) (hh : 1 ≤ h) : ¬ HFree H4 (Host.matrix h) := by
  intro hf
  have hl := arbitrary_edit_distance h hh (Host.matrix h) hf
  have he : editCount h (Host.matrix h) = 0 := by
    classical
    simp [editCount,edits]
  rw [he] at hl
  have hm : 0 < (2 ^ h) ^ 2 := Nat.pow_pos (Nat.pow_pos (by decide))
  omega

theorem domain_nonempty : ∃ h : Nat, 1 ≤ h := ⟨1,by decide⟩

theorem all_depth_axes_nonempty (h : Nat) : 0 < Host.size h := by
  unfold Host.size
  exact Nat.mul_pos (by omega) (Nat.pow_pos (by decide))

#print axioms original_not_free
#print axioms domain_nonempty
#print axioms all_depth_axes_nonempty
end IndependentAudit
