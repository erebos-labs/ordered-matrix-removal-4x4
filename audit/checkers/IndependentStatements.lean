import OrderedMatrixRemoval4
open OrderedMatrixRemoval4
namespace IndependentAudit

theorem free_iff_count_zero {n : Nat} (A : BinaryMatrix n) :
    HFree H4 A ↔ Counting.copyCount A = 0 := by
  classical
  rw [Counting.copyCount, List.length_eq_zero_iff]
  constructor
  · intro hf
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    exact hf e.1 e.2 ((Counting.mem_copies A e).mp he)
  · intro hz rows cols hc
    have hm := (Counting.mem_copies A (rows,cols)).mpr hc
    rw [hz] at hm
    cases hm

theorem editCount_eq_hamming {n : Nat} (A B : BinaryMatrix n) :
    Blowup.editCount A B = (Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ B e.1 e.2)).card := by
  classical
  have he : (Blowup.edits A B).toFinset = Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ B e.1 e.2) := by
    ext e
    rcases e with ⟨r,c⟩
    simp [Blowup.mem_edits, ne_comm]
  rw [← he, List.toFinset_card_of_nodup (Blowup.edits_nodup A B)]
  rfl

attribute [local instance] Classical.propDecidable

theorem copyCount_eq_all_embeddings {n : Nat} (A : BinaryMatrix n) :
    Counting.copyCount A = (Finset.univ.filter (fun e : (Fin 4 → Fin n) × (Fin 4 → Fin n) =>
      OrderedCopy H4 A e.1 e.2)).card := by
  classical
  have he : (Counting.copies A).toFinset = Finset.univ.filter (fun e => OrderedCopy H4 A e.1 e.2) := by
    ext e
    simp [Counting.mem_copies]
  rw [← he, List.toFinset_card_of_nodup (Counting.copies_nodup A)]
  rfl

theorem repair_is_actual_minimum {n : Nat} (A : BinaryMatrix n) :
    ∃ B : BinaryMatrix n, HFree H4 B ∧
      (Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ B e.1 e.2)).card = Removal.repairCount A ∧
      ∀ D : BinaryMatrix n, HFree H4 D → Removal.repairCount A ≤
        (Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ D e.1 e.2)).card := by
  classical
  obtain ⟨B,hf,he⟩ := Removal.repair_attained A
  refine ⟨B,hf,?_,?_⟩
  · rw [← editCount_eq_hamming A B]; exact he
  · intro D hD
    rw [← editCount_eq_hamming A D]
    exact Removal.repair_minimal A D hD

example : H4 = (fun r c => (![![false,true,true,false], ![true,false,false,true],
    ![true,false,true,false], ![false,true,true,true]]) r c) := by decide

example : ¬ (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n : Nat, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ A : Fin n → Fin n → Bool,
    ε ≤ (Removal.repairCount A : ℝ) / (n : ℝ)^2 →
    c * Real.rpow ε C * (n : ℝ)^8 ≤ (Counting.copyCount A : ℝ)) :=
  Removal.no_polynomial_removal

theorem host_has_copy (h : Nat) (hh : 1 ≤ h) : ∃ rows cols,
    OrderedCopy H4 (Host.matrix h) rows cols := by
  exact Host.intact_path_contains_copy h hh (Host.matrix h)
    (Host.shiftPath h ⟨0,Nat.two_pow_pos h⟩ ⟨0,Nat.two_pow_pos h⟩)
    (fun _ _ _ _ _ => rfl)

example (c C η : ℝ) (hc : 0 < c) (hC : 0 < C) (hη : 0 < η) (N : ℝ → Nat) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε < η ∧ ∃ n : Nat, 1 ≤ n ∧ N ε ≤ n ∧
      ∃ A : Fin n → Fin n → Bool, ε ≤ Removal.distance A ∧
        (Counting.copyCount A : ℝ) < c * Real.rpow ε C * (n : ℝ)^8 :=
  Removal.counterexample c C η hc hC hη N

#print axioms copyCount_eq_all_embeddings
#print axioms repair_is_actual_minimum
#print axioms host_has_copy
#print axioms free_iff_count_zero
#print axioms editCount_eq_hamming
#print axioms Host.tagCopy_iff_exists_copy
#print axioms Host.labelAt_injective
#print axioms Host.copy_anchor_shape
#print axioms Host.all_copy_localization
#print axioms Host.sparseCells_nodup
#print axioms Host.mem_sparseCells_iff
#print axioms Host.sparseCells_length
#print axioms Counting.mem_copies
#print axioms Counting.copies_nodup
#print axioms Host.copy_count_bound
#print axioms Host.shiftPath_separates
#print axioms Host.intact_path_contains_copy
#print axioms Host.arbitrary_edit_distance
#print axioms Blowup.project_copy
#print axioms Blowup.arbitrary_edit_distance
#print axioms Blowup.copy_count_bound
#print axioms Removal.repair_attained
#print axioms Removal.repair_minimal
#print axioms Removal.blowup_distance
#print axioms Removal.exponential_choice
#print axioms Removal.counterexample
#print axioms Removal.no_polynomial_removal
end IndependentAudit
