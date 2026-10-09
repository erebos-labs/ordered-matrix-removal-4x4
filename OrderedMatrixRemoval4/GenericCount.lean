import OrderedMatrixRemoval4.FiniteCounting

namespace OrderedMatrixRemoval4

namespace Counting

abbrev Embedding (n : Nat) := (Fin 4 → Fin n) × (Fin 4 → Fin n)

noncomputable def copies {n : Nat} (A : BinaryMatrix n) : List (Embedding n) := by
  classical
  exact (cartesian (assignments n 4) (assignments n 4)).filter
    fun e => decide (OrderedCopy H4 A e.1 e.2)

noncomputable def copyCount {n : Nat} (A : BinaryMatrix n) : Nat := (copies A).length

theorem mem_copies {n : Nat} (A : BinaryMatrix n) (e : Embedding n) :
    e ∈ copies A ↔ OrderedCopy H4 A e.1 e.2 := by
  classical
  rcases e with ⟨rows,cols⟩
  simp [copies,mem_cartesian,mem_assignments]

theorem copies_nodup {n : Nat} (A : BinaryMatrix n) : (copies A).Nodup := by
  classical
  exact List.Pairwise.filter _ (cartesian_nodup _ _ (assignments_nodup _ _) (assignments_nodup _ _))

def rebuild (n : Nat) (cell : Fin n × Fin n) (xs : Fin 6 → Fin n) : Embedding n :=
  (fun i => if i = 0 then xs 0 else if i = 1 then xs 1 else if i = 2 then cell.1 else xs 2,
   fun j => if j = 0 then xs 3 else if j = 1 then xs 4 else if j = 2 then xs 5 else cell.2)

def remainder (n : Nat) (e : Embedding n) : Fin 6 → Fin n := fun i =>
  if i = 0 then e.1 0 else if i = 1 then e.1 1 else if i = 2 then e.1 3
  else if i = 3 then e.2 0 else if i = 4 then e.2 1 else e.2 2

theorem rebuild_remainder (n : Nat) (e : Embedding n) :
    rebuild n (e.1 2,e.2 3) (remainder n e) = e := by
  apply Prod.ext <;> funext i
  all_goals have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rcases hi with rfl | rfl | rfl | rfl <;> simp [rebuild,remainder]

def candidates (n : Nat) (cells : List (Fin n × Fin n)) : List (Embedding n) :=
  cells.flatMap fun cell => (assignments n 6).map (rebuild n cell)

theorem candidates_length (n : Nat) (cells : List (Fin n × Fin n)) :
    (candidates n cells).length = cells.length * n ^ 6 := by
  simp [candidates,List.length_flatMap,assignments_length,List.map_const',List.sum_replicate_nat]

theorem bound_from_localization {n : Nat} (A : BinaryMatrix n) (cells : List (Fin n × Fin n))
    (hz : ∀ rows cols, OrderedCopy H4 A rows cols → (rows 2,cols 3) ∈ cells) :
    copyCount A ≤ cells.length * n ^ 6 := by
  have hs : copies A ⊆ candidates n cells := by
    intro e he
    have hc := (mem_copies A e).mp he
    exact List.mem_flatMap.mpr ⟨(e.1 2,e.2 3),hz e.1 e.2 hc,
      List.mem_map.mpr ⟨remainder n e,mem_assignments _ _ _,rebuild_remainder n e⟩⟩
  simpa only [copyCount,candidates_length] using (copies_nodup A).length_le_of_subset hs

end Counting
end OrderedMatrixRemoval4
