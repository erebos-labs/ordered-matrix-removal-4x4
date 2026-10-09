import OrderedMatrixRemoval4.Sparse
import OrderedMatrixRemoval4.FiniteCounting

namespace OrderedMatrixRemoval4.Host

abbrev Embedding (h : Nat) := (Fin 4 → Fin (size h)) × (Fin 4 → Fin (size h))

noncomputable def copies (h : Nat) : List (Embedding h) := by
  classical
  exact (cartesian (assignments (size h) 4) (assignments (size h) 4)).filter
    fun e => decide (Copy h e.1 e.2)

noncomputable def copyCount (h : Nat) : Nat := (copies h).length

theorem mem_copies (h : Nat) (e : Embedding h) : e ∈ copies h ↔ Copy h e.1 e.2 := by
  classical
  rcases e with ⟨rows,cols⟩
  simp [copies,mem_cartesian,mem_assignments]

theorem copies_nodup (h : Nat) : (copies h).Nodup := by
  classical
  exact List.Pairwise.filter _ (cartesian_nodup _ _ (assignments_nodup _ _) (assignments_nodup _ _))

def rebuild (h : Nat) (cell : Fin (size h) × Fin (size h))
    (xs : Fin 6 → Fin (size h)) : Embedding h :=
  (fun i => if i = 0 then xs 0 else if i = 1 then xs 1 else if i = 2 then cell.1 else xs 2,
   fun j => if j = 0 then xs 3 else if j = 1 then xs 4 else if j = 2 then xs 5 else cell.2)

def remainder (h : Nat) (e : Embedding h) : Fin 6 → Fin (size h) := fun i =>
  if i = 0 then e.1 0 else if i = 1 then e.1 1 else if i = 2 then e.1 3
  else if i = 3 then e.2 0 else if i = 4 then e.2 1 else e.2 2

theorem rebuild_remainder (h : Nat) (e : Embedding h) :
    rebuild h (e.1 2,e.2 3) (remainder h e) = e := by
  apply Prod.ext <;> funext i
  all_goals have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rcases hi with rfl | rfl | rfl | rfl <;> simp [rebuild,remainder]

noncomputable def copyCandidates (h : Nat) (hh : 1 ≤ h) : List (Embedding h) :=
  (sparseCells h hh).flatMap fun cell => (assignments (size h) 6).map (rebuild h cell)

theorem copyCandidates_length (h : Nat) (hh : 1 ≤ h) :
    (copyCandidates h hh).length = 2 * 2 ^ h * (size h) ^ 6 := by
  simp [copyCandidates,List.length_flatMap,assignments_length,List.map_const',
    List.sum_replicate_nat,sparseCells_length]

theorem copies_subset_candidates (h : Nat) (hh : 1 ≤ h) : copies h ⊆ copyCandidates h hh := by
  intro e he
  have hc := (mem_copies h e).mp he
  have hz := all_copy_localization h hh e.1 e.2 hc
  exact List.mem_flatMap.mpr ⟨(e.1 2,e.2 3),(mem_sparseCells_iff h hh _ _).mpr hz,
    List.mem_map.mpr ⟨remainder h e,mem_assignments _ _ _,rebuild_remainder h e⟩⟩

/-- Counts all independently increasing embeddings matching all 16 bits.
The candidate list can contain extra noncopies; this only enlarges the bound. -/
theorem copy_count_bound (h : Nat) (hh : 1 ≤ h) :
    copyCount h ≤ 2 * 2 ^ h * (size h) ^ 6 := by
  have hb := (copies_nodup h).length_le_of_subset (copies_subset_candidates h hh)
  simpa only [copyCount,copyCandidates_length] using hb

end OrderedMatrixRemoval4.Host
