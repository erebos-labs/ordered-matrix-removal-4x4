import OrderedMatrixRemoval4.SelectionFamily
import OrderedMatrixRemoval4.GenericCount

namespace OrderedMatrixRemoval4

namespace Blowup

def liftIndex (n t : Nat) (ht : 1 ≤ t) (r : Fin n) (a : Fin t) : Fin (n*t) :=
  ⟨r.val*t+a.val,by
    have hb := Nat.mul_le_mul_right t (Nat.succ_le_of_lt r.isLt)
    rw [Nat.succ_mul] at hb
    omega⟩

def project (n t : Nat) (ht : 1 ≤ t) (r : Fin (n*t)) : Fin n :=
  ⟨r.val/t,(Nat.div_lt_iff_lt_mul (by omega : 0 < t)).mpr r.isLt⟩

theorem project_lift (n t : Nat) (ht : 1 ≤ t) (r : Fin n) (a : Fin t) :
    project n t ht (liftIndex n t ht r a) = r := by
  apply Fin.ext
  dsimp [project,liftIndex]
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega : 0 < t),Nat.div_eq_of_lt a.isLt]
  simp

theorem lift_clone (n t : Nat) (ht : 1 ≤ t) (r : Fin n) (a : Fin t) :
    (liftIndex n t ht r a).val % t = a.val := by
  simp [liftIndex,Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt a.isLt]

theorem lift_index_injective (n t : Nat) (ht : 1 ≤ t) (r q : Fin n) (a b : Fin t)
    (he : liftIndex n t ht r a = liftIndex n t ht q b) : r = q ∧ a = b := by
  have hp := congrArg (project n t ht) he
  have hc := congrArg (fun x => x.val%t) he
  rw [project_lift,project_lift] at hp
  rw [lift_clone,lift_clone] at hc
  exact ⟨hp,Fin.ext hc⟩

theorem lift_strict (n t : Nat) (ht : 1 ≤ t) (r q : Fin n) (a b : Fin t)
    (hrq : r.val < q.val) : (liftIndex n t ht r a).val < (liftIndex n t ht q b).val := by
  have hm := Nat.mul_le_mul_right t (Nat.succ_le_of_lt hrq)
  dsimp [liftIndex]
  rw [Nat.succ_mul] at hm
  omega

def matrix {n : Nat} (A : BinaryMatrix n) (t : Nat) (ht : 1 ≤ t) : BinaryMatrix (n*t) :=
  fun r c => A (project n t ht r) (project n t ht c)

def slice {n t : Nat} (ht : 1 ≤ t) (B : BinaryMatrix (n*t)) (a b : Fin t) : BinaryMatrix n :=
  fun r c => B (liftIndex n t ht r a) (liftIndex n t ht c b)

theorem slice_copy_lifts {n t : Nat} (ht : 1 ≤ t) (B : BinaryMatrix (n*t)) (a b : Fin t)
    (rows cols : Fin 4 → Fin n) (hc : OrderedCopy H4 (slice ht B a b) rows cols) :
    OrderedCopy H4 B (fun i => liftIndex n t ht (rows i) a)
      (fun j => liftIndex n t ht (cols j) b) := by
  exact ⟨fun i j hij => lift_strict n t ht _ _ a a (hc.1 i j hij),
    fun i j hij => lift_strict n t ht _ _ b b (hc.2.1 i j hij),hc.2.2⟩

theorem free_slice {n t : Nat} (ht : 1 ≤ t) (B : BinaryMatrix (n*t))
    (hf : HFree H4 B) (a b : Fin t) : HFree H4 (slice ht B a b) := by
  intro rows cols hc
  exact hf _ _ (slice_copy_lifts ht B a b rows cols hc)

noncomputable def edits {n : Nat} (A B : BinaryMatrix n) : List (Fin n × Fin n) := by
  classical
  exact (cartesian (List.finRange n) (List.finRange n)).filter fun e => decide (B e.1 e.2 ≠ A e.1 e.2)

noncomputable def editCount {n : Nat} (A B : BinaryMatrix n) : Nat := (edits A B).length

theorem mem_edits {n : Nat} (A B : BinaryMatrix n) (r c : Fin n) :
    (r,c) ∈ edits A B ↔ B r c ≠ A r c := by
  classical
  simp [edits,mem_cartesian,List.mem_finRange]

theorem edits_nodup {n : Nat} (A B : BinaryMatrix n) : (edits A B).Nodup := by
  classical
  exact List.Pairwise.filter _ (cartesian_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))

def liftCell (n t : Nat) (ht : 1 ≤ t) (a b : Fin t) (cell : Fin n × Fin n) : Fin (n*t) × Fin (n*t) :=
  (liftIndex n t ht cell.1 a,liftIndex n t ht cell.2 b)

theorem liftCell_injective (n t : Nat) (ht : 1 ≤ t) (a b c d : Fin t)
    (x y : Fin n × Fin n) (he : liftCell n t ht a b x = liftCell n t ht c d y) :
    a = c ∧ b = d ∧ x = y := by
  have hr := lift_index_injective n t ht x.1 y.1 a c (congrArg Prod.fst he)
  have hc := lift_index_injective n t ht x.2 y.2 b d (congrArg Prod.snd he)
  exact ⟨hr.2,hc.2,Prod.ext hr.1 hc.1⟩

noncomputable def sliceEdits (h t : Nat) (ht : 1 ≤ t)
    (B : BinaryMatrix (Host.size h*t)) : List (Fin (Host.size h*t) × Fin (Host.size h*t)) :=
  (cartesian (List.finRange t) (List.finRange t)).flatMap fun ab =>
    (Host.edits h (slice ht B ab.1 ab.2)).map (liftCell (Host.size h) t ht ab.1 ab.2)

theorem sliceEdits_nodup (h t : Nat) (ht : 1 ≤ t) (B : BinaryMatrix (Host.size h*t)) :
    (sliceEdits h t ht B).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro ab hab
    apply List.Pairwise.map _ _ (Host.edits_nodup h _)
    intro x y hxy he
    exact hxy (liftCell_injective _ _ ht _ _ _ _ x y he).2.2
  · apply (cartesian_nodup _ _ (List.nodup_finRange t) (List.nodup_finRange t)).imp
    intro ab cd hab x hx y hy he
    rcases List.mem_map.mp hx with ⟨e,he',rfl⟩
    rcases List.mem_map.mp hy with ⟨f,hf',rfl⟩
    have hi := liftCell_injective _ _ ht _ _ _ _ e f he
    exact hab (Prod.ext hi.1 hi.2.1)

theorem sliceEdits_subset (h t : Nat) (ht : 1 ≤ t) (B : BinaryMatrix (Host.size h*t)) :
    sliceEdits h t ht B ⊆ edits (matrix (Host.matrix h) t ht) B := by
  intro cell hc
  rcases List.mem_flatMap.mp hc with ⟨ab,hab,hc⟩
  rcases List.mem_map.mp hc with ⟨e,he,rfl⟩
  apply (mem_edits _ B _ _).mpr
  have hb := (Host.mem_edits h (slice ht B ab.1 ab.2) e.1 e.2).mp he
  simpa only [matrix,liftCell,project_lift,slice] using hb

private theorem length_mul_le_sum_map {α : Type} (xs : List α) (f : α → Nat) (k : Nat)
    (hf : ∀ a ∈ xs, k ≤ f a) : xs.length*k ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a (by simp)
    have hb := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    simpa only [List.length_cons,List.map_cons,List.sum_cons,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add ha hb

/-- Every uniform consecutive t-fold blowup retains the same normalized
arbitrary-edit distance. Constant-clone sections partition the physical edits. -/
theorem arbitrary_edit_distance (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (B : BinaryMatrix (Host.size h*t)) (hf : HFree H4 B) :
    (t*2^h)^2 ≤ editCount (matrix (Host.matrix h) t ht) B := by
  have hsum := length_mul_le_sum_map
    (cartesian (List.finRange t) (List.finRange t))
    (fun ab => Host.editCount h (slice ht B ab.1 ab.2)) ((2^h)^2)
    (fun ab _ => Host.arbitrary_edit_distance h hh _ (free_slice ht B hf ab.1 ab.2))
  have hlen : (t*2^h)^2 ≤ (sliceEdits h t ht B).length := by
    unfold sliceEdits
    simp only [List.length_flatMap,List.length_map]
    have he : (t*2^h)^2 = (t*t)*((2^h)^2) := by
      simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
      ac_rfl
    rw [he]
    simpa only [cartesian_length,List.length_finRange,Host.editCount] using hsum
  exact Nat.le_trans hlen ((sliceEdits_nodup h t ht B).length_le_of_subset (sliceEdits_subset h t ht B))

theorem project_copy {n : Nat} (A : BinaryMatrix n) (t : Nat) (ht : 1 ≤ t)
    (rows cols : Fin 4 → Fin (n*t)) (hc : OrderedCopy H4 (matrix A t ht) rows cols) :
    OrderedCopy H4 A (fun i => project n t ht (rows i)) (fun j => project n t ht (cols j)) := by
  refine ⟨?_,?_,hc.2.2⟩
  · intro i j hij
    have hle := Nat.div_le_div_right (c := t) (Nat.le_of_lt (hc.1 i j hij))
    have hne : (project n t ht (rows i)).val ≠ (project n t ht (rows j)).val := by
      intro he
      have hp : project n t ht (rows i) = project n t ht (rows j) := Fin.ext he
      have hij' : i ≠ j := by intro he; subst j; omega
      rcases pattern_rows_distinct i j hij' with ⟨c,hpattern⟩
      have hm1 := hc.2.2 i c
      have hm2 := hc.2.2 j c
      change A (project n t ht (rows i)) (project n t ht (cols c)) = H4 i c at hm1
      change A (project n t ht (rows j)) (project n t ht (cols c)) = H4 j c at hm2
      rw [hp] at hm1
      exact hpattern (hm1.symm.trans hm2)
    change (rows i).val/t < (rows j).val/t
    change (rows i).val/t ≠ (rows j).val/t at hne
    omega
  · intro i j hij
    have hle := Nat.div_le_div_right (c := t) (Nat.le_of_lt (hc.2.1 i j hij))
    have hne : (project n t ht (cols i)).val ≠ (project n t ht (cols j)).val := by
      intro he
      have hp : project n t ht (cols i) = project n t ht (cols j) := Fin.ext he
      have hij' : i ≠ j := by intro he; subst j; omega
      rcases pattern_columns_distinct i j hij' with ⟨r,hpattern⟩
      have hm1 := hc.2.2 r i
      have hm2 := hc.2.2 r j
      change A (project n t ht (rows r)) (project n t ht (cols i)) = H4 r i at hm1
      change A (project n t ht (rows r)) (project n t ht (cols j)) = H4 r j at hm2
      rw [hp] at hm1
      exact hpattern (hm1.symm.trans hm2)
    change (cols i).val/t < (cols j).val/t
    change (cols i).val/t ≠ (cols j).val/t at hne
    omega

def cloneOf (n t : Nat) (ht : 1 ≤ t) (r : Fin (n*t)) : Fin t :=
  ⟨r.val%t,Nat.mod_lt _ (by omega)⟩

theorem lift_project_clone (n t : Nat) (ht : 1 ≤ t) (r : Fin (n*t)) :
    liftIndex n t ht (project n t ht r) (cloneOf n t ht r) = r := by
  apply Fin.ext
  dsimp [liftIndex,project,cloneOf]
  have he := Nat.mod_add_div r.val t
  simpa only [Nat.add_comm,Nat.mul_comm] using he

noncomputable def liftedSparse (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    List (Fin (Host.size h*t) × Fin (Host.size h*t)) :=
  (Host.sparseCells h hh).flatMap fun cell =>
    (cartesian (List.finRange t) (List.finRange t)).map fun ab =>
      liftCell (Host.size h) t ht ab.1 ab.2 cell

theorem liftedSparse_length (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    (liftedSparse h t hh ht).length = (2*2^h)*(t*t) := by
  simp [liftedSparse,List.length_flatMap,cartesian_length,List.map_const',
    List.sum_replicate_nat,Host.sparseCells_length]

theorem blowup_localization (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (rows cols : Fin 4 → Fin (Host.size h*t))
    (hc : OrderedCopy H4 (matrix (Host.matrix h) t ht) rows cols) :
    (rows 2,cols 3) ∈ liftedSparse h t hh ht := by
  have hproject := project_copy (Host.matrix h) t ht rows cols hc
  have hz := Host.all_copy_localization h hh _ _ hproject
  apply List.mem_flatMap.mpr
  refine ⟨(project (Host.size h) t ht (rows 2),project (Host.size h) t ht (cols 3)),
    (Host.mem_sparseCells_iff h hh _ _).mpr hz,?_⟩
  apply List.mem_map.mpr
  refine ⟨(cloneOf (Host.size h) t ht (rows 2),cloneOf (Host.size h) t ht (cols 3)),
    (mem_cartesian _ _ _ _).mpr ⟨List.mem_finRange _,List.mem_finRange _⟩,?_⟩
  exact Prod.ext (lift_project_clone _ _ ht _) (lift_project_clone _ _ ht _)

/-- All ordinary ordered copies in every uniform consecutive blowup. -/
theorem copy_count_bound (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    Counting.copyCount (matrix (Host.matrix h) t ht) ≤
      (2*2^h)*(t*t)*(Host.size h*t)^6 := by
  have hb := Counting.bound_from_localization (matrix (Host.matrix h) t ht)
    (liftedSparse h t hh ht) (fun rows cols hc => blowup_localization h t hh ht rows cols hc)
  simpa only [liftedSparse_length] using hb

end Blowup
end OrderedMatrixRemoval4
