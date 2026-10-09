import OrderedMatrixRemoval4.Bounds
import OrderedMatrixRemoval4.Correspondence

namespace OrderedMatrixRemoval4.Host

theorem sparse_tag_members (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) (b : Fin 2) :
    .variable h true p.val 0 ∈ axis false h ∧
    .variable (h - 1) false (p.val / 2) b.val ∈ axis true h := by
  have he : h = (h - 1) + 1 := by omega
  have hp : p.val / 2 < 2 ^ (h - 1) := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
    have hepow : 2 ^ h = 2 ^ (h - 1) * 2 := by
      calc
        2 ^ h = 2 ^ ((h - 1) + 1) := congrArg (fun e => 2 ^ e) he
        _ = 2 ^ (h - 1) * 2 := Nat.pow_succ ..
    rw [← hepow]
    exact p.isLt
  constructor
  · rw [variable_axis_mem_iff]
    exact ⟨by omega,p.isLt,by simp,by simp⟩
  · rw [variable_axis_mem_iff]
    refine ⟨by omega,hp,?_,?_⟩
    · have hd : h - (h - 1) = 1 := by omega
      simpa only [hd] using b.isLt
    · intro he; omega

noncomputable def sparseCell (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) (b : Fin 2) :
    Fin (size h) × Fin (size h) :=
  (Classical.choose (labelAt_surjective false h _ (sparse_tag_members h hh p b).1),
   Classical.choose (labelAt_surjective true h _ (sparse_tag_members h hh p b).2))

theorem sparseCell_labels (h : Nat) (hh : 1 ≤ h) (p : Fin (2 ^ h)) (b : Fin 2) :
    labelAt false h (sparseCell h hh p b).1 = .variable h true p.val 0 ∧
    labelAt true h (sparseCell h hh p b).2 = .variable (h - 1) false (p.val / 2) b.val :=
  ⟨Classical.choose_spec (labelAt_surjective false h _ (sparse_tag_members h hh p b).1),
   Classical.choose_spec (labelAt_surjective true h _ (sparse_tag_members h hh p b).2)⟩

theorem sparseCell_injective (h : Nat) (hh : 1 ≤ h) (p q : Fin (2 ^ h)) (a b : Fin 2)
    (he : sparseCell h hh p a = sparseCell h hh q b) : p = q ∧ a = b := by
  have hr := congrArg (fun c => labelAt false h c.1) he
  have hc := congrArg (fun c => labelAt true h c.2) he
  rw [(sparseCell_labels h hh p a).1, (sparseCell_labels h hh q b).1] at hr
  rw [(sparseCell_labels h hh p a).2, (sparseCell_labels h hh q b).2] at hc
  exact ⟨Fin.ext (Position.variable.inj hr).2.2.1,
    Fin.ext (Position.variable.inj hc).2.2.2⟩

noncomputable def sparseCells (h : Nat) (hh : 1 ≤ h) : List (Fin (size h) × Fin (size h)) :=
  (List.finRange (2 ^ h)).flatMap fun p => (List.finRange 2).map (sparseCell h hh p)

theorem sparseCells_length (h : Nat) (hh : 1 ≤ h) :
    (sparseCells h hh).length = 2 * 2 ^ h := by
  simp [sparseCells, List.length_flatMap, List.map_const', List.sum_replicate_nat, Nat.mul_comm]

theorem sparseCells_nodup (h : Nat) (hh : 1 ≤ h) : (sparseCells h hh).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p hp
    exact List.Pairwise.map _ (fun a b hab he => hab (sparseCell_injective h hh p p a b he).2)
      (List.nodup_finRange 2)
  · apply (List.nodup_finRange (2 ^ h)).imp
    intro p q hpq x hx y hy he
    rcases List.mem_map.mp hx with ⟨a,ha,rfl⟩
    rcases List.mem_map.mp hy with ⟨b,hb,rfl⟩
    exact hpq (sparseCell_injective h hh p q a b he).1

/-- A duplicate-free enumeration of precisely the physical sparse cells,
not merely an upper bound or a list of possible labels. -/
theorem mem_sparseCells_iff (h : Nat) (hh : 1 ≤ h) (r c : Fin (size h)) :
    (r,c) ∈ sparseCells h hh ↔ sparseZero h r c := by
  constructor
  · intro hm
    rcases List.mem_flatMap.mp hm with ⟨p,hp,hm⟩
    rcases List.mem_map.mp hm with ⟨b,hb,he⟩
    have hl := sparseCell_labels h hh p b
    rw [he] at hl
    exact ⟨p.val,b.val,hl⟩
  · rintro ⟨p,b,hr,hc⟩
    have hpr := (variable_axis_mem_iff false h h true p 0).mp
      (hr ▸ List.getElem_mem (labelAt._proof_1 false h r))
    have hbc := (variable_axis_mem_iff true h (h-1) false (p/2) b).mp
      (hc ▸ List.getElem_mem (labelAt._proof_1 true h c))
    have hd : h - (h - 1) = 1 := by omega
    have hb : b < 2 := by simpa only [hd] using hbc.2.2.1
    let pp : Fin (2 ^ h) := ⟨p,hpr.2.1⟩
    let bb : Fin 2 := ⟨b,hb⟩
    have hl := sparseCell_labels h hh pp bb
    have he : sparseCell h hh pp bb = (r,c) := Prod.ext
      (labelAt_injective false h _ _ (hl.1.trans hr.symm))
      (labelAt_injective true h _ _ (hl.2.trans hc.symm))
    exact List.mem_flatMap.mpr ⟨pp,List.mem_finRange pp,
      List.mem_map.mpr ⟨bb,List.mem_finRange bb,he⟩⟩

theorem sparse_zero_is_zero (h : Nat) (hh : 1 ≤ h) (r c : Fin (size h))
    (hz : sparseZero h r c) : matrix h r c = false := by
  rcases hz with ⟨p,b,hr,hc⟩
  have hd : h ≠ h - 1 := by omega
  simp [matrix,hr,hc,entry,signed,hd]

end OrderedMatrixRemoval4.Host
