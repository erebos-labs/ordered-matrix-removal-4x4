import OrderedMatrixRemoval4.ShiftSampling

namespace OrderedMatrixRemoval4.Host

theorem anchor_tag_mem (column : Bool) (h l k g a : Nat)
    (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6) (hg : g < 2) (ha : a < 2 ^ h) :
    .anchor l k g a ∈ axis column h := by
  have hm : 0 < 2 ^ h := Nat.pow_pos (by decide)
  let rank := anchorRank (l-1) k g
  have hrank : rank + 1 ≤ 12*h := by unfold rank anchorRank; omega
  have hi : rank * 2^h + a < 12*h*2^h := by
    have hb := Nat.mul_le_mul_right (2^h) hrank
    rw [Nat.add_mul] at hb
    omega
  have hdiv : (rank*2^h+a)/2^h = rank := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt ha]
    simp
  have hmod : (rank*2^h+a)%2^h = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have he : anchorLabel h (rank*2^h+a) = .anchor l k g a := by
    unfold anchorLabel
    rw [hdiv,hmod]
    unfold rank anchorRank
    have hs : l-1+1=l := by omega
    have hl' : (2*(6*(l-1)+k)+g)/12+1 = l := by omega
    have hk' : (2*(6*(l-1)+k)+g)%12/2 = k := by omega
    have hg' : (2*(6*(l-1)+k)+g)%12%2 = g := by omega
    dsimp only
    rw [hl',hk',hg']

  apply List.mem_append.mpr
  apply Or.inl
  exact List.mem_map.mpr ⟨rank*2^h+a,List.mem_range.mpr hi,he⟩

theorem dummy_tag_mem (column : Bool) (h a : Nat) (ha : a < 2 ^ h) :
    .dummy a ∈ axis column h := by
  have hm : .dummy a ∈ dummies h := List.mem_map.mpr ⟨a,List.mem_range.mpr ha,rfl⟩
  apply List.mem_append.mpr
  apply Or.inr
  cases column
  · exact List.mem_append.mpr (Or.inr hm)
  · exact List.mem_append.mpr (Or.inl hm)

def shiftLeaf (h : Nat) (u v : Fin (2 ^ h)) : Nat := (u.val+v.val) % 2 ^ h

def shiftNode (h : Nat) (u v : Fin (2 ^ h)) (i : Nat) : Nat :=
  ancestor (h-i) (shiftLeaf h u v)

theorem shiftNode_bound (h : Nat) (u v : Fin (2 ^ h)) (i : Nat) (hi : i ≤ h) :
    shiftNode h u v i < 2 ^ i := by
  unfold shiftNode
  rw [ancestor_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2))).mpr
  rw [← dyadic_split h i hi]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem shiftNode_root (h : Nat) (u v : Fin (2 ^ h)) : shiftNode h u v 0 = 0 := by
  unfold shiftNode
  rw [ancestor_eq_div_pow]
  exact Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by decide)))

theorem shiftNode_parent (h : Nat) (u v : Fin (2 ^ h)) (i : Nat) (hi : i < h) :
    shiftNode h u v (i+1) / 2 = shiftNode h u v i := by
  unfold shiftNode
  have he : h-i = (h-(i+1))+1 := by omega
  rw [he,ancestor]

theorem shifted_variable_mem (column : Bool) (h : Nat) (u v : Fin (2 ^ h))
    (i : Nat) (hi : i ≤ h) (sig : Bool) (seed : Fin (2 ^ h)) :
    .variable i (viewSign h i sig) (shiftNode h u v i) (seed.val%2^(h-i)) ∈ axis column h := by
  rw [variable_axis_mem_iff]
  exact ⟨hi,shiftNode_bound h u v i hi,Nat.mod_lt _ (Nat.pow_pos (by decide)),
    by intro he; simp [he,viewSign]⟩

private theorem size_pos (h : Nat) : 0 < size h :=
  Nat.mul_pos (by omega) (Nat.pow_pos (by decide))

noncomputable def pick (column : Bool) (h : Nat) (p : Position) : Fin (size h) := by
  classical
  exact if hp : p ∈ axis column h then Classical.choose (labelAt_surjective column h p hp)
    else ⟨0,size_pos h⟩

theorem pick_label (column : Bool) (h : Nat) (p : Position) (hp : p ∈ axis column h) :
    labelAt column h (pick column h p) = p := by
  classical
  unfold pick
  rw [dif_pos hp]
  exact Classical.choose_spec (labelAt_surjective column h p hp)

noncomputable def shiftPath (h : Nat) (u v : Fin (2 ^ h)) : PathSelection h where
  node := shiftNode h u v
  root := shiftNode_root h u v
  parent := shiftNode_parent h u v
  row := fun i sig => pick false h (.variable i (viewSign h i sig) (shiftNode h u v i) (u.val%2^(h-i)))
  col := fun i sig => pick true h (.variable i (viewSign h i sig) (shiftNode h u v i) (v.val%2^(h-i)))
  rowClone := fun i _ => u.val%2^(h-i)
  colClone := fun i _ => v.val%2^(h-i)
  rowLabel := fun i hi sig => pick_label false h _ (shifted_variable_mem false h u v i hi sig u)
  colLabel := fun i hi sig => pick_label true h _ (shifted_variable_mem true h u v i hi sig v)
  ra := fun l k g => pick false h (.anchor l k g u.val)
  ca := fun l k g => pick true h (.anchor l k g v.val)
  raClone := fun _ _ _ => u.val
  caClone := fun _ _ _ => v.val
  raLabel := fun l hl hlh k hk g hg => pick_label false h _ (anchor_tag_mem false h l k g u.val hl hlh hk hg u.isLt)
  caLabel := fun l hl hlh k hk g hg => pick_label true h _ (anchor_tag_mem true h l k g v.val hl hlh hk hg v.isLt)
  rd := pick false h (.dummy u.val)
  cd := pick true h (.dummy v.val)
  rdClone := u.val
  cdClone := v.val
  rdLabel := pick_label false h _ (dummy_tag_mem false h u.val u.isLt)
  cdLabel := pick_label true h _ (dummy_tag_mem true h v.val v.isLt)

def SeedInfo (h : Nat) (u v : Fin (2^h)) (column : Bool) : Position → Prop
  | .anchor _ _ _ a => a = (if column then v else u).val
  | .dummy a => a = (if column then v else u).val
  | .variable i _ q a => i ≤ h ∧ q = shiftNode h u v i ∧
      a = (if column then v else u).val % 2^(h-i)

theorem shift_selected_info (h : Nat) (u v : Fin (2^h)) (column : Bool) (x : Fin (size h))
    (hx : (shiftPath h u v).Selected column x) : SeedInfo h u v column (labelAt column h x) := by
  cases column
  · rcases hx with ⟨i,hi,sig,rfl⟩ | ⟨l,hl,hlh,k,hk,g,hg,rfl⟩ | rfl
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).rowLabel i hi sig]
      exact ⟨hi,rfl,rfl⟩
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).raLabel l hl hlh k hk g hg]
      rfl
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).rdLabel]
      rfl
  · rcases hx with ⟨i,hi,sig,rfl⟩ | ⟨l,hl,hlh,k,hk,g,hg,rfl⟩ | rfl
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).colLabel i hi sig]
      exact ⟨hi,rfl,rfl⟩
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).caLabel l hl hlh k hk g hg]
      rfl
    · try simp only [Bool.false_eq_true,↓reduceIte]
      rw [(shiftPath h u v).cdLabel]
      rfl

private theorem seed_info_fixed_row (h : Nat) (u v w : Fin (2^h)) (c : Position)
    (hv : SeedInfo h u v true c) (hw : SeedInfo h u w true c) : v = w := by
  cases c with
  | anchor l k g a => exact Fin.ext (hv.symm.trans hw)
  | dummy a => exact Fin.ext (hv.symm.trans hw)
  | «variable» i sig q a =>
    rcases hv with ⟨hi,hqv,hav⟩
    rcases hw with ⟨_,hqw,haw⟩
    apply Fin.ext
    apply shift_class_injective (2^h) (2^(h-i)) u.val v.val w.val
      (dyadic_block_divides h i hi) u.isLt v.isLt w.isLt
    · simpa [shiftNode,ancestor_eq_div_pow,shiftLeaf] using hqv.symm.trans hqw
    · exact hav.symm.trans haw

private theorem seed_info_fixed_column (h : Nat) (v u w : Fin (2^h)) (r : Position)
    (hu : SeedInfo h u v false r) (hw : SeedInfo h w v false r) : u = w := by
  cases r with
  | anchor l k g a => exact Fin.ext (hu.symm.trans hw)
  | dummy a => exact Fin.ext (hu.symm.trans hw)
  | «variable» i sig q a =>
    rcases hu with ⟨hi,hqu,hau⟩
    rcases hw with ⟨_,hqw,haw⟩
    apply Fin.ext
    apply shift_class_injective (2^h) (2^(h-i)) v.val u.val w.val
      (dyadic_block_divides h i hi) v.isLt u.isLt w.isLt
    · simpa [shiftNode,ancestor_eq_div_pow,shiftLeaf,Nat.add_comm] using hqu.symm.trans hqw
    · exact hau.symm.trans haw

theorem protected_seed_separation (h : Nat) (u v u' v' : Fin (2^h)) (r c : Position)
    (hr : SeedInfo h u v false r) (hr' : SeedInfo h u' v' false r)
    (hc : SeedInfo h u v true c) (hc' : SeedInfo h u' v' true c)
    (hp : Anchor r ∨ Anchor c ∨ Dummy r ∨ Dummy c ∨ (Root r ∧ Root c)) :
    u = u' ∧ v = v' := by
  cases r with
  | anchor l k g a =>
    have he : u = u' := Fin.ext (hr.symm.trans hr')
    subst u'
    exact ⟨rfl,seed_info_fixed_row h u v v' c hc hc'⟩
  | dummy a =>
    have he : u = u' := Fin.ext (hr.symm.trans hr')
    subst u'
    exact ⟨rfl,seed_info_fixed_row h u v v' c hc hc'⟩
  | «variable» i sig q a =>
    cases c with
    | anchor l k g b =>
      have he : v = v' := Fin.ext (hc.symm.trans hc')
      subst v'
      exact ⟨seed_info_fixed_column h v u u' _ hr hr',rfl⟩
    | dummy b =>
      have he : v = v' := Fin.ext (hc.symm.trans hc')
      subst v'
      exact ⟨seed_info_fixed_column h v u u' _ hr hr',rfl⟩
    | «variable» j tau p b =>
      have hij : i = 0 ∧ j = 0 := by simpa [Anchor,Dummy,Root] using hp
      rcases hij with ⟨rfl,rfl⟩
      simp only [SeedInfo,Nat.sub_zero,Bool.false_eq_true,↓reduceIte,Nat.mod_eq_of_lt u.isLt,Nat.mod_eq_of_lt u'.isLt] at hr hr'
      simp only [SeedInfo,Nat.sub_zero,Bool.false_eq_true,↓reduceIte,Nat.mod_eq_of_lt v.isLt,Nat.mod_eq_of_lt v'.isLt] at hc hc'
      exact ⟨Fin.ext (hr.2.2.symm.trans hr'.2.2),Fin.ext (hc.2.2.symm.trans hc'.2.2)⟩

theorem shiftPath_separates (h : Nat) (a b : Fin (2^h) × Fin (2^h)) (r c : Fin (size h))
    (hr : (shiftPath h a.1 a.2).Selected false r)
    (hc : (shiftPath h a.1 a.2).Selected true c)
    (hr' : (shiftPath h b.1 b.2).Selected false r)
    (hc' : (shiftPath h b.1 b.2).Selected true c) (hp : Protected h r c) : a = b := by
  have he := protected_seed_separation h a.1 a.2 b.1 b.2 (labelAt false h r) (labelAt true h c)
    (shift_selected_info h a.1 a.2 false r hr) (shift_selected_info h b.1 b.2 false r hr')
    (shift_selected_info h a.1 a.2 true c hc) (shift_selected_info h b.1 b.2 true c hc') hp
  exact Prod.ext he.1 he.2

/-- Unrestricted edits in either direction and at every physical cell. -/
theorem arbitrary_edit_distance (h : Nat) (hh : 1 ≤ h) (B : BinaryMatrix (size h))
    (hf : HFree H4 B) : (2^h)^2 ≤ editCount h B := by
  have hb := edit_count_of_separating_paths h hh B hf
    (cartesian (List.finRange (2^h)) (List.finRange (2^h)))
    (cartesian_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))
    (fun a => shiftPath h a.1 a.2)
    (fun a _ b _ r c hr hc hr' hc' hp => shiftPath_separates h a b r c hr hc hr' hc' hp)
  simpa [cartesian_length,Nat.pow_succ] using hb

end OrderedMatrixRemoval4.Host
