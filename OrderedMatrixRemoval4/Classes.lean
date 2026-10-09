import OrderedMatrixRemoval4.Crown

namespace OrderedMatrixRemoval4.Host

def Valid (h : Nat) : Position → Prop
  | .variable i s _ _ => i ≤ h ∧ (i = h → s = true)
  | _ => True

def SameClass : Position → Position → Prop
  | .variable i s _ _, .variable j t _ _ => i = j ∧ s = t
  | .dummy _, .dummy _ => True
  | _, _ => False

theorem labelAt_valid (column : Bool) (h : Nat) (j : Fin (size h)) :
    Valid h (labelAt column h j) := by
  have hm := List.getElem_mem (labelAt._proof_1 column h j)
  change labelAt column h j ∈ axis column h at hm
  generalize he : labelAt column h j = p at hm ⊢
  cases p with
  | anchor => trivial
  | dummy => trivial
  | «variable» i s q a => exact variable_tag_valid column h i s q a hm

theorem column_role_same_class (h l k g : Nat) (r c : Position)
    (vr : Valid h r) (vc : Valid h c)
    (hr : columnRole h l k g r) (hc : columnRole h l k g c) : SameClass r c := by
  cases r with
  | anchor => contradiction
  | dummy =>
    cases c with
    | anchor => contradiction
    | dummy => trivial
    | «variable» j t q b => cases t <;> simp_all [Valid, columnRole, SameClass, signed] <;> omega
  | «variable» i s p a =>
    cases c with
    | anchor => contradiction
    | dummy => cases s <;> simp_all [Valid, columnRole, SameClass, signed] <;> omega
    | «variable» j t q b => cases s <;> cases t <;> simp_all [Valid, columnRole, SameClass, signed] <;> omega

theorem row_role_same_class (h l k g : Nat) (r c : Position)
    (vr : Valid h r) (vc : Valid h c)
    (hr : rowRole h l k g r) (hc : rowRole h l k g c) : SameClass r c := by
  cases r with
  | anchor => contradiction
  | dummy =>
    cases c with
    | anchor => contradiction
    | dummy => trivial
    | «variable» j t q b => cases t <;> simp_all [Valid, rowRole, SameClass, signed] <;> omega
  | «variable» i s p a =>
    cases c with
    | anchor => contradiction
    | dummy => cases s <;> simp_all [Valid, rowRole, SameClass, signed] <;> omega
    | «variable» j t q b => cases s <;> cases t <;> simp_all [Valid, rowRole, SameClass, signed] <;> omega

theorem sameClass_trans (a b c : Position) (hab : SameClass a b) (hbc : SameClass b c) :
    SameClass a c := by
  cases a <;> cases b <;> cases c <;> simp_all [SameClass]

theorem dummy_nonanchor_entry (h a : Nat) (c : Position) (hc : Nonanchor c) :
    entry h (.dummy a) c = true := by
  cases c <;> simp_all [Nonanchor, entry]

theorem same_class_rows_no_cross (h : Nat) (r s c d : Position)
    (hclass : SameClass r s) (hc : Nonanchor c) (hd : Nonanchor d)
    (h00 : entry h r c = true) (h10 : entry h s c = false)
    (h01 : entry h r d = false) (h11 : entry h s d = true) : False := by
  cases r with
  | anchor => contradiction
  | dummy a => rw [dummy_nonanchor_entry h a d hd] at h01; contradiction
  | «variable» i sig p a =>
    cases s with
    | anchor => contradiction
    | dummy => contradiction
    | «variable» j tau q b =>
      rcases hclass with ⟨rfl, rfl⟩
      rcases Nat.le_total p q with hle | hle
      · have hn := variable_row_nested h i sig p q a b hle d hd h11
        rw [h01] at hn
        contradiction
      · have hn := variable_row_nested h i sig q p b a hle c hc h00
        rw [h10] at hn
        contradiction

def parityKey : Position → Nat
  | .variable _ _ p _ => p % 2
  | _ => 0

theorem parityKey_bound (p : Position) : parityKey p < 2 := by
  cases p <;> simp only [parityKey] <;> omega

def RowAnchorTraceEqual (h : Nat) (r s : Position) : Prop :=
  ∀ l k g a, entry h r (.anchor l k g a) = entry h s (.anchor l k g a)

theorem same_class_parity_row_signature (h : Nat) (r s : Position)
    (hclass : SameClass r s) (hpar : parityKey r = parityKey s) :
    RowAnchorTraceEqual h r s := by
  cases r with
  | anchor => contradiction
  | dummy =>
    cases s with
    | anchor => contradiction
    | dummy => intro l k g a; rfl
    | «variable» => contradiction
  | «variable» i sig p a =>
    cases s with
    | anchor => contradiction
    | dummy => contradiction
    | «variable» j tau q b =>
      rcases hclass with ⟨rfl, rfl⟩
      intro l k g z
      exact equal_parity_row_anchor_signature h i sig p q a b l k g z hpar

theorem same_class_three_row_signatures (h : Nat) (r s t : Position)
    (hrs : SameClass r s) (hrt : SameClass r t) (hst : SameClass s t) :
    RowAnchorTraceEqual h r s ∨ RowAnchorTraceEqual h r t ∨ RowAnchorTraceEqual h s t := by
  have hb0 := parityKey_bound r
  have hb1 := parityKey_bound s
  have hb2 := parityKey_bound t
  have he : parityKey r = parityKey s ∨ parityKey r = parityKey t ∨ parityKey s = parityKey t := by omega
  rcases he with he | he | he
  · exact Or.inl (same_class_parity_row_signature h r s hrs he)
  · exact Or.inr (Or.inl (same_class_parity_row_signature h r t hrt he))
  · exact Or.inr (Or.inr (same_class_parity_row_signature h s t hst he))

theorem sameClass_symm (a b : Position) (hab : SameClass a b) : SameClass b a := by
  cases a <;> cases b <;> simp_all [SameClass, and_comm]

theorem same_class_columns_no_cross (h : Nat) (c d r s : Position)
    (hclass : SameClass c d) (hr : Nonanchor r) (hs : Nonanchor s)
    (h00 : entry h r c = true) (h01 : entry h r d = false)
    (h10 : entry h s c = false) (h11 : entry h s d = true) : False := by
  cases c with
  | anchor => contradiction
  | dummy a =>
    cases s <;> simp_all [Nonanchor, entry]
  | «variable» i sig p a =>
    cases d with
    | anchor => contradiction
    | dummy => contradiction
    | «variable» j tau q b =>
      rcases hclass with ⟨rfl, rfl⟩
      rcases Nat.le_total p q with hle | hle
      · have hn := variable_column_nested h i sig p q a b hle r hr h00
        rw [h01] at hn
        contradiction
      · have hn := variable_column_nested h i sig q p b a hle s hs h11
        rw [h10] at hn
        contradiction

def ColumnAnchorTraceEqual (h : Nat) (c d : Position) : Prop :=
  ∀ l k g a, entry h (.anchor l k g a) c = entry h (.anchor l k g a) d

theorem same_class_parity_column_signature (h : Nat) (r s : Position)
    (hclass : SameClass r s) (hpar : parityKey r = parityKey s) :
    ColumnAnchorTraceEqual h r s := by
  cases r with
  | anchor => contradiction
  | dummy =>
    cases s with
    | anchor => contradiction
    | dummy => intro l k g a; rfl
    | «variable» => contradiction
  | «variable» i sig p a =>
    cases s with
    | anchor => contradiction
    | dummy => contradiction
    | «variable» j tau q b =>
      rcases hclass with ⟨rfl, rfl⟩
      intro l k g z
      exact equal_parity_column_anchor_signature h i sig p q a b l k g z hpar

theorem same_class_three_column_signatures (h : Nat) (r s t : Position)
    (hrs : SameClass r s) (hrt : SameClass r t) (hst : SameClass s t) :
    ColumnAnchorTraceEqual h r s ∨ ColumnAnchorTraceEqual h r t ∨ ColumnAnchorTraceEqual h s t := by
  have hb0 := parityKey_bound r
  have hb1 := parityKey_bound s
  have hb2 := parityKey_bound t
  have he : parityKey r = parityKey s ∨ parityKey r = parityKey t ∨ parityKey s = parityKey t := by omega
  rcases he with he | he | he
  · exact Or.inl (same_class_parity_column_signature h r s hrs he)
  · exact Or.inr (Or.inl (same_class_parity_column_signature h r t hrt he))
  · exact Or.inr (Or.inr (same_class_parity_column_signature h s t hst he))

end OrderedMatrixRemoval4.Host
