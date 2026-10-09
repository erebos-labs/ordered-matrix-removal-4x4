import OrderedMatrixRemoval4.Host

namespace OrderedMatrixRemoval4.Host

def Nonanchor : Position → Prop
  | .anchor .. => False
  | _ => True

theorem variable_row_nested (h i : Nat) (s : Bool) (p p' a a' : Nat)
    (hp : p ≤ p') (c : Position) (hc : Nonanchor c)
    (he : entry h (.variable i s p' a') c = true) :
    entry h (.variable i s p a) c = true := by
  cases c with
  | anchor => contradiction
  | dummy => rfl
  | «variable» j t q b => cases s <;> cases t <;> simp_all [entry, signed] <;> omega

theorem variable_column_nested (h j : Nat) (t : Bool) (q q' b b' : Nat)
    (hq : q ≤ q') (r : Position) (hr : Nonanchor r)
    (he : entry h r (.variable j t q b) = true) :
    entry h r (.variable j t q' b') = true := by
  cases r with
  | anchor => contradiction
  | dummy => rfl
  | «variable» i s p a => cases s <;> cases t <;> simp_all [entry, signed] <;> omega

theorem equal_parity_row_anchor_signature (h i : Nat) (s : Bool)
    (p q a b l k g z : Nat) (hp : p % 2 = q % 2) :
    entry h (.variable i s p a) (.anchor l k g z) =
      entry h (.variable i s q b) (.anchor l k g z) := by
  simp only [entry, rowRole, hp]

theorem equal_parity_column_anchor_signature (h i : Nat) (s : Bool)
    (p q a b l k g z : Nat) (hp : p % 2 = q % 2) :
    entry h (.anchor l k g z) (.variable i s p a) =
      entry h (.anchor l k g z) (.variable i s q b) := by
  simp only [entry, columnRole, hp]

theorem anchor_row_twins (h l k g a b : Nat) (c : Position) :
    entry h (.anchor l k g a) c = entry h (.anchor l k g b) c := by
  cases c <;> rfl

theorem anchor_column_twins (h l k g a b : Nat) (r : Position) :
    entry h r (.anchor l k g a) = entry h r (.anchor l k g b) := by
  cases r <;> rfl

theorem variable_row_twins (h i : Nat) (s : Bool) (p a b : Nat) (c : Position) :
    entry h (.variable i s p a) c = entry h (.variable i s p b) c := by
  cases c <;> rfl

theorem variable_column_twins (h i : Nat) (s : Bool) (p a b : Nat) (r : Position) :
    entry h r (.variable i s p a) = entry h r (.variable i s p b) := by
  cases r <;> rfl

end OrderedMatrixRemoval4.Host
