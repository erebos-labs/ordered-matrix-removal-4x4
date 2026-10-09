import Lean

/-!
Semantic groundwork only. These definitions and finite pattern properties do
not certify the all-depth localization or removal theorem. New code written
for this local effort; mathematical candidate and semantics credited in NOTICE.
-/

namespace OrderedMatrixRemoval4

abbrev BinaryMatrix (n : Nat) := Fin n → Fin n → Bool

def H4 : BinaryMatrix 4 := fun r c =>
  match r.val, c.val with
  | 0, 1 | 0, 2 | 1, 0 | 1, 3 | 2, 0 | 2, 2 | 3, 1 | 3, 2 | 3, 3 => true
  | _, _ => false

def Increasing {k n : Nat} (f : Fin k → Fin n) : Prop :=
  ∀ i j, i.val < j.val → (f i).val < (f j).val

def Matches {k n : Nat} (H : BinaryMatrix k) (A : BinaryMatrix n)
    (rows cols : Fin k → Fin n) : Prop :=
  ∀ r c, A (rows r) (cols c) = H r c

def OrderedCopy {k n : Nat} (H : BinaryMatrix k) (A : BinaryMatrix n)
    (rows cols : Fin k → Fin n) : Prop :=
  Increasing rows ∧ Increasing cols ∧ Matches H A rows cols

def HFree {k n : Nat} (H : BinaryMatrix k) (A : BinaryMatrix n) : Prop :=
  ∀ rows cols, ¬ OrderedCopy H A rows cols

theorem pattern_rows_distinct :
    ∀ r s : Fin 4, r ≠ s → ∃ c : Fin 4, H4 r c ≠ H4 s c := by
  decide

theorem pattern_columns_distinct :
    ∀ c d : Fin 4, c ≠ d → ∃ r : Fin 4, H4 r c ≠ H4 r d := by
  decide

theorem localized_pattern_coordinate_is_zero : H4 2 3 = false := by
  rfl

end OrderedMatrixRemoval4
