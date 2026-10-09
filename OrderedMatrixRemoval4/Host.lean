import OrderedMatrixRemoval4.Semantics
import OrderedMatrixRemoval4.Arithmetic

/-!
The two-group host of report.tex, Section 3. Newly written implementation;
mathematical provenance is recorded in NOTICE.md. Levels here are one-based
for modes and zero-based for variable blocks. A leaf has one physical tag.
The two axes have independent depth-first traversals.
-/
namespace OrderedMatrixRemoval4
namespace Host

inductive Position where
  | anchor (level kind group clone : Nat)
  | variable (depth : Nat) (plus : Bool) (node clone : Nat)
  | dummy (clone : Nat)
  deriving DecidableEq, Repr

def signed (h depth : Nat) (actual wanted : Bool) : Prop :=
  actual = wanted ∨ depth = h

instance (h depth : Nat) (actual wanted : Bool) :
    Decidable (signed h depth actual wanted) := inferInstanceAs
      (Decidable (actual = wanted ∨ depth = h))

def rowRole (h l k g : Nat) (r : Position) : Prop :=
  match r with
  | .anchor .. => False
  | .dummy _ => (k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) ∧ g = 1
  | .variable j s p _ =>
    (k = 0 ∧ ((g = 0 ∧ j = l ∧ signed h j s true) ∨
               (g = 1 ∧ j + 1 = l ∧ signed h j s true))) ∨
    (k = 1 ∧ ((g = 0 ∧ j + 1 = l ∧ signed h j s false) ∨
               (g = 1 ∧ j = l ∧ signed h j s false))) ∨
    ((k = 2 ∨ k = 3) ∧ g = 0 ∧ j = l ∧
      signed h j s true ∧ p % 2 = k - 2) ∨
    ((k = 4 ∨ k = 5) ∧ g = 0 ∧ j = l ∧
      signed h j s false ∧ p % 2 = k - 4)

def columnRole (h l k g : Nat) (c : Position) : Prop :=
  match c with
  | .anchor .. => False
  | .dummy _ => (k = 0 ∨ k = 1) ∧ g = 0
  | .variable j s p _ =>
    (k = 0 ∧ g = 1 ∧ j + 1 = l ∧ signed h j s true) ∨
    (k = 1 ∧ g = 1 ∧ j + 1 = l ∧ signed h j s false) ∨
    ((k = 2 ∨ k = 3) ∧
      ((g = 0 ∧ j + 1 = l ∧ signed h j s true) ∨
       (g = 1 ∧ j = l ∧ signed h j s true ∧ p % 2 = k - 2))) ∨
    ((k = 4 ∨ k = 5) ∧
      ((g = 0 ∧ j = l ∧ signed h j s false ∧ p % 2 = k - 4) ∨
       (g = 1 ∧ j + 1 = l ∧ signed h j s false)))

instance (h l k g : Nat) (r : Position) : Decidable (rowRole h l k g r) := by
  cases r <;> unfold rowRole <;> infer_instance
instance (h l k g : Nat) (c : Position) : Decidable (columnRole h l k g c) := by
  cases c <;> unfold columnRole <;> infer_instance

def entry (h : Nat) (r c : Position) : Bool :=
  match r, c with
  | .anchor l k g _, .anchor l' k' g' _ => decide (l = l' ∧ k = k' ∧ g ≠ g')
  | .anchor l k g _, c => decide (columnRole h l k g c)
  | r, .anchor l k g _ => decide (rowRole h l k g r)
  | .dummy _, _ | _, .dummy _ => true
  | .variable i s p _, .variable j t q _ => decide (
      (i = j ∧ signed h i s true ∧ signed h j t true ∧ p ≤ q) ∨
      (i = j ∧ i < h ∧ s = false ∧ t = false ∧ p < q) ∨
      (i = j + 1 ∧ signed h i s true ∧ t = true ∧ p / 2 ≤ q) ∨
      (i = j + 1 ∧ signed h i s false ∧ t = false ∧ p / 2 < q))

def block (depth : Nat) (plus : Bool) (node size : Nat) : List Position :=
  (List.range size).map (Position.variable depth plus node)

/-- `column=false`: minus opens and plus closes. The column signs reverse. -/
def tree (column : Bool) : Nat → Nat → Nat → List Position
  | 0, depth, node => [.variable depth true node 0]
  | rem + 1, depth, node =>
      block depth column node (2 ^ (rem + 1)) ++
      tree column rem (depth + 1) (2 * node) ++
      tree column rem (depth + 1) (2 * node + 1) ++
      block depth (!column) node (2 ^ (rem + 1))

/-- Consecutive clones, groups, kinds, then levels, in the prescribed order. -/
def anchorLabel (h index : Nat) : Position :=
  let u := index / 2 ^ h
  .anchor (u / 12 + 1) (u % 12 / 2) (u % 12 % 2) (index % 2 ^ h)

def anchors (h : Nat) : List Position :=
  (List.range (12 * h * 2 ^ h)).map (anchorLabel h)

def dummies (h : Nat) : List Position :=
  (List.range (2 ^ h)).map Position.dummy

def nonanchors (column : Bool) (h : Nat) : List Position :=
  if column then dummies h ++ tree true h 0 0
  else tree false h 0 0 ++ dummies h

def axis (column : Bool) (h : Nat) : List Position :=
  anchors h ++ nonanchors column h

def size (h : Nat) : Nat := (14 * h + 2) * 2 ^ h

@[simp] theorem block_length (depth : Nat) (plus : Bool) (node size : Nat) :
    (block depth plus node size).length = size := by simp [block]

theorem tree_length (column : Bool) (rem depth node : Nat) :
    (tree column rem depth node).length = (2 * rem + 1) * 2 ^ rem := by
  induction rem generalizing depth node with
  | zero => simp [tree]
  | succ rem ih =>
    simp only [tree, List.length_append, block_length, ih, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_add]
    simp only [Nat.mul_assoc]
    simp only [← Nat.mul_assoc rem (2 ^ rem) 2]
    omega

theorem anchors_length (h : Nat) : (anchors h).length = 12 * h * 2 ^ h := by
  simp [anchors]

theorem axis_length (column : Bool) (h : Nat) : (axis column h).length = size h := by
  cases column <;>
    simp only [axis, nonanchors, Bool.false_eq_true, ↓reduceIte, List.length_append, anchors_length,
      dummies, List.length_map, List.length_range, tree_length, size]
  all_goals simp only [Nat.add_mul, Nat.mul_assoc]
  all_goals omega

def labelAt (column : Bool) (h : Nat) (i : Fin (size h)) : Position :=
  (axis column h)[i.val]'(by rw [axis_length]; exact i.isLt)

theorem labelAt_append (column : Bool) (h : Nat) (j : Fin (size h)) :
    labelAt column h j = (anchors h ++ nonanchors column h)[j.val]'(by
      change j.val < (axis column h).length
      rw [axis_length]; exact j.isLt) := rfl

/-- The ordinary matrix indexed by independently ordered `Fin n` axes. -/
def matrix (h : Nat) : BinaryMatrix (size h) := fun r c =>
  entry h (labelAt false h r) (labelAt true h c)

def Copy (h : Nat) (rows cols : Fin 4 → Fin (size h)) : Prop :=
  OrderedCopy H4 (matrix h) rows cols

def sparseZero (h : Nat) (r c : Fin (size h)) : Prop :=
  ∃ p b, labelAt false h r = .variable h true p 0 ∧
    labelAt true h c = .variable (h - 1) false (p / 2) b

/-- The sign views coincide literally, not merely in their matrix entries. -/
def signedPosition (h depth : Nat) (plus : Bool) (node clone : Nat) : Position :=
  .variable depth (if depth = h then true else plus) node clone

@[simp] theorem leaf_sign_identification (h p a : Nat) :
    signedPosition h h false p a = signedPosition h h true p a := by
  simp [signedPosition]

end Host
end OrderedMatrixRemoval4
