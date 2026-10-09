import OrderedMatrixRemoval4.ParentOrder

namespace OrderedMatrixRemoval4.Host

theorem ancestor_add (a b p : Nat) : ancestor a (ancestor b p) = ancestor (a + b) p := by
  induction a with
  | zero => simp [ancestor]
  | succ a ih => simpa only [ancestor, Nat.succ_add] using congrArg (fun n => n / 2) ih

theorem lt_of_ancestor_lt (d p q : Nat) (he : ancestor d p < ancestor d q) : p < q := by
  by_cases hp : p < q
  · exact hp
  · have hm := ancestor_mono d q p (by omega)
    omega

/-- An earlier subtree gives strict node separation at the shallower level. -/
theorem separated_ancestors (base i j p q l r : Nat)
    (hi : base ≤ i) (hj : base ≤ j) (hlr : l < r)
    (hp : ancestor (i - base) p = l) (hq : ancestor (j - base) q = r) :
    (i ≤ j → p < ancestor (j - i) q) ∧
    (j ≤ i → ancestor (i - j) p < q) := by
  constructor
  · intro hij
    apply lt_of_ancestor_lt (i - base)
    rw [hp, ancestor_add]
    have he : (i - base) + (j - i) = j - base := by omega
    rw [he, hq]
    exact hlr
  · intro hji
    apply lt_of_ancestor_lt (j - base)
    rw [ancestor_add, hq]
    have he : (j - base) + (i - j) = i - base := by omega
    rw [he, hp]
    exact hlr

def TraversalOrdered (column : Bool) (x y : Position) : Prop :=
  match x, y with
  | .variable i s p _, .variable j t q _ =>
    (i = j → p ≤ q ∧ (s ≠ column ∧ t = column → p < q)) ∧
    (i < j → p ≤ ancestor (j - i) q ∧ (s ≠ column → p < ancestor (j - i) q)) ∧
    (j < i → ancestor (i - j) p ≤ q ∧ (t = column → ancestor (i - j) p < q))
  | _, _ => True

private theorem block_traversal_ordered (column : Bool) (depth node size : Nat) (s : Bool) :
    (block depth s node size).Pairwise (TraversalOrdered column) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [block, List.getElem_map, List.getElem_range, TraversalOrdered]
  constructor
  · intro he; exact ⟨Nat.le_refl node, by intro hbad; exact False.elim (hbad.1 hbad.2)⟩
  · constructor <;> intro hbad <;> omega

private theorem opening_traversal_ordered (column : Bool) (rem depth node child size : Nat)
    (x y : Position) (hx : x ∈ block depth column node size)
    (hy : y ∈ tree column rem (depth + 1) child) (hchild : child / 2 = node) :
    TraversalOrdered column x y := by
  simp only [block, List.mem_map] at hx
  rcases hx with ⟨a, _, rfl⟩
  have hv := tree_variable column rem (depth + 1) child y hy
  cases y with
  | anchor => contradiction
  | dummy => contradiction
  | «variable» j t q b =>
    have ht := tree_location column rem (depth + 1) child j t q b hy
    have hd : j - depth = (j - (depth + 1)) + 1 := by omega
    have hn : ancestor (j - depth) q = node := by rw [hd, ancestor, ht.2, hchild]
    simp only [TraversalOrdered]
    constructor
    · intro he; omega
    · constructor
      · intro he; rw [hn]; exact ⟨Nat.le_refl node, by intro hn; contradiction⟩
      · intro he; omega

private theorem closing_traversal_ordered (column : Bool) (rem depth node child size : Nat)
    (x y : Position) (hx : x ∈ tree column rem (depth + 1) child)
    (hy : y ∈ block depth (!column) node size) (hchild : child / 2 = node) :
    TraversalOrdered column x y := by
  simp only [block, List.mem_map] at hy
  rcases hy with ⟨b, _, rfl⟩
  have hv := tree_variable column rem (depth + 1) child x hx
  cases x with
  | anchor => contradiction
  | dummy => contradiction
  | «variable» i s p a =>
    have ht := tree_location column rem (depth + 1) child i s p a hx
    have hd : i - depth = (i - (depth + 1)) + 1 := by omega
    have hn : ancestor (i - depth) p = node := by rw [hd, ancestor, ht.2, hchild]
    simp only [TraversalOrdered]
    constructor
    · intro he; omega
    · constructor
      · intro he; omega
      · intro he
        rw [hn]
        refine ⟨Nat.le_refl node, ?_⟩
        intro hbad
        cases column <;> simp at hbad

private theorem siblings_traversal_ordered (column : Bool) (rem depth node : Nat)
    (x y : Position)
    (hx : x ∈ tree column rem (depth + 1) (2 * node))
    (hy : y ∈ tree column rem (depth + 1) (2 * node + 1)) : TraversalOrdered column x y := by
  have hvx := tree_variable column rem (depth + 1) (2 * node) x hx
  have hvy := tree_variable column rem (depth + 1) (2 * node + 1) y hy
  cases x with
  | anchor => contradiction
  | dummy => contradiction
  | «variable» i s p a =>
    cases y with
    | anchor => contradiction
    | dummy => contradiction
    | «variable» j t q b =>
      have h0 := tree_location column rem (depth + 1) (2 * node) i s p a hx
      have h1 := tree_location column rem (depth + 1) (2 * node + 1) j t q b hy
      have hs := separated_ancestors (depth + 1) i j p q (2 * node) (2 * node + 1)
        h0.1 h1.1 (by omega) h0.2 h1.2
      simp only [TraversalOrdered]
      constructor
      · intro he
        have hl := hs.1 (by omega)
        have hpq : p < q := by simpa [he, ancestor] using hl
        exact ⟨Nat.le_of_lt hpq, fun _ => hpq⟩
      · constructor
        · intro hij; have hl := hs.1 (by omega); exact ⟨Nat.le_of_lt hl, fun _ => hl⟩
        · intro hji; have hl := hs.2 (by omega); exact ⟨Nat.le_of_lt hl, fun _ => hl⟩

theorem tree_traversal_ordered (column : Bool) (rem depth node : Nat) :
    (tree column rem depth node).Pairwise (TraversalOrdered column) := by
  induction rem generalizing depth node with
  | zero => simp [tree]
  | succ rem ih =>
    have hab : (block depth column node (2 ^ (rem + 1)) ++
        tree column rem (depth + 1) (2 * node)).Pairwise (TraversalOrdered column) := by
      apply List.pairwise_append.mpr
      refine ⟨block_traversal_ordered .., ih .., ?_⟩
      intro x hx y hy
      exact opening_traversal_ordered column rem depth node _ _ x y hx hy (by omega)
    have habc : ((block depth column node (2 ^ (rem + 1)) ++
        tree column rem (depth + 1) (2 * node)) ++
        tree column rem (depth + 1) (2 * node + 1)).Pairwise (TraversalOrdered column) := by
      apply List.pairwise_append.mpr
      refine ⟨hab, ih .., ?_⟩
      intro x hx y hy
      rcases List.mem_append.mp hx with hx | hx
      · exact opening_traversal_ordered column rem depth node _ _ x y hx hy (by omega)
      · exact siblings_traversal_ordered column rem depth node x y hx hy
    unfold tree
    apply List.pairwise_append.mpr
    refine ⟨habc, block_traversal_ordered .., ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · simp only [block, List.mem_map] at hx hy
        rcases hx with ⟨a, _, rfl⟩
        rcases hy with ⟨b, _, rfl⟩
        simp only [TraversalOrdered]
        constructor
        · intro he
          refine ⟨Nat.le_refl node, ?_⟩
          intro hbad
          exact False.elim (hbad.1 rfl)
        · constructor <;> intro hbad <;> omega
      · exact closing_traversal_ordered column rem depth node _ _ x y hx hy (by omega)
    · exact closing_traversal_ordered column rem depth node _ _ x y hx hy (by omega)

theorem axis_traversal_ordered (column : Bool) (h : Nat) :
    (axis column h).Pairwise (TraversalOrdered column) := by
  have ha : (anchors h).Pairwise (TraversalOrdered column) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [anchors, List.getElem_map, List.getElem_range, anchorLabel, TraversalOrdered]
  have hd : (dummies h).Pairwise (TraversalOrdered column) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [dummies, List.getElem_map, List.getElem_range, TraversalOrdered]
  have hn : (nonanchors column h).Pairwise (TraversalOrdered column) := by
    cases column <;> unfold nonanchors <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · apply List.pairwise_append.mpr
      refine ⟨tree_traversal_ordered .., hd, ?_⟩
      intro x hx y hy
      simp only [dummies, List.mem_map] at hy
      rcases hy with ⟨a, _, rfl⟩
      cases x <;> trivial
    · apply List.pairwise_append.mpr
      refine ⟨hd, tree_traversal_ordered .., ?_⟩
      intro x hx y hy
      simp only [dummies, List.mem_map] at hx
      rcases hx with ⟨a, _, rfl⟩
      cases y <;> trivial
  apply List.pairwise_append.mpr
  refine ⟨ha, hn, ?_⟩
  intro x hx y hy
  simp only [anchors, List.mem_map] at hx
  rcases hx with ⟨index, _, rfl⟩
  unfold anchorLabel
  cases y <;> trivial

theorem indexed_traversal_ordered (column : Bool) (h : Nat) (x y : Fin (size h))
    (hxy : x.val < y.val) : TraversalOrdered column (labelAt column h x) (labelAt column h y) := by
  have hxlen : x.val < (axis column h).length := by rw [axis_length]; exact x.isLt
  have hylen : y.val < (axis column h).length := by rw [axis_length]; exact y.isLt
  exact (axis_traversal_ordered column h).rel_getElem_of_lt hxlen hylen hxy

theorem same_class_node_order (column : Bool) (h i p q a b : Nat) (s : Bool)
    (x y : Fin (size h)) (hxy : x.val < y.val)
    (hx : labelAt column h x = .variable i s p a)
    (hy : labelAt column h y = .variable i s q b) : p ≤ q := by
  have ht := indexed_traversal_ordered column h x y hxy
  rw [hx, hy] at ht
  exact (ht.1 rfl).1

/-- Child sign is arbitrary here, so these bounds include literal shared leaves. -/
theorem child_before_parent_bound (column : Bool) (h i p q a b : Nat) (s t : Bool)
    (x y : Fin (size h)) (hxy : x.val < y.val)
    (hx : labelAt column h x = .variable (i + 1) s p a)
    (hy : labelAt column h y = .variable i t q b) :
    p / 2 ≤ q ∧ (t = column → p / 2 < q) := by
  have ht := indexed_traversal_ordered column h x y hxy
  rw [hx, hy] at ht
  have hb := ht.2.2 (Nat.lt_succ_self i)
  simpa [ancestor] using hb

theorem parent_before_child_bound (column : Bool) (h i p q a b : Nat) (s t : Bool)
    (x y : Fin (size h)) (hxy : x.val < y.val)
    (hx : labelAt column h x = .variable i s p a)
    (hy : labelAt column h y = .variable (i + 1) t q b) :
    p ≤ q / 2 ∧ (s ≠ column → p < q / 2) := by
  have ht := indexed_traversal_ordered column h x y hxy
  rw [hx, hy] at ht
  have hb := ht.2.1 (Nat.lt_succ_self i)
  simpa [ancestor] using hb

theorem same_level_phase_order (column : Bool) (h i p q a b : Nat) (s t : Bool)
    (x y : Fin (size h)) (hxy : x.val < y.val)
    (hx : labelAt column h x = .variable i s p a)
    (hy : labelAt column h y = .variable i t q b) :
    p ≤ q ∧ (s ≠ column ∧ t = column → p < q) := by
  have ht := indexed_traversal_ordered column h x y hxy
  rw [hx, hy] at ht
  exact ht.1 rfl

end OrderedMatrixRemoval4.Host
