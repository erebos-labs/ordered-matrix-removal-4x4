import OrderedMatrixRemoval4.Host

/-!
The exhaustive minus-column incidence list and exclusion of the nonterminal
sibling exception. These are unconditional host lemmas at arbitrary depth.
The reduction of every H4 embedding to the canonical/unpinned shapes remains
a separate obligation; it is not assumed here as a certificate.
-/
namespace OrderedMatrixRemoval4.Host

theorem minus_nonterminal_incidence_iff (h i l k g q a z : Nat) (hi : i < h) :
    entry h (.anchor l k g a) (.variable i false q z) = true ↔
      (((k = 4 ∨ k = 5) ∧ g = 0 ∧ l = i ∧ q % 2 = k - 4) ∨
       (l = i + 1 ∧ g = 1 ∧ (k = 1 ∨ k = 4 ∨ k = 5))) := by
  simp [entry, columnRole, signed, Nat.ne_of_lt hi]
  omega

/-- Any earlier anchor that meets this minus class can select only even nodes. -/
theorem earlier_minus_incidence_even (h i l k g q a z : Nat)
    (hi : i < h) (hpos : 1 ≤ i) (hl : 1 ≤ l)
    (horder : anchorRank (l - 1) k g < anchorRank (i - 1) 4 1)
    (hentry : entry h (.anchor l k g a) (.variable i false q z) = true) :
    q % 2 = 0 := by
  rw [minus_nonterminal_incidence_iff h i l k g q a z hi] at hentry
  unfold anchorRank at horder
  omega

/-- Full incidence/order contradiction for the exceptional sibling branch. -/
theorem nonterminal_sibling_exception_impossible (h i l k g p q b a z : Nat)
    (hi : i < h) (hpos : 1 ≤ i) (hl : 1 ≤ l)
    (horder : anchorRank (l - 1) k g < anchorRank (i - 1) 4 1)
    (hentry : entry h (.anchor l k g a) (.variable i false q z) = true)
    (hpq : p < q) (hqb : q / 2 ≤ b) (hbp : b ≤ p / 2) : False := by
  have heven := earlier_minus_incidence_even h i l k g q a z hi hpos hl horder hentry
  have hs := OrderedMatrixRemoval4.nonterminal_siblings p q b hpq hqb hbp
  omega

/-- Role-predicate version avoids re-elaborating Boolean decision instances. -/
theorem earlier_minus_role_even (h i l k g q z : Nat)
    (hi : i < h) (hpos : 1 ≤ i) (hl : 1 ≤ l)
    (horder : anchorRank (l - 1) k g < anchorRank (i - 1) 4 1)
    (hrole : columnRole h l k g (.variable i false q z)) : q % 2 = 0 := by
  simp [columnRole, signed, Nat.ne_of_lt hi] at hrole
  unfold anchorRank at horder
  omega

end OrderedMatrixRemoval4.Host
