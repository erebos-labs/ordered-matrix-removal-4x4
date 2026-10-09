import OrderedMatrixRemoval4

open OrderedMatrixRemoval4
open OrderedMatrixRemoval4.Host

example (h : Nat) (hh : 1 ≤ h) (rows cols : Fin 4 → Fin (size h))
    (hc : OrderedCopy H4 (matrix h) rows cols) : sparseZero h (rows 2) (cols 3) :=
  all_copy_localization h hh rows cols hc

example (h : Nat) (hh : 1 ≤ h) : (sparseCells h hh).length = 2 * 2 ^ h :=
  sparseCells_length h hh

example (h : Nat) (hh : 1 ≤ h) : copyCount h ≤ 2 * 2 ^ h * (size h) ^ 6 :=
  copy_count_bound h hh

example (h : Nat) (hh : 1 ≤ h) (B : BinaryMatrix (size h)) (s : PathSelection h)
    (hint : IntactPath h B s) : ∃ rows cols, OrderedCopy H4 B rows cols :=
  intact_path_contains_copy h hh B s hint

#print Host.all_copy_localization
#print axioms Host.all_copy_localization
#print axioms Host.copy_count_bound
#print axioms Host.intact_path_contains_copy

example (h : Nat) (hh : 1 ≤ h) (B : BinaryMatrix (size h))
    (hf : HFree H4 B) : (2^h)^2 ≤ Host.editCount h B :=
  Host.arbitrary_edit_distance h hh B hf

example (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t)
    (B : BinaryMatrix (size h*t)) (hf : HFree H4 B) :
    (t*2^h)^2 ≤ Blowup.editCount (Blowup.matrix (matrix h) t ht) B :=
  Blowup.arbitrary_edit_distance h t hh ht B hf

example (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ n : Nat, 1 ≤ n ∧ ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ A : BinaryMatrix n, ε ≤ Removal.distance A ∧
        (Counting.copyCount A:ℝ) < c * ε^C * (n:ℝ)^8 := by
  obtain ⟨ε,hε0,hε1,_,n,hn,_,A,hfar,hfew⟩ :=
    Removal.counterexample c C 1 hc hC (by norm_num) (fun _ => 1)
  exact ⟨n,hn,ε,hε0,hε1,A,hfar,hfew⟩

example : ¬ Removal.PolynomialRemoval := Removal.no_polynomial_removal

#print Removal.PolynomialRemoval
#print Removal.counterexample
#print Removal.no_polynomial_removal
#print axioms Host.arbitrary_edit_distance
#print axioms Blowup.arbitrary_edit_distance
#print axioms Blowup.copy_count_bound
#print axioms Removal.counterexample
#print axioms Removal.no_polynomial_removal
