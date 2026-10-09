import OrderedMatrixRemoval4.Semantics

/-! Generic H4 frame extension for arbitrary edited Boolean matrices.
The guard covers only cells with a pattern anchor endpoint. It puts no
constraint on the four body bits and asserts no host localization. -/
namespace OrderedMatrixRemoval4

def FrameGuard {n : Nat} (B : BinaryMatrix n) (rows cols : Fin 4 → Fin n) : Prop :=
  Increasing rows ∧ Increasing cols ∧
  (∀ i j, i.val < 2 ∨ j.val < 2 → B (rows i) (cols j) = H4 i j)

def BodyBits {n : Nat} (B : BinaryMatrix n) (rows cols : Fin 4 → Fin n)
    (a b c d : Bool) : Prop :=
  B (rows 2) (cols 2) = a ∧ B (rows 2) (cols 3) = b ∧
  B (rows 3) (cols 2) = c ∧ B (rows 3) (cols 3) = d

theorem frame_extension {n : Nat} (B : BinaryMatrix n) (rows cols : Fin 4 → Fin n)
    (hg : FrameGuard B rows cols) (hb : BodyBits B rows cols true false true true) :
    OrderedCopy H4 B rows cols := by
  refine ⟨hg.1, hg.2.1, ?_⟩
  intro i j
  by_cases ha : i.val < 2 ∨ j.val < 2
  · exact hg.2.2 i j ha
  · have hi : i = 2 ∨ i = 3 := by omega
    have hj : j = 2 ∨ j = 3 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2

theorem body_forbidden_of_free {n : Nat} (B : BinaryMatrix n)
    (hf : HFree H4 B) (rows cols : Fin 4 → Fin n) (hg : FrameGuard B rows cols) :
    ¬ BodyBits B rows cols true false true true := by
  intro hb
  exact hf rows cols (frame_extension B rows cols hg hb)

/-- All-depth propagation in any edited matrix, conditional on intact ordered
frames. Sampling an intact frame and constructing its actual host coordinates
are separate obligations, so this is not the edit-distance theorem. -/
theorem guarded_path_contradiction {n : Nat} (B : BinaryMatrix n) (h : Nat)
    (hf : HFree H4 B) (dp dm up um : Nat → Bool)
    (vrp vcp vrm vcm wrp wcp wrm wcm : Nat → Fin 4 → Fin n)
    (hp : dp 0 = true) (hm : dm 0 = false) (hleaf : dp h = dm h)
    (hframes : ∀ i, i < h →
      FrameGuard B (vrp i) (vcp i) ∧ FrameGuard B (vrm i) (vcm i) ∧
      FrameGuard B (wrp i) (wcp i) ∧ FrameGuard B (wrm i) (wcm i))
    (hbodies : ∀ i, i < h →
      BodyBits B (vrp i) (vcp i) true (up i) true (dp i) ∧
      BodyBits B (vrm i) (vcm i) true (dm i) true (um i) ∧
      BodyBits B (wrp i) (wcp i) (up i) (dp (i + 1)) true true ∧
      BodyBits B (wrm i) (wcm i) (dm (i + 1)) (um i) true true) : False := by
  have hind : ∀ j, j ≤ h → dp j = true ∧ dm j = false := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hp, hm⟩
    | succ j ih =>
      intro hj
      have hlt : j < h := by omega
      have hd := ih (by omega)
      have hg := hframes j hlt
      have hb := hbodies j hlt
      have hu : up j = true := by
        cases hu' : up j
        · have hbad := hb.1
          rw [hu', hd.1] at hbad
          exact False.elim (body_forbidden_of_free B hf _ _ hg.1 hbad)
        · rfl
      have hv : um j = false := by
        cases hv' : um j
        · rfl
        · have hbad := hb.2.1
          rw [hv', hd.2] at hbad
          exact False.elim (body_forbidden_of_free B hf _ _ hg.2.1 hbad)
      constructor
      · cases hn : dp (j + 1)
        · have hbad := hb.2.2.1
          rw [hu, hn] at hbad
          exact False.elim (body_forbidden_of_free B hf _ _ hg.2.2.1 hbad)
        · rfl
      · cases hn : dm (j + 1)
        · rfl
        · have hbad := hb.2.2.2
          rw [hv, hn] at hbad
          exact False.elim (body_forbidden_of_free B hf _ _ hg.2.2.2 hbad)
  have hend := hind h (Nat.le_refl h)
  rw [hend.1, hend.2] at hleaf
  contradiction

end OrderedMatrixRemoval4
