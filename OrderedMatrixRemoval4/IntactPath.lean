import OrderedMatrixRemoval4.PathFrames

namespace OrderedMatrixRemoval4.Host

def Dummy : Position → Prop
  | .dummy _ => True
  | _ => False

def Root : Position → Prop
  | .variable i _ _ _ => i = 0
  | _ => False

/-- Exactly the protected cells used by the arbitrary-edit argument. -/
def Protected (h : Nat) (r c : Fin (size h)) : Prop :=
  Anchor (labelAt false h r) ∨ Anchor (labelAt true h c) ∨
  Dummy (labelAt false h r) ∨ Dummy (labelAt true h c) ∨
  (Root (labelAt false h r) ∧ Root (labelAt true h c))

def PathSelection.Selected {h : Nat} (s : PathSelection h) (column : Bool)
    (x : Fin (size h)) : Prop :=
  (∃ i, i ≤ h ∧ ∃ sig, x = (if column then s.col else s.row) i sig) ∨
  (∃ l, 1 ≤ l ∧ l ≤ h ∧ ∃ k, k < 6 ∧ ∃ g, g < 2 ∧
    x = (if column then s.ca else s.ra) l k g) ∨
  x = (if column then s.cd else s.rd)

def IntactPath (h : Nat) (B : BinaryMatrix (size h)) (s : PathSelection h) : Prop :=
  ∀ r c, s.Selected false r → s.Selected true c → Protected h r c → B r c = matrix h r c

private theorem selected_row {h : Nat} (s : PathSelection h) (i : Nat) (hi : i ≤ h) (sig : Bool) :
    s.Selected false (s.row i sig) := Or.inl ⟨i,hi,sig,rfl⟩
private theorem selected_col {h : Nat} (s : PathSelection h) (i : Nat) (hi : i ≤ h) (sig : Bool) :
    s.Selected true (s.col i sig) := Or.inl ⟨i,hi,sig,rfl⟩
private theorem selected_ra {h : Nat} (s : PathSelection h) (l k g : Nat)
    (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6) (hg : g < 2) :
    s.Selected false (s.ra l k g) := Or.inr (Or.inl ⟨l,hl,hlh,k,hk,g,hg,rfl⟩)
private theorem selected_ca {h : Nat} (s : PathSelection h) (l k g : Nat)
    (hl : 1 ≤ l) (hlh : l ≤ h) (hk : k < 6) (hg : g < 2) :
    s.Selected true (s.ca l k g) := Or.inr (Or.inl ⟨l,hl,hlh,k,hk,g,hg,rfl⟩)
private theorem selected_rd {h : Nat} (s : PathSelection h) : s.Selected false s.rd :=
  Or.inr (Or.inr rfl)
private theorem selected_cd {h : Nat} (s : PathSelection h) : s.Selected true s.cd :=
  Or.inr (Or.inr rfl)

private theorem four_selected {h : Nat} (s : PathSelection h) (column : Bool)
    (a b c d : Fin (size h))
    (ha : s.Selected column a) (hb : s.Selected column b)
    (hc : s.Selected column c) (hd : s.Selected column d) :
    ∀ i, s.Selected column (four a b c d i) := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl <;> simpa [four]

/-- Transfers a proved actual mode guard using agreement only on selected
protected cells. It imposes no conditions on the nonroot variable body entries. -/
theorem intact_mode_guard (h i k : Nat) (B : BinaryMatrix (size h)) (s : PathSelection h)
    (hi : i < h) (hk : k < 6) (hint : IntactPath h B s)
    (r2 r3 c2 c3 : Fin (size h))
    (sr2 : s.Selected false r2) (sr3 : s.Selected false r3)
    (sc2 : s.Selected true c2) (sc3 : s.Selected true c3)
    (hg : FrameGuard (matrix h)
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) r2 r3)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) c2 c3)) :
    FrameGuard B
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) r2 r3)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) c2 c3) := by
  have hr := four_selected s false _ _ _ _
    (selected_ra s (i+1) k 0 (by omega) (by omega) hk (by decide))
    (selected_ra s (i+1) k 1 (by omega) (by omega) hk (by decide)) sr2 sr3
  have hc := four_selected s true _ _ _ _
    (selected_ca s (i+1) k 0 (by omega) (by omega) hk (by decide))
    (selected_ca s (i+1) k 1 (by omega) (by omega) hk (by decide)) sc2 sc3
  refine ⟨hg.1,hg.2.1,?_⟩
  intro a b hab
  have hp : Protected h
      (four (s.ra (i+1) k 0) (s.ra (i+1) k 1) r2 r3 a)
      (four (s.ca (i+1) k 0) (s.ca (i+1) k 1) c2 c3 b) := by
    rcases hab with ha | hb
    · have he : a = 0 ∨ a = 1 := by omega
      rcases he with rfl | rfl
      all_goals apply Or.inl
      · simp [four,Anchor,s.raLabel (i+1) (by omega) (by omega) k hk 0 (by decide)]
      · simp [four,Anchor,s.raLabel (i+1) (by omega) (by omega) k hk 1 (by decide)]
    · have he : b = 0 ∨ b = 1 := by omega
      rcases he with rfl | rfl
      all_goals apply Or.inr ∘ Or.inl
      · simp [four,Anchor,s.caLabel (i+1) (by omega) (by omega) k hk 0 (by decide)]
      · simp [four,Anchor,s.caLabel (i+1) (by omega) (by omega) k hk 1 (by decide)]
  exact (hint _ _ (hr a) (hc b) hp).trans (hg.2.2 a b hab)

theorem intact_dummy_column (h i : Nat) (B : BinaryMatrix (size h)) (s : PathSelection h)
    (hi : i ≤ h) (sig : Bool) (hint : IntactPath h B s) : B (s.row i sig) s.cd = true := by
  have hp : Protected h (s.row i sig) s.cd := Or.inr (Or.inr (Or.inr (Or.inl (by simp [s.cdLabel,Dummy]))))
  rw [hint _ _ (selected_row s i hi sig) (selected_cd s) hp]
  simp [matrix,s.rowLabel i hi sig,s.cdLabel,entry]

theorem intact_dummy_row (h i : Nat) (B : BinaryMatrix (size h)) (s : PathSelection h)
    (hi : i ≤ h) (sig : Bool) (hint : IntactPath h B s) : B s.rd (s.col i sig) = true := by
  have hp : Protected h s.rd (s.col i sig) := Or.inr (Or.inr (Or.inl (by simp [s.rdLabel,Dummy])))
  rw [hint _ _ (selected_rd s) (selected_col s i hi sig) hp]
  simp [matrix,s.rdLabel,s.colLabel i hi sig,entry]

theorem intact_roots (h : Nat) (hh : 1 ≤ h) (B : BinaryMatrix (size h))
    (s : PathSelection h) (hint : IntactPath h B s) :
    B (s.row 0 true) (s.col 0 true) = true ∧ B (s.row 0 false) (s.col 0 false) = false := by
  have hp : ∀ sig, Protected h (s.row 0 sig) (s.col 0 sig) := by
    intro sig
    apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    simp [s.rowLabel 0 (by omega) sig,s.colLabel 0 (by omega) sig,Root]
  have hb := fun sig => hint _ _ (selected_row s 0 (by omega) sig) (selected_col s 0 (by omega) sig) (hp sig)
  have hz : 0 ≠ h := by omega
  constructor
  · rw [hb true]
    simp [matrix,s.rowLabel 0 (by omega) true,s.colLabel 0 (by omega) true,
      viewSign,hz,entry,signed,s.root]
  · rw [hb false]
    simp [matrix,s.rowLabel 0 (by omega) false,s.colLabel 0 (by omega) false,
      viewSign,hz,entry,signed,s.root]

theorem path_shared_leaf (h : Nat) (s : PathSelection h) :
    s.row h true = s.row h false ∧ s.col h true = s.col h false := by
  have hr := fun sig => s.rowLabel h (Nat.le_refl h) sig
  have hc := fun sig => s.colLabel h (Nat.le_refl h) sig
  have hrc : ∀ sig, s.rowClone h sig = 0 := by
    intro sig
    apply leaf_tag_clone_zero false h true (s.node h) (s.rowClone h sig)
    have hm := List.getElem_mem (labelAt._proof_1 false h (s.row h sig))
    change labelAt false h (s.row h sig) ∈ axis false h at hm
    simpa [hr sig,viewSign] using hm
  have hcc : ∀ sig, s.colClone h sig = 0 := by
    intro sig
    apply leaf_tag_clone_zero true h true (s.node h) (s.colClone h sig)
    have hm := List.getElem_mem (labelAt._proof_1 true h (s.col h sig))
    change labelAt true h (s.col h sig) ∈ axis true h at hm
    simpa [hc sig,viewSign] using hm
  constructor
  · apply labelAt_injective false h
    simp [hr,hrc,viewSign]
  · apply labelAt_injective true h
    simp [hc,hcc,viewSign]

/-- An intact selection of actual protected path cells forces an ordinary
ordered H4 copy in any edited matrix. The four frames are constructed here;
no frame guards, body bits, localization, or freeness conclusion are assumed. -/
theorem intact_path_contains_copy (h : Nat) (hh : 1 ≤ h) (B : BinaryMatrix (size h))
    (s : PathSelection h) (hint : IntactPath h B s) :
    ∃ rows cols, OrderedCopy H4 B rows cols := by
  classical
  apply Classical.byContradiction
  intro hn
  have hf : HFree H4 B := fun rows cols hc => hn ⟨rows,cols,hc⟩
  let vpr := fun i => four (s.ra (i+1) 0 0) (s.ra (i+1) 0 1) (s.row (i+1) true) (s.row i true)
  let vpc := fun i => four (s.ca (i+1) 0 0) (s.ca (i+1) 0 1) s.cd (s.col i true)
  let vmr := fun i => four (s.ra (i+1) 1 0) (s.ra (i+1) 1 1) (s.row i false) (s.row (i+1) false)
  let vmc := fun i => four (s.ca (i+1) 1 0) (s.ca (i+1) 1 1) s.cd (s.col i false)
  let wpr := fun i => let k := 2 + s.node (i+1) % 2
    four (s.ra (i+1) k 0) (s.ra (i+1) k 1) (s.row (i+1) true) s.rd
  let wpc := fun i => let k := 2 + s.node (i+1) % 2
    four (s.ca (i+1) k 0) (s.ca (i+1) k 1) (s.col i true) (s.col (i+1) true)
  let wmr := fun i => let k := 4 + s.node (i+1) % 2
    four (s.ra (i+1) k 0) (s.ra (i+1) k 1) (s.row (i+1) false) s.rd
  let wmc := fun i => let k := 4 + s.node (i+1) % 2
    four (s.ca (i+1) k 0) (s.ca (i+1) k 1) (s.col (i+1) false) (s.col i false)
  have hroots := intact_roots h hh B s hint
  have hleaf : B (s.row h true) (s.col h true) = B (s.row h false) (s.col h false) := by
    rw [(path_shared_leaf h s).1,(path_shared_leaf h s).2]
  apply guarded_path_contradiction B h hf
    (fun i => B (s.row i true) (s.col i true))
    (fun i => B (s.row i false) (s.col i false))
    (fun i => B (s.row (i+1) true) (s.col i true))
    (fun i => B (s.row (i+1) false) (s.col i false))
    vpr vpc vmr vmc wpr wpc wmr wmc hroots.1 hroots.2 hleaf
  · intro i hi
    refine ⟨?_,?_,?_,?_⟩
    · exact intact_mode_guard h i 0 B s hi (by decide) hint _ _ _ _
        (selected_row s _ (by omega) true) (selected_row s _ (by omega) true)
        (selected_cd s) (selected_col s _ (by omega) true) (path_vertical_plus_guard h i s hi)
    · exact intact_mode_guard h i 1 B s hi (by decide) hint _ _ _ _
        (selected_row s _ (by omega) false) (selected_row s _ (by omega) false)
        (selected_cd s) (selected_col s _ (by omega) false) (path_vertical_minus_guard h i s hi)
    · exact intact_mode_guard h i (2+s.node (i+1)%2) B s hi (by omega) hint _ _ _ _
        (selected_row s _ (by omega) true) (selected_rd s)
        (selected_col s _ (by omega) true) (selected_col s _ (by omega) true)
        (path_horizontal_plus_guard h i s hi)
    · exact intact_mode_guard h i (4+s.node (i+1)%2) B s hi (by omega) hint _ _ _ _
        (selected_row s _ (by omega) false) (selected_rd s)
        (selected_col s _ (by omega) false) (selected_col s _ (by omega) false)
        (path_horizontal_minus_guard h i s hi)
  · intro i hi
    have hdc0 := intact_dummy_column h i B s (by omega) true hint
    have hdc1 := intact_dummy_column h (i+1) B s (by omega) true hint
    have hdm0 := intact_dummy_column h i B s (by omega) false hint
    have hdm1 := intact_dummy_column h (i+1) B s (by omega) false hint
    have hdr0 := intact_dummy_row h i B s (by omega) true hint
    have hdr1 := intact_dummy_row h (i+1) B s (by omega) true hint
    have hdrm0 := intact_dummy_row h i B s (by omega) false hint
    have hdrm1 := intact_dummy_row h (i+1) B s (by omega) false hint
    simp [BodyBits,vpr,vpc,vmr,vmc,wpr,wpc,wmr,wmc,four,
      hdc0,hdc1,hdm0,hdm1,hdr0,hdr1,hdrm0,hdrm1]

end OrderedMatrixRemoval4.Host
