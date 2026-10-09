import OrderedMatrixRemoval4.Semantics

namespace OrderedMatrixRemoval4

def assignments (n : Nat) : (k : Nat) → List (Fin k → Fin n)
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange n).flatMap fun a =>
      (assignments n k).map (fun f => Fin.cases a f)

theorem assignments_length (n k : Nat) : (assignments n k).length = n ^ k := by
  induction k with
  | zero => simp [assignments]
  | succ k ih =>
    simp [assignments, List.length_flatMap, ih, List.map_const', List.sum_replicate_nat,
      Nat.pow_succ, Nat.mul_comm]

theorem mem_assignments (n k : Nat) (f : Fin k → Fin n) : f ∈ assignments n k := by
  induction k with
  | zero =>
    have hf : f = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [assignments,hf]
  | succ k ih =>
    have he : (fun i => Fin.cases (f 0) (fun j => f j.succ) i) = f := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    exact List.mem_flatMap.mpr ⟨f 0,List.mem_finRange _,
      List.mem_map.mpr ⟨_,ih _,he⟩⟩

theorem assignments_nodup (n k : Nat) : (assignments n k).Nodup := by
  induction k with
  | zero => simp [assignments]
  | succ k ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro a ha
      apply List.Pairwise.map _ _ ih
      intro f g hfg he
      apply hfg
      funext i
      exact congrArg (fun u => u i.succ) he
    · apply (List.nodup_finRange n).imp
      intro a b hab x hx y hy he
      rcases List.mem_map.mp hx with ⟨f,hf,rfl⟩
      rcases List.mem_map.mp hy with ⟨g,hg,rfl⟩
      exact hab (congrArg (fun f => f 0) he)

def cartesian {α β : Type} (l : List α) (m : List β) : List (α × β) :=
  l.flatMap fun a => m.map fun b => (a,b)

theorem cartesian_length {α β : Type} (l : List α) (m : List β) :
    (cartesian l m).length = l.length * m.length := by
  simp [cartesian,List.length_flatMap,List.map_const',List.sum_replicate_nat]

theorem mem_cartesian {α β : Type} (l : List α) (m : List β) (a : α) (b : β) :
    (a,b) ∈ cartesian l m ↔ a ∈ l ∧ b ∈ m := by
  simp [cartesian]

theorem cartesian_nodup {α β : Type} (l : List α) (m : List β)
    (hl : l.Nodup) (hm : m.Nodup) : (cartesian l m).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    exact List.Pairwise.map _ (fun b c hbc he => hbc (congrArg Prod.snd he)) hm
  · apply hl.imp
    intro a b hab x hx y hy he
    rcases List.mem_map.mp hx with ⟨c,hc,rfl⟩
    rcases List.mem_map.mp hy with ⟨d,hd,rfl⟩
    exact hab (congrArg Prod.fst he)

end OrderedMatrixRemoval4
