import OrderedMatrixRemoval4.Sampling

namespace OrderedMatrixRemoval4.Host

private theorem add_mod_cancel_bounded (m u v w : Nat) (hu : u < m) (hv : v < m) (hw : w < m)
    (he : (u + v) % m = (u + w) % m) : v = w := by
  have hmv := Nat.mod_add_div (u+v) m
  have hmw := Nat.mod_add_div (u+w) m
  have hdv : (u+v)/m ≤ 1 := by
    apply Nat.le_of_lt_succ
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr (by omega)
  have hdw : (u+w)/m ≤ 1 := by
    apply Nat.le_of_lt_succ
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < m)).mpr (by omega)
  have hcasesv : (u+v)/m = 0 ∨ (u+v)/m = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hdv
  have hcasesw : (u+w)/m = 0 ∨ (u+w)/m = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hdw
  rcases hcasesv with hdv | hdv <;> rcases hcasesw with hdw | hdw
  all_goals rw [hdv] at hmv
  all_goals rw [hdw] at hmw
  all_goals simp only [Nat.mul_zero,Nat.mul_one] at hmv hmw
  all_goals omega

/-- Dyadic class coordinates give a bijective column coding for each fixed row
seed, and conversely by symmetry. This is arithmetic groundwork for a finite
family of actual path selections, not yet an instantiated host sampling bound. -/
theorem shift_class_injective (m d u v w : Nat) (hd : d ∣ m)
    (hu : u < m) (hv : v < m) (hw : w < m)
    (hnode : ((u+v)%m)/d = ((u+w)%m)/d) (hclone : v%d = w%d) : v = w := by
  have hrem : ((u+v)%m)%d = ((u+w)%m)%d := by
    rw [Nat.mod_mod_of_dvd _ hd,Nat.mod_mod_of_dvd _ hd,
      Nat.add_mod u v d,Nat.add_mod u w d,hclone]
  have hvd := Nat.mod_add_div ((u+v)%m) d
  have hwd := Nat.mod_add_div ((u+w)%m) d
  have he : (u+v)%m = (u+w)%m := by rw [hrem,hnode] at hvd; omega
  exact add_mod_cancel_bounded m u v w hu hv hw he

theorem dyadic_split (h i : Nat) (hi : i ≤ h) : 2 ^ h = 2 ^ i * 2 ^ (h-i) := by
  have he : h = i + (h-i) := by omega
  calc
    2 ^ h = 2 ^ (i+(h-i)) := congrArg (fun e => 2 ^ e) he
    _ = 2 ^ i * 2 ^ (h-i) := Nat.pow_add ..

theorem dyadic_block_divides (h i : Nat) (hi : i ≤ h) : 2 ^ (h-i) ∣ 2 ^ h := by
  rw [dyadic_split h i hi]
  exact ⟨2 ^ i,Nat.mul_comm _ _⟩

end OrderedMatrixRemoval4.Host
