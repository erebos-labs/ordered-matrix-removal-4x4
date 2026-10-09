import OrderedMatrixRemoval4.Blowup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace OrderedMatrixRemoval4
namespace Removal

 theorem zero_free (n : Nat) : HFree H4 (fun (_ _) => false : BinaryMatrix n) := by
  intro rows cols hc
  have he := hc.2.2 0 1
  change false = true at he
  cases he

 theorem repair_exists {n : Nat} (A : BinaryMatrix n) :
    ∃ k : Nat, ∃ B : BinaryMatrix n, HFree H4 B ∧ Blowup.editCount A B = k :=
  ⟨_,fun _ _ => false,zero_free n,rfl⟩

noncomputable def repairCount {n : Nat} (A : BinaryMatrix n) : Nat :=
  by
  classical
  exact Nat.find (repair_exists A)

 theorem repair_attained {n : Nat} (A : BinaryMatrix n) :
    ∃ B : BinaryMatrix n, HFree H4 B ∧ Blowup.editCount A B = repairCount A :=
by
  classical
  exact Nat.find_spec (repair_exists A)

 theorem repair_minimal {n : Nat} (A B : BinaryMatrix n) (hf : HFree H4 B) :
    repairCount A ≤ Blowup.editCount A B :=
by
  classical
  exact Nat.find_min' (repair_exists A) ⟨B,hf,rfl⟩

noncomputable def distance {n : Nat} (A : BinaryMatrix n) : ℝ :=
  (repairCount A : ℝ) / (n : ℝ)^2

noncomputable def epsilon (h : Nat) : ℝ := 1 / (14*(h:ℝ)+2)^2

 theorem epsilon_range (h : Nat) : 0 < epsilon h ∧ epsilon h < 1 := by
  have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  unfold epsilon
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < (14*(h:ℝ)+2)^2)).mpr
    nlinarith

 theorem blowup_distance (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    epsilon h ≤ distance (Blowup.matrix (Host.matrix h) t ht) := by
  obtain ⟨B,hf,hB⟩ := repair_attained (Blowup.matrix (Host.matrix h) t ht)
  have hl := Blowup.arbitrary_edit_distance h t hh ht B hf
  rw [hB] at hl
  have hr : ((t:ℝ)*2^h)^2 ≤ (repairCount (Blowup.matrix (Host.matrix h) t ht):ℝ) := by
    exact_mod_cast hl
  have hm : (0:ℝ) < 2^h := by positivity
  have ht' : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hd : (0:ℝ) < 14*(h:ℝ)+2 := by positivity
  unfold epsilon distance Host.size
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ = ((t:ℝ)*2^h)^2 * (14*(h:ℝ)+2)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hr (sq_nonneg (14*(h:ℝ)+2))

 theorem blowup_copies (h t : Nat) (hh : 1 ≤ h) (ht : 1 ≤ t) :
    (Counting.copyCount (Blowup.matrix (Host.matrix h) t ht):ℝ) ≤
      (2 / ((14*(h:ℝ)+2)^2 * 2^h)) * ((Host.size h*t:Nat):ℝ)^8 := by
  have hb := Blowup.copy_count_bound h t hh ht
  have hr : (Counting.copyCount (Blowup.matrix (Host.matrix h) t ht):ℝ) ≤
      (2*2^h)*(t:ℝ)^2 * ((Host.size h*t:Nat):ℝ)^6 := by
    convert (Nat.cast_le.mpr hb : (_:ℝ) ≤ _) using 1
    push_cast
    ring
  have hm : (0:ℝ) < 2^h := by positivity
  have hd : (0:ℝ) < 14*(h:ℝ)+2 := by positivity
  have he : (2*2^h)*(t:ℝ)^2 * ((Host.size h*t:Nat):ℝ)^6 =
      (2 / ((14*(h:ℝ)+2)^2 * 2^h)) * ((Host.size h*t:Nat):ℝ)^8 := by
    unfold Host.size
    push_cast
    field_simp
  exact he ▸ hr

 theorem exponential_choice (c C : ℝ) (hc : 0 < c) (_hC : 0 < C) (L : Nat) :
    ∃ h : Nat, L ≤ h ∧ 1 ≤ h ∧ 2 / ((14*(h:ℝ)+2)^2 * 2^h) < c * (epsilon h)^C := by
  obtain ⟨K,hK⟩ := exists_nat_ge (2*C)
  have htend : Filter.Tendsto (fun h : Nat => (2*16^K:ℝ) * ((h:ℝ)^K / 2^h))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt K (by norm_num : (1:ℝ)<2)).const_mul (2*16^K:ℝ)
  have hev : ∀ᶠ h : Nat in Filter.atTop, (2*16^K:ℝ) * ((h:ℝ)^K / 2^h) < c :=
    htend.eventually (gt_mem_nhds hc)
  obtain ⟨h,hh,he⟩ := (hev.and ((Filter.eventually_ge_atTop 1).and (Filter.eventually_ge_atTop L))).exists
  refine ⟨h,he.2,he.1,?_⟩
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast he.1
  have hd : (1:ℝ) ≤ 14*(h:ℝ)+2 := by nlinarith
  have hpow : (14*(h:ℝ)+2)^(2*C) ≤ (16:ℝ)^K*(h:ℝ)^K := by
    calc
      _ ≤ (14*(h:ℝ)+2)^K := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hd hK
      _ ≤ (16*(h:ℝ))^K := pow_le_pow_left₀ (by positivity) (by nlinarith) K
      _ = _ := by rw [mul_pow]
  have hm : (0:ℝ) < 2^h := by positivity
  have hdpos : (0:ℝ) < 14*(h:ℝ)+2 := by positivity
  have hp : 0 < (14*(h:ℝ)+2)^(2*C) := Real.rpow_pos_of_pos hdpos _
  have heps : (epsilon h)^C = ((14*(h:ℝ)+2)^(2*C))⁻¹ := by
    unfold epsilon
    rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    norm_num
  rw [heps]
  apply (lt_mul_inv_iff₀ hp).mpr
  have hbound : 2 * (14*(h:ℝ)+2)^(2*C) / 2^h < c := by
    calc
      _ ≤ (2*16^K:ℝ)*((h:ℝ)^K/2^h) := by
        apply (div_le_iff₀ hm).mpr
        field_simp
        nlinarith
      _ < c := hh
  have hd2 : 1 ≤ (14*(h:ℝ)+2)^2 := by nlinarith
  calc
    _ = (2 * (14*(h:ℝ)+2)^(2*C) / 2^h) / (14*(h:ℝ)+2)^2 := by
      field_simp
    _ ≤ 2 * (14*(h:ℝ)+2)^(2*C) / 2^h :=
      div_le_self (by positivity) hd2
    _ < c := hbound

/-- The failure persists beyond any order threshold depending on epsilon,
and with epsilon below any prescribed positive real number. -/
 theorem counterexample (c C η : ℝ) (hc : 0 < c) (hC : 0 < C) (hη : 0 < η)
    (threshold : ℝ → Nat) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ε < η ∧
      ∃ n : Nat, 1 ≤ n ∧ threshold ε ≤ n ∧
        ∃ A : BinaryMatrix n, ε ≤ distance A ∧
          (Counting.copyCount A:ℝ) < c * ε^C * (n:ℝ)^8 := by
  obtain ⟨L,hL⟩ := exists_nat_gt (1/η)
  obtain ⟨h,hLh,hh,hsmall⟩ := exponential_choice c C hc hC L
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hLh' : (L:ℝ) ≤ h := by exact_mod_cast hLh
  have hηsmall : epsilon h < η := by
    unfold epsilon
    apply (div_lt_iff₀ (by positivity : 0 < (14*(h:ℝ)+2)^2)).mpr
    have hi : 1 < η*(L:ℝ) := by simpa [mul_comm] using (div_lt_iff₀ hη).mp hL
    have hs : (L:ℝ) ≤ (14*(h:ℝ)+2)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs (le_of_lt hη)]
  let t := threshold (epsilon h) + 1
  have ht : 1 ≤ t := by omega
  have hnbase : 1 ≤ Host.size h := by
    unfold Host.size
    have hm : 0 < 2^h := Nat.two_pow_pos h
    have hd : 0 < 14*h+2 := by omega
    exact Nat.succ_le_of_lt (Nat.mul_pos hd hm)
  have htn : t ≤ Host.size h*t := by
    simpa using Nat.mul_le_mul_right t hnbase
  have hn : 1 ≤ Host.size h*t := by omega
  have hnpos : (0:ℝ) < (Host.size h*t:Nat) := by exact_mod_cast (show 0 < Host.size h*t by omega)
  refine ⟨epsilon h,(epsilon_range h).1,(epsilon_range h).2,hηsmall,
    Host.size h*t,hn,by omega,Blowup.matrix (Host.matrix h) t ht,
    blowup_distance h t hh ht,?_⟩
  exact lt_of_le_of_lt (blowup_copies h t hh ht)
    (mul_lt_mul_of_pos_right hsmall (pow_pos hnpos 8))

/-- Polynomial ordered removal in the original real-quantified convention. -/
noncomputable def PolynomialRemoval : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ n : Nat, 1 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ A : BinaryMatrix n, ε ≤ distance A →
        c * ε^C * (n:ℝ)^8 ≤ (Counting.copyCount A:ℝ)

 theorem no_polynomial_removal : ¬ PolynomialRemoval := by
  rintro ⟨c,C,hc,hC,hrem⟩
  obtain ⟨ε,hε0,hε1,_,n,hn,_,A,hfar,hfew⟩ :=
    counterexample c C 1 hc hC (by norm_num) (fun _ => 1)
  exact (not_lt_of_ge (hrem n hn ε hε0 hε1 A hfar)) hfew

end Removal
end OrderedMatrixRemoval4
