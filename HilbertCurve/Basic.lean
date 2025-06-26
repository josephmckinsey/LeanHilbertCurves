import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace HilbertCurve

def hilbert_length (i : ℕ) := 2^(2*i)

/--
An inductive characterization of hilbert_length
-/
lemma hilbert_length_succ (i : ℕ) :
  hilbert_length (i + 1) = 4 * hilbert_length i := by
  simp [hilbert_length]
  rw [mul_add, pow_add]
  group

lemma hilbert_length_pos (i : ℕ) :
  0 < hilbert_length i := by simp [hilbert_length]

instance {α : Type} [PartialOrder α] [Ring α] [IsStrictOrderedRing α] :
  IsOrderedRing (α × α) where
  add_le_add_left
  | _, _, ⟨h1, h2⟩, (c1, c2) =>
    ⟨add_le_add_left h1 c1, add_le_add_left h2 c2⟩
  /-le_of_add_le_add_left
  | _, _, _, ⟨h1, h2⟩ =>
    ⟨le_of_add_le_add_left h1, le_of_add_le_add_left h2⟩
  -/
  zero_le_one := ⟨zero_le_one, zero_le_one⟩
  mul_le_mul_of_nonneg_left _ _ _
  | ⟨h1, h2⟩, ⟨h1', h2'⟩ =>
    ⟨mul_le_mul_of_nonneg_left h1 h1',
    mul_le_mul_of_nonneg_left h2 h2'⟩
  mul_le_mul_of_nonneg_right _ _ _
  | ⟨h1, h2⟩, ⟨h1', h2'⟩ =>
    ⟨mul_le_mul_of_nonneg_right h1 h1',
    mul_le_mul_of_nonneg_right h2 h2'⟩

end HilbertCurve

variable {R : Type*} [Ring R]

@[coe]
def NtimesN.toRtimesR : ℕ × ℕ → R × R := fun p => (p.1, p.2)

instance : Coe (ℕ × ℕ) (R × R) where
  coe := NtimesN.toRtimesR

@[simp]
theorem RtimesR.coe_prod (p : ℕ × ℕ) : (p : R × R) = (↑p.1, ↑p.2) := rfl

@[simp] theorem RtimesR.coe_first (p : ℕ × ℕ) : (p : R × R).1 = p.1 := rfl
@[simp] theorem RtimesR.coe_second (p : ℕ × ℕ) : (p : R × R).2 = p.2 := rfl

@[simp, norm_cast]
lemma NtimesN.cast_inj (mn mn' : ℕ × ℕ) : (mn : ℤ × ℤ) = mn' ↔ mn = mn' := by
  simp [<-Prod.ext_iff]

@[zify_simps]
lemma ZtimesZ.cast_eq (mn mn' : ℕ × ℕ) : mn = mn' ↔ (mn : ℤ × ℤ) = mn' := by
  simp [<-Prod.ext_iff]

@[zify_simps]
lemma ZtimesZ.cast_mul (mn mn' a : ℕ × ℕ) : mn * mn' = a ↔ (mn : ℤ × ℤ) * mn' = a := by
  zify
  simp

@[simp, norm_cast]
lemma NtimesN.cast_le (mn mn' : ℕ × ℕ) : (mn : ℤ × ℤ) ≤ mn' ↔ mn ≤ mn' := by
  simp [<-Prod.le_def]

@[zify_simps]
lemma ZtimesZ.cast_le (mn mn' : ℕ × ℕ) : mn ≤ mn' ↔ (mn : ℤ × ℤ) ≤ mn' := by
  simp [<-Prod.le_def]
