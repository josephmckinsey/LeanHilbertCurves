import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

def hello := "world"

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
