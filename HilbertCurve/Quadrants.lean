import HilbertCurve.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

inductive Quadrant where
| BOTTOM_LEFT | TOP_LEFT | TOP_RIGHT | BOTTOM_RIGHT
deriving DecidableEq

def get_quadrant (i n : ℕ) : Quadrant :=
  if n < hilbert_length i then
    Quadrant.BOTTOM_LEFT
  else if n < 2 * hilbert_length i then
    Quadrant.TOP_LEFT
  else if n < 3 * hilbert_length i then
    Quadrant.TOP_RIGHT
  else
    Quadrant.BOTTOM_RIGHT

def adjacent : Quadrant → Quadrant → Prop
| Quadrant.BOTTOM_LEFT, Quadrant.TOP_LEFT => True
| Quadrant.TOP_LEFT, Quadrant.TOP_RIGHT => True
| Quadrant.TOP_RIGHT, Quadrant.BOTTOM_RIGHT => True
| _, _ => False

def get_quadrant' (i : ℕ) : ℕ × ℕ → Quadrant
| (m, n) => if (m < 2^i) then
    if (n < 2^i) then
      Quadrant.BOTTOM_LEFT
    else
      Quadrant.TOP_LEFT
  else
    if (n < 2^i) then
      Quadrant.BOTTOM_RIGHT
    else
      Quadrant.TOP_RIGHT

lemma get_quadrant_rec (i n : ℕ) :
  get_quadrant (i+1) n = get_quadrant i (n/4) := by
  simp only [get_quadrant]
  simp_rw [mul_comm, hilbert_length_succ, Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)]
  rw [mul_assoc, mul_assoc, mul_comm, mul_comm 4 _, mul_comm 4 _]

lemma get_quadrant_end (i : ℕ) :
  get_quadrant i (hilbert_length (i+1) - 1) = Quadrant.BOTTOM_RIGHT := by
  simp [get_quadrant, hilbert_length]
  split_ifs with h
  · rw [mul_add, pow_add] at h
    omega
  · rw [mul_add, pow_add] at *
    omega
  · rw [mul_add, pow_add] at *
    omega
  rfl


lemma bottom_left_eq (i n : ℕ) :
  get_quadrant i n = Quadrant.BOTTOM_LEFT ↔ n < hilbert_length i := by
  rw [get_quadrant]
  constructor
  · split_ifs
    · intro _; trivial
    · intro h
      contradiction
    · intro h
      contradiction
    intro h
    contradiction
  intro h; rw [if_pos h]

lemma top_left_eq (i n : ℕ) :
  get_quadrant i n = Quadrant.TOP_LEFT ↔
  hilbert_length i ≤ n ∧ n < 2 * hilbert_length i:= by
  rw [get_quadrant]
  constructor
  · split_ifs
    · intro h; contradiction
    · intro h; omega
    · intro h; contradiction
    intro h; contradiction
  intro h
  rw [if_neg (by linarith), if_pos (by linarith)]

lemma top_right_eq (i n : ℕ) :
  get_quadrant i n = Quadrant.TOP_RIGHT ↔
  2*hilbert_length i ≤ n ∧ n < 3 * hilbert_length i:= by
  rw [get_quadrant]
  constructor
  · split_ifs
    · intro h; contradiction
    · intro h; contradiction
    · intro h; omega
    intro h; contradiction
  intro h
  rw [if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]

lemma bottom_right_eq (i n : ℕ) :
  get_quadrant i n = Quadrant.BOTTOM_RIGHT ↔
  3*hilbert_length i ≤ n := by
  rw [get_quadrant]
  constructor
  · split_ifs
    · intro h; contradiction
    · intro h; contradiction
    · intro h; contradiction
    intro h; linarith
  intro h
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

lemma bottom_left_quad (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i mn = Quadrant.BOTTOM_LEFT ↔
  mn.1 < 2^i ∧ mn.2 < 2^i := by
  rw [get_quadrant']
  constructor
  · split_ifs with h h'
    · intro _; trivial
    · intro h
      contradiction
    · intro h
      contradiction
    intro h
    contradiction
  intro h
  rw [if_pos h.1, if_pos h.2]

lemma top_left_quad (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i mn = Quadrant.TOP_LEFT ↔
  2^i ≤ mn.2 ∧ mn.1 < 2^i := by
  rw [get_quadrant']
  constructor
  · split_ifs with h h'
    · intro _; contradiction
    · intro _;
      omega
    · intro h
      contradiction
    intro h
    contradiction
  intro h
  rw [if_pos]
  · rw [if_neg]
    linarith
  exact h.2

lemma top_right_quad (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i mn = Quadrant.TOP_RIGHT ↔
  2^i ≤ mn.1 ∧ 2^i ≤ mn.2 := by
  rw [get_quadrant']
  constructor
  · split_ifs with h h'
    · intro _; contradiction
    · intro _; contradiction
    · intro h
      contradiction
    intro h
    omega
  intro h
  rw [if_neg]
  · rw [if_neg]
    omega
  omega

lemma bottom_right_quad (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i mn = Quadrant.BOTTOM_RIGHT ↔
  2^i ≤ mn.1 ∧ mn.2 < 2^i:= by
  rw [get_quadrant']
  constructor
  · split_ifs with h h'
    · intro _; contradiction
    · intro _; contradiction
    · intro _
      omega
    intro _
    contradiction
  intro h
  rw [if_neg]
  · rw [if_pos]
    exact h.2
  omega
