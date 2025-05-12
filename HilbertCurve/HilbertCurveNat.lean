-- This module serves as the root of the `HilbertCurve` library.
-- Import modules here that should be built as part of the library.
import HilbertCurve.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Sub.Defs
import HilbertCurve.Quadrants
import HilbertCurve.Transformations

/-
universe u in
def hilbert_cases {motive : ℕ → Sort u} (i : ℕ) (n : ℕ)
    (h1 : ∀n, n < hilbert_length i → motive n)
    (h2 : ∀n, hilbert_length i ≤ n → n < 2*hilbert_length i → motive n)
    (h3 : ∀n, 2*hilbert_length i ≤ n → n < 3*hilbert_length i → motive n)
    (h4 : ∀n, 3*hilbert_length i ≤ n → motive n) : motive n :=
  if h : n < hilbert_length i then
    h1 n h
  else if h' : n < 2 * hilbert_length i then
    h2 n (Nat.le_of_not_lt h) h'
  else if h'' : n < 3 * hilbert_length i then
    h3 n (Nat.le_of_not_lt h') h''
  else
    h4 n (Nat.le_of_not_lt h'')

-/

def hilbert_curve : ℕ → ℕ → (ℕ × ℕ)
| 0 => fun _ => (0, 0)
| .succ i => fun n => match get_quadrant i n with
  | Quadrant.BOTTOM_LEFT =>
    let h := hilbert_curve i n
    T0_nat h
  | Quadrant.TOP_LEFT => let h := hilbert_curve i (n - hilbert_length i)
    T1_nat i h
  | Quadrant.TOP_RIGHT => let h := hilbert_curve i (n - 2*hilbert_length i)
    T2_nat i h
  | Quadrant.BOTTOM_RIGHT =>
    let h := hilbert_curve i (n - 3*hilbert_length i)
    T3_nat i h
    --(2^(i+1) - 1, 2^i - 1) - (h.2, h.1)

/-
def hilbert_curve : ℕ → ℕ → (ℕ × ℕ)
| 0 => fun _ => (0, 0)
| .succ i => fun n =>
  if n < 2^(2*i) then
    let h := hilbert_curve i n
    (h.2, h.1)
  else if n < 2*2^(2*i) then
    let h := hilbert_curve i (n - 2^(2*i))
    h + (0, 2^i)
  else if n < 3*2^(2*i) then
    let h := hilbert_curve i (n - 2*2^(2*i))
    h + (2^i, 2^i)
  else
    let h := hilbert_curve i (n - 3*2^(2*i))
    (2^(i+1) - 1 - h.2, 2^i - 1 - h.1)
-/

/--
info: (0, 0)
-/
#guard_msgs in
#eval hilbert_curve 0 0

/--
info: [(0, 0), (0, 1), (1, 1), (1, 0)]
-/
#guard_msgs in
#eval List.map (hilbert_curve 1) (List.range (2^2))

def hilbert_inverse : ℕ → ℕ × ℕ → ℕ
| 0 => fun _ => 0
| .succ i => fun mn => match get_quadrant' i mn with
  | Quadrant.BOTTOM_LEFT =>
      hilbert_inverse i (T0_nat mn)
  | Quadrant.TOP_LEFT =>
    hilbert_length i + hilbert_inverse i (T1_inv_nat i mn)
  | Quadrant.BOTTOM_RIGHT =>
    3*hilbert_length i + hilbert_inverse i (T3_inv_nat i mn)
  | Quadrant.TOP_RIGHT =>
      2*hilbert_length i + hilbert_inverse i (T2_inv_nat i mn)

#eval hilbert_curve 2 4
#guard hilbert_inverse 10 (hilbert_curve 10 304) = 304

/--
A hilbert curve begins at (0, 0)
-/
lemma hilbert_curve_start (i : ℕ) : hilbert_curve i 0 = (0, 0) := by
  induction i with
  | zero => simp [hilbert_curve]
  | succ i ih => rw [hilbert_curve]; simp [get_quadrant, T0_nat, hilbert_length, ih]

/--
A hilbert curve ends at (2^i - 1, 0)
-/
lemma hilbert_curve_end (i : ℕ) : hilbert_curve i (hilbert_length i - 1) = (2^i - 1, 0) := by
  induction i with
  | zero => simp [hilbert_curve]
  | succ i ih =>
    simp [hilbert_curve]
    rw [get_quadrant_end]
    dsimp
    rw [hilbert_length_succ]
    rw [show ∀a>0, 4*a - 1 - 3*a = a - 1 by intro a ah; omega]
    · rw [ih]
      simp [T3_nat]
    exact hilbert_length_pos i

lemma hilbert_curve_size (i n : ℕ) :
  hilbert_curve i n ≤ (2^i -1, 2^i - 1) := by
  induction i generalizing n with
  | zero =>
    simp [hilbert_curve]
  | succ i ih =>
    unfold hilbert_curve
    split
    · apply le_trans (b := (2^i - 1, 2^i - 1))
      · exact Prod.swap_le_swap.mp (ih n)
      simp; omega
      --apply Prod.mk_le_mk.mpr
    · have := ih (n - hilbert_length i)
      dsimp
      zify
      rw [<-T1_cast_nat, T1]
      calc
        (hilbert_curve i (n - hilbert_length i) : ℤ × ℤ) + (0, 2^i)
        ≤ ((2 : ℤ)^i - 1, 2^i - 1) + (0, 2^i) := by
          apply add_le_add_right
          rw [show ((2 ^ i - 1, 2 ^ i - 1) : ℤ × ℤ) = ((2^i -1, 2^i - 1) : ℕ × ℕ) by simp]
          exact_mod_cast ih (n - hilbert_length i)
        _ = (2^i - 1, 2^i + 2^i - 1) := by simp; ring
        _ = (2^i - 1, 2^(i+1) - 1) := by simp; ring
        _ ≤ (2^(i+1) -1, 2^(i+1) - 1) := by simp [pow_add]
      simp
    · have := ih (n - 2*hilbert_length i)
      dsimp
      zify
      rw [<-T2_cast_nat, T2]
      calc
        (hilbert_curve i _ : ℤ × ℤ) + (2^i, 2^i) ≤ (2^i - 1, 2^i - 1) + (2^i, 2^i) := by
          apply add_le_add_right
          rw [show ((2 ^ i - 1, 2 ^ i - 1) : ℤ × ℤ) = ((2^i -1, 2^i - 1) : ℕ × ℕ) by simp]
          exact_mod_cast ih _
        _ = (2^(i+1) - 1, 2^(i+1) - 1) := by
          simp [pow_add]; omega
      simp
    have := (T3_nat_bound i (hilbert_curve i (n - 3*hilbert_length i)))
    refine ⟨this.1, ?_⟩
    apply le_trans this.2
    omega

def dist' (x y : ℕ × ℕ) : ℕ :=
  ((x.1 : ℤ) - (y.1 : ℤ)).natAbs ⊔ ((x.2 : ℤ) - (y.2 : ℤ)).natAbs

lemma dist'_symm (x y : ℕ × ℕ) :
  dist' x y = dist' y x := by
  unfold dist'
  omega


lemma dist'_flip (x y : ℕ × ℕ) :
  dist' (x.2, x.1) (y.2, y.1) = dist' x y := by
  unfold dist'
  omega

lemma dist'_add (x y z : ℕ × ℕ) :
  dist' (x+z) (y+z) = dist' x y := by
  unfold dist'
  simp

lemma dist'_eq_0 (x y : ℕ × ℕ) :
  dist' x y = 0 ↔ x = y := by
  rw [dist']
  simp [Prod.ext_iff]
  omega

lemma dist'_sub {a b c : ℕ × ℕ} (h : a ≤ c) (h' : b ≤ c) :
  dist' (c - a) (c - b) = dist' a b := by
  simp [dist']
  congr 1
  · rw [Int.ofNat_sub (Prod.mk_le_mk.mp h).1]
    rw [Int.ofNat_sub (Prod.mk_le_mk.mp h').1]
    zify
    rw [sub_sub_sub_cancel_left (c := (c.1 : ℤ))]
    rw [abs_sub_comm]
  rw [Int.ofNat_sub (Prod.mk_le_mk.mp h).2]
  rw [Int.ofNat_sub (Prod.mk_le_mk.mp h').2]
  zify
  rw [sub_sub_sub_cancel_left (c := (c.2 : ℤ))]
  rw [abs_sub_comm]

@[simp]
lemma dist'_T0 (x y : ℕ × ℕ) :
  dist' (T0_nat x) (T0_nat y) = dist' x y := by
  simp only [T0_nat]
  exact dist'_flip x y

@[simp]
lemma dist'_T1 (i : ℕ) (x y : ℕ × ℕ) :
  dist' (T1_nat i x) (T1_nat i y) = dist' x y := by
  simp [T1_nat, dist'_add]

@[simp]
lemma dist'_T2 (i : ℕ) (x y : ℕ × ℕ) :
  dist' (T2_nat i x) (T2_nat i y) = dist' x y := by
  simp [T2_nat, dist'_add]

lemma dist'_cast (x y : ℕ × ℕ) :
  dist' x y = dist (x : ℤ × ℤ) (y : ℤ × ℤ) := by
  simp [dist', dist, Int.cast_natAbs]

@[simp]
lemma dist'_T3 (i : ℕ) (x y : ℕ × ℕ)
  (h1 : x.1 ≤ 2 ^ i - 1) (h2 : x.2 ≤ 2 ^ (i + 1) - 1)
  (h1' : y.1 ≤ 2 ^ i - 1) (h2' : y.2 ≤ 2 ^ (i + 1) - 1) :
  dist' (T3_nat i x) (T3_nat i y) = dist' x y := by
  -- We could use dist'_sub too
  rify
  rw [dist'_cast]
  rw [<-T3_cast_nat _ _ h1 h2, <-T3_cast_nat _ _ h1' h2', T3, T3, dist'_cast]
  rw [dist_sub_left]
  simp only [dist, RtimesR.coe_prod, Prod.swap_prod_mk, Int.cast_natCast]
  rw [sup_comm]

lemma split_domain (i : ℕ) (n : ℕ) :
  n < hilbert_length i ∨
  (hilbert_length i ≤ n ∧ n < 2*hilbert_length i) ∨
  (2*hilbert_length i ≤ n ∧ n < 3*hilbert_length i) ∨
  (3*hilbert_length i ≤ n) := by
  omega  -- I love omega

lemma n_and_n_succ_adjacent_or_equal (i n : ℕ) :
  let q1 := get_quadrant i n
  let q2 := get_quadrant i (n+1)
  adjacent q1 q2 ∨ q1 = q2 := by
  have nsucc_lt {a : ℕ} (apos : a > 0) (h : n < a * hilbert_length i) :
    n + 1 < a * hilbert_length i ∨ n+1 = a* hilbert_length i := by
    omega
  rcases split_domain i n with h | h | h | h
  · have := nsucc_lt (by norm_num : 1 > 0)
    rw [one_mul] at this
    replace this := this h
    rcases this with same | different
    <;> rw [get_quadrant, if_pos h, get_quadrant]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different]), if_pos]
    · left; trivial
    omega
  · have := nsucc_lt (by norm_num : 2 > 0)
    replace this := this h.2
    rcases this with same | different
    <;> rw [get_quadrant, if_neg (Nat.not_lt.mpr h.1), if_pos h.2, get_quadrant, if_neg (by linarith)]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different]), if_pos]
    · left; trivial
    omega
  · have := nsucc_lt (by norm_num : 3 > 0) h.2
    rcases this with same | different
    <;> rw [get_quadrant, if_neg (by linarith), if_neg (Nat.not_lt.mpr h.1), if_pos h.2, get_quadrant, if_neg (by linarith), if_neg (by linarith)]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different])]
    left; trivial
  · rw [get_quadrant, get_quadrant]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    right; trivial

def at_end (i n : ℕ) : Prop :=
  (n + 1 = hilbert_length i) ∨
  (n + 1 = 2 * hilbert_length i) ∨
  (n + 1 = 3 * hilbert_length i)

lemma hilbert_start1 (i : ℕ) :
  hilbert_curve (i+1) (hilbert_length i - 1) = (0, 2^i - 1) := by
  unfold hilbert_curve
  have := (bottom_left_eq i (hilbert_length i - 1)).mpr (by simp [hilbert_length_pos])
  simp [this, hilbert_curve_end, T0_nat]

lemma hilbert_end1 (i : ℕ) :
  hilbert_curve (i+1) (hilbert_length i) = (0, 2^i) := by
  unfold hilbert_curve
  have := (top_left_eq i (hilbert_length i)).mpr (by simp [hilbert_length_pos])
  simp [this, T1_nat, hilbert_curve_start]

lemma hilbert_start2 (i : ℕ) :
  hilbert_curve (i+1) (2*hilbert_length i - 1) = (2^i - 1, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_left_eq i (2*hilbert_length i - 1)).mpr (by omega)
  have hilbert_length_minus1 : 2 * hilbert_length i - 1 - hilbert_length i = hilbert_length i - 1 := by
    omega
  simp [this, hilbert_length_minus1, T1_nat, hilbert_curve_end]

lemma hilbert_end2 (i : ℕ) :
  hilbert_curve (i+1) (2*hilbert_length i) = (2^i, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_right_eq i (2*hilbert_length i)).mpr (by omega)
  rw [this]
  simp [Nat.sub_self, hilbert_curve_start, T2_nat]

lemma hilbert_start3 (i : ℕ) :
  hilbert_curve (i+1) (3*hilbert_length i - 1) = (2^(i+1) - 1, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_right_eq i (3*hilbert_length i - 1)).mpr (by omega)
  rw [this]
  have : 3 * hilbert_length i - 1 - 2*hilbert_length i = hilbert_length i - 1 := by
    omega
  simp [this, hilbert_curve_end, T2_nat, pow_add, pow_one]
  omega

lemma hilbert_end3 (i : ℕ) :
  hilbert_curve (i+1) (3*hilbert_length i) = (2^(i+1) - 1, 2^i - 1) := by
  unfold hilbert_curve
  have := (bottom_right_eq i (3*hilbert_length i)).mpr (by omega)
  rw [this]
  zify
  simp [<-T3_cast_nat, T3_nat, hilbert_curve_start]

lemma n_and_n_succ_adjacent_or_equal' (i n : ℕ) :
  let q1 := get_quadrant i n
  let q2 := get_quadrant i (n+1)
  at_end i n ∨ q1 = q2 := by
  have nsucc_lt {a : ℕ} (apos : a > 0) (h : n < a * hilbert_length i) :
    n + 1 < a * hilbert_length i ∨ n+1 = a* hilbert_length i := by
    omega
  rcases split_domain i n with h | h | h | h
  · have := nsucc_lt (by norm_num : 1 > 0)
    rw [one_mul] at this
    replace this := this h
    rcases this with same | different
    <;> rw [get_quadrant, if_pos h, get_quadrant]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different]), if_pos]
    · simp [at_end, different]
    omega
  · have := nsucc_lt (by norm_num : 2 > 0)
    replace this := this h.2
    rcases this with same | different
    <;> rw [get_quadrant, if_neg (Nat.not_lt.mpr h.1), if_pos h.2, get_quadrant, if_neg (by linarith)]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different]), if_pos]
    · simp [at_end, different]
    omega
  · have := nsucc_lt (by norm_num : 3 > 0) h.2
    rcases this with same | different
    <;> rw [get_quadrant, if_neg (by linarith), if_neg (Nat.not_lt.mpr h.1), if_pos h.2, get_quadrant, if_neg (by linarith), if_neg (by linarith)]
    · rw [if_pos same]
      right; rfl
    rw [if_neg (by simp [different])]
    simp [at_end, different]
  · rw [get_quadrant, get_quadrant]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    right; trivial


/--
A hilbert curve moves by at most 1 each time
-/
lemma hilbert_diff (i n : ℕ) : dist' (hilbert_curve i (n + 1)) (hilbert_curve i n) ≤ 1 := by
  induction i generalizing n with
  | zero => simp [hilbert_curve, dist']
  | succ i ih =>
    rcases n_and_n_succ_adjacent_or_equal' i n with (h | h | h) | h
    · have : n = hilbert_length i - 1 := by omega
      rw [h, this, hilbert_start1 i, hilbert_end1 i]
      simp [dist']
    · have : n = 2*hilbert_length i - 1 := by omega
      rw [h, this, hilbert_start2 i, hilbert_end2 i]
      simp [dist']
    · have : n = 3*hilbert_length i - 1 := by omega
      rw [h, this, hilbert_start3 i, hilbert_end3 i]
      simp [dist']
    rw [hilbert_curve]
    dsimp
    rw [<-h]
    set q := get_quadrant i n with quad
    have := hilbert_length_pos i
    rcases q
    · rw [dist'_T0]
      exact ih n
    · rw [dist'_T1]
      have := (top_left_eq i n).mp quad.symm
      rw [show n + 1 - hilbert_length i = (n - hilbert_length i) + 1 by omega]
      exact ih (n - hilbert_length i)
    · rw [dist'_T2]
      have := (top_right_eq i n).mp quad.symm
      rw [show n + 1 - 2*hilbert_length i = (n - 2*hilbert_length i) + 1 by omega]
      exact ih (n - 2*hilbert_length i)
    have := (bottom_right_eq i n).mp quad.symm
    have h'_small : hilbert_curve i (n - 3*hilbert_length i) ≤ (2^i - 1, 2^(i+1) - 1) := by
      apply le_trans (hilbert_curve_size i _)
      simp [pow_add]
      omega
    have h_small : hilbert_curve i (n - 3 * hilbert_length i + 1) ≤ (2^i - 1, 2^(i+1) -1) := by
      apply le_trans (hilbert_curve_size i _)
      simp [pow_add]
      omega
    rw [show n + 1 - 3*hilbert_length i = (n - 3*hilbert_length i) + 1 by omega]
    rw [dist'_T3 _ _ _ h_small.1 h_small.2 h'_small.1 h'_small.2]
    exact ih (n - 3*hilbert_length i)


lemma get_quadrant'_T0 (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T0_nat mn) = Quadrant.BOTTOM_LEFT := by
  simp only [get_quadrant', T0_nat]
  have : 2^i - 1 < 2^i := by simp
  rw [if_pos, if_pos]
  · apply lt_of_le_of_lt h.1 this
  apply lt_of_le_of_lt h.2 this

lemma get_quadrant'_T1 (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T1_nat i mn) = Quadrant.TOP_LEFT := by
  simp only [get_quadrant', T1_nat]
  have : 2^i - 1 < 2^i := by simp
  rw [if_pos, if_neg]
  · simp
  apply lt_of_le_of_lt h.1 this

lemma get_quadrant'_T2 (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i (T2_nat i mn) = Quadrant.TOP_RIGHT := by
  simp only [get_quadrant']
  rw [if_neg, if_neg]
  · simp [T2_nat]
  simp [T2_nat]

lemma get_quadrant'_T3 (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T3_nat i mn) = Quadrant.BOTTOM_RIGHT := by
  simp only [get_quadrant']
  rw [if_neg, if_pos]
  · suffices (T3_nat i mn : ℤ × ℤ).2 < 2^i by
      zify
      exact this
    rw [<- T3_cast_nat i _ h.1 (le_trans h.2 (by omega))]
    simp [T3]
    omega
  suffices 2^i ≤ (T3_nat i mn : ℤ × ℤ).1 by
    zify
    simpa using this
  rw [<- T3_cast_nat i _ h.1 (le_trans h.2 (by omega))]
  simp [T3]
  suffices 2^i + mn.2 ≤ 2^(i+1) - (1 : ℤ) by
    linarith
  rw [pow_add, pow_one, mul_two, add_sub_assoc]
  apply add_le_add_left
  have : (2^i - 1 : ℤ) = (2^i - 1 : ℕ) := by
    rw [Nat.cast_sub]
    · norm_cast
    exact Nat.one_le_two_pow
  rw [this]
  exact_mod_cast h.2

lemma quadrant_preserved (i n : ℕ) :
  get_quadrant' i (hilbert_curve (i+1) n) = get_quadrant i n := by
  set q := get_quadrant i n with q_def
  unfold hilbert_curve
  rcases q <;> rw [<-q_def] <;> dsimp
  · apply get_quadrant'_T0
    exact hilbert_curve_size i n
  · apply get_quadrant'_T1
    exact hilbert_curve_size i _
  · apply get_quadrant'_T2
  apply get_quadrant'_T3
  exact hilbert_curve_size i _

lemma hilbert_inverse_size (i : ℕ) (mn : ℕ × ℕ) :
  hilbert_inverse i mn < hilbert_length i := by
  induction i generalizing mn with
  | zero => simp [hilbert_length, hilbert_inverse]
  | succ i ih =>
    unfold hilbert_inverse
    set q := get_quadrant' i mn with q_def
    have := hilbert_length_pos i
    rcases q
    · simp [T0_nat]
      apply lt_trans (ih _)
      rw [hilbert_length_succ]
      linarith
    · simp
      calc
        hilbert_length i + hilbert_inverse i _ < hilbert_length i + hilbert_length i := by
          apply add_lt_add_left
          exact ih _
        _ < hilbert_length (i+1) := by
          rw [hilbert_length_succ]
          linarith
    · simp
      calc
        2*hilbert_length i + hilbert_inverse i _ < 2*hilbert_length i + hilbert_length i := by
          apply add_lt_add_left
          exact ih _
        _ < hilbert_length (i+1) := by
          rw [hilbert_length_succ]
          linarith
    simp
    calc
      3*hilbert_length i + hilbert_inverse i _ < 3*hilbert_length i + hilbert_length i := by
        apply add_lt_add_left
        exact ih _
      _ = hilbert_length (i+1) := by
        rw [hilbert_length_succ]
        group

lemma quadrant'_preserved (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant i (hilbert_inverse (i+1) mn) = get_quadrant' i mn := by
  set q := get_quadrant' i mn with q_def
  unfold hilbert_inverse
  rcases q
  · simp [<-q_def]
    rw [bottom_left_eq]
    exact hilbert_inverse_size i (mn.2, mn.1)
  · simp [<-q_def]
    rw [top_left_eq]
    have := hilbert_inverse_size i (T1_inv_nat i mn)
    constructor
    · linarith
    linarith
  · simp [<-q_def]
    have := hilbert_inverse_size i (T2_inv_nat i mn)
    rw [top_right_eq]
    constructor
    · linarith
    linarith
  simp [<-q_def]
  have := hilbert_inverse_size i (T3_inv_nat i mn)
  rw [bottom_right_eq]
  linarith

/--
A hilbert curve is injective on its length
-/
lemma hilbert_curve_injective (i : ℕ) (n : ℕ) (h : n < hilbert_length i) :
  hilbert_inverse i (hilbert_curve i n) = n := by
  induction i generalizing n with
  | zero =>
    simp [hilbert_length] at h
    rw [h]
    simp [hilbert_curve, hilbert_inverse]
  | succ i ih =>
    have := quadrant_preserved i n
    set q := get_quadrant i n with q_def
    unfold hilbert_inverse
    rw [this]
    rcases q <;> dsimp <;> unfold hilbert_curve <;> rw [<-q_def]
    · simp  [T0_involutive]
      apply ih
      exact (bottom_left_eq i n).mp (Eq.symm q_def)
    · simp only
      rw [T1_inv_of_T1_nat]
      have := (top_left_eq i n).mp (Eq.symm q_def)
      rw [ih (n - hilbert_length i)]
      · omega
      omega
    · simp only
      rw [T2_inv_of_T2_nat]
      have := (top_right_eq i n).mp (Eq.symm q_def)
      rw [ih (n - 2*hilbert_length i)]
      · omega
      omega
    simp only
    have size := hilbert_curve_size i (n - 3 * hilbert_length i)
    rw [T3_inv_of_T3_nat]
    · rw [ih _]
      · have := (bottom_right_eq i n).mp (Eq.symm q_def)
        omega
      rw [hilbert_length_succ] at h
      omega
    · exact size.1
    apply le_trans size.2
    omega


/--
A hilbert curve touches every point in the square
-/
lemma hilbert_curve_of_inverse (i : ℕ) (mn : ℕ × ℕ) (h : mn.1 < 2^i) (h' : mn.2 < 2^i) :
  hilbert_curve i (hilbert_inverse i mn) = mn := by
  induction i generalizing mn with
  | zero =>
    simp at h h'
    rw [show mn = 0 from Prod.mk_eq_zero.mpr ⟨h, h'⟩]
    simp [hilbert_inverse, hilbert_curve]
  | succ i ih =>
    unfold hilbert_curve
    have := quadrant'_preserved i mn
    rw [this]
    unfold hilbert_inverse
    set q := get_quadrant' i mn with q_def
    rcases q <;> simp [<-q_def]
    · have := (bottom_left_quad i mn).mp q_def.symm
      rw [ih, T0_nat_involutive]
      · rw [T0_nat]; exact this.2
      rw [T0_nat]; exact this.1
    · have := (top_left_quad i mn).mp q_def.symm
      zify; rw [<-T1_cast_nat]
      rw [ih]
      · rw [<-T1_inv_cast_nat, T1_of_T1_inv]
        exact this.1
      · simp [T1_inv_nat, this.2]
      simp [T1_inv_nat]
      omega
    · have := (top_right_quad i mn).mp q_def.symm
      rw [ih]
      · zify; rw [<-T2_cast_nat, <-T2_inv_cast_nat, T2_of_T2_inv]
        exact this
      · simp [T2_inv_nat]; omega
      simp [T2_inv_nat]; omega
    have := (bottom_right_quad i mn).mp q_def.symm
    rw [ih]
    · zify
      rw [<-T3_cast_nat, <-T3_inv_cast_nat, T3_of_T3_inv]
      · omega
      · omega
      · simp [T3_inv_nat]
      simp [T3_inv_nat]
    · simp [T3_inv_nat]
      omega
    simp [T3_inv_nat]; omega

/-
Each iteration subdivides each square
-/
lemma subdivision_size (i n : ℕ) :
  2 * hilbert_curve i (n/4) ≤ hilbert_curve (i+1) n ∧
  hilbert_curve (i+1) n ≤ 2 * hilbert_curve i (n/4) + 1 := by
  induction i generalizing n with
  | zero =>
    simp [hilbert_curve]
    split
    <;> simp [T0_nat, T1_nat, T2_nat, T3_nat, Prod.le_def]
  | succ i ih =>
    have two_def : (2 : ℕ × ℕ) = ((2 : ℕ), (2 : ℕ)) := rfl
    unfold hilbert_curve
    rw [get_quadrant_rec]
    set q := get_quadrant i (n/4) with q_def
    have two_swap : ∀mn, 2 * (mn : ℕ × ℕ).swap = (2 * mn).swap := by
      simp [Prod.swap, Prod.mul_def]
    have swap_one : ∀mn, (mn : ℕ × ℕ).swap + 1 = (mn + 1).swap := by
      simp [Prod.swap, Prod.add_def]
    rcases q
    · dsimp
      rw [T0_nat, two_swap, swap_one, Prod.swap_le_swap, Prod.swap_le_swap]
      exact ih n
    · dsimp
      apply T1_within_square
      rw [hilbert_length_succ]
      have : (n / 4 - hilbert_length i) = (n - 4 * hilbert_length i) / 4 := by
        omega
      rw [this]
      apply ih
    · dsimp
      apply T2_within_square
      have : (n / 4 - 2*hilbert_length i) = (n - 2*(4*hilbert_length i)) / 4 := by
        omega
      rw [hilbert_length_succ, this]
      apply ih
    dsimp
    have : (n / 4 - 3*hilbert_length i) = (n - 3*(4*hilbert_length i)) / 4 := by
      omega
    rw [hilbert_length_succ, this]
    apply T3_within_square
    · exact hilbert_curve_size i ((n - 3 * (4 * hilbert_length i)) / 4)
    · exact hilbert_curve_size (i + 1) (n - 3 * (4 * hilbert_length i))
    apply ih

instance : IsOrderedRing (ℕ × ℕ) where
  add_le_add_left := by
    intro a b h c
    rw [Prod.le_def] at *
    simpa
  zero_le_one := by
    rw [Prod.le_def]; simp
  mul_le_mul_of_nonneg_left := by
    intro a b c h h'
    rw [Prod.le_def]
    simp [mul_le_mul_of_nonneg_left h.1 h'.1,
      mul_le_mul_of_nonneg_left h.2 h'.2]
  mul_le_mul_of_nonneg_right :=  by
    intro a b c h h'
    rw [Prod.le_def]
    simp [mul_le_mul_of_nonneg_right h.1 h'.1,
      mul_le_mul_of_nonneg_right h.2 h'.2]

lemma NtimesN.add_sub_assoc {m k : ℕ × ℕ} (h : k ≤ m) (n : ℕ × ℕ) : n + m - k = n + (m - k) := by
  rw [Prod.ext_iff]
  simp
  rw [Nat.add_sub_assoc h.1, Nat.add_sub_assoc h.2]
  simp

lemma subdivision_cauchy (i j n : ℕ) :
  2^j * hilbert_curve i (n/(2^(2*j))) ≤ hilbert_curve (i+j) n ∧
  hilbert_curve (i+j) n ≤ 2^j * hilbert_curve i (n/(2^(2*j))) + 2^j - 1 := by
  induction j generalizing i with
  | zero =>
    simp only [pow_zero, mul_zero, Nat.div_one, one_mul, add_zero, le_refl, true_and]
    exact le_refl _
  | succ j ih =>
    set m := n / 2 ^ (2 * j) with m_def
    have : n / 2 ^ (2 * (j+1)) = m / 4 := by
      rw [m_def, mul_add, pow_add]
      simp [Nat.div_div_eq_div_mul]
    rw [this]
    rw [show (i + (j + 1)) = (i + 1) + j by group]
    constructor
    · rw [pow_add, pow_one, mul_assoc]
      calc
        2^j * (2 * hilbert_curve i (m / 4))
        ≤ 2^j * (hilbert_curve (i + 1) m) := by
          apply mul_le_mul_of_nonneg_left
          · apply (subdivision_size _ _).1
          simp
       _ ≤ _ := by
        exact (ih (i + 1)).1
    apply le_trans (ih (i+1)).2
    have := (subdivision_size i m).2
    have : 2^j * hilbert_curve (i + 1) m ≤ 2^(j+1) * hilbert_curve i (m / 4) + 2^j := by
      rw [show ∀a, a + (2^j : ℕ × ℕ) = a + 2^j * 1 by simp]
      rw [pow_succ, mul_assoc, <-mul_add]
      apply mul_le_mul_of_nonneg_left this (by simp)
    nth_rw 2 [pow_succ]
    rw [mul_two, <-add_assoc]
    have one_le_two_pow : (1 : ℕ × ℕ) ≤ 2^j  := by rw [Prod.le_def]; simp [Nat.one_le_two_pow]
    rw [NtimesN.add_sub_assoc (k := 1) one_le_two_pow]
    rw [NtimesN.add_sub_assoc (k := 1) one_le_two_pow]
    apply add_le_add_right this
