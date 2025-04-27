-- This module serves as the root of the `HilbertCurve` library.
-- Import modules here that should be built as part of the library.
import HilbertCurve.Basic
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Sub.Defs
import HilbertCurve.Quadrants
import HilbertCurve.Transformations
import Mathlib.Data.Real.Basic -- Added import
import Mathlib.Algebra.Order.Archimedean.Basic

open ProofWidgets Svg
open scoped Real -- Added open scoped

private def frame : Frame where
  xmin   := -2
  ymin   := -2
  xSize  := 4
  width  := 400
  height := 400


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
    T0' h
  | Quadrant.TOP_LEFT => let h := hilbert_curve i (n - hilbert_length i)
    T1' i h
  | Quadrant.TOP_RIGHT => let h := hilbert_curve i (n - 2*hilbert_length i)
    T2' i h
  | Quadrant.BOTTOM_RIGHT =>
    let h := hilbert_curve i (n - 3*hilbert_length i)
    T3' i h
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
      hilbert_inverse i (T0' mn)
  | Quadrant.TOP_LEFT =>
    hilbert_length i + hilbert_inverse i (T1'_inv i mn)
  | Quadrant.BOTTOM_RIGHT =>
    3*hilbert_length i + hilbert_inverse i (T3'_inv i mn)
  | Quadrant.TOP_RIGHT =>
      2*hilbert_length i + hilbert_inverse i (T2'_inv i mn)

#eval hilbert_curve 2 4
#guard hilbert_inverse 10 (hilbert_curve 10 304) = 304

/--
  Create an SVG visualization of the i-th order Hilbert curve.
-/
def hilbert_curve_svg (i : ℕ) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  { elements := lineElements.toArray }

-- Example: Display a Hilbert curve of order 2
#html (hilbert_curve_svg 2).toHtml
#html (hilbert_curve_svg 4).toHtml -- Looks good

/--
A hilbert curve begins at (0, 0)
-/
lemma hilbert_curve_start (i : ℕ) : hilbert_curve i 0 = (0, 0) := by
  induction i with
  | zero => simp [hilbert_curve]
  | succ i ih => rw [hilbert_curve]; simp [get_quadrant, T0', hilbert_length, ih]

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
      simp [T3']
    exact hilbert_length_pos i

/-

instance test : IsOrderedAddMonoid (ℕ × ℕ) where
  add_le_add_left := by
    intro a b
    rcases a
    rcases b
    simp

instance test2 : OrderedSub (ℕ × ℕ) where
  tsub_le_iff_right := by
    intro a b c
    rcases a
    rcases b
    rcases c
    simp

instance : CanonicallyOrderedAdd (ℕ × ℕ) where
  exists_add_of_le := by
    intro a b h
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    rw [Prod.mk_le_mk] at h
    have ⟨c1, c1h⟩ : ∃c1, b1 = a1 + c1 := exists_add_of_le h.1
    have ⟨c2, c2h⟩ : ∃c2, b2 = a2 + c2 := exists_add_of_le h.2
    use ⟨c1, c2⟩
    simp [c1h, c2h]
  le_self_add := by
    intro a b
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1, b2⟩
    have self_add_a := le_self_add (a := a1) (b := b1)
    have self_add_b := le_self_add (a := a2) (b := b2)
    simp [self_add_a, self_add_b]


instance test3 : IsOrderedCancelAddMonoid (ℕ × ℕ) where
  le_of_add_le_add_left := by
    intro a b c
    rcases a; rcases b; rcases c
    simp
-/

#check (inferInstance : Ring (ℤ × ℤ))
#check IsStrictOrderedRing ℤ

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
      rw [<-T1_cast, T1]
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
      rw [<-T2_cast, T2]
      calc
        (hilbert_curve i _ : ℤ × ℤ) + (2^i, 2^i) ≤ (2^i - 1, 2^i - 1) + (2^i, 2^i) := by
          apply add_le_add_right
          rw [show ((2 ^ i - 1, 2 ^ i - 1) : ℤ × ℤ) = ((2^i -1, 2^i - 1) : ℕ × ℕ) by simp]
          exact_mod_cast ih _
        _ = (2^(i+1) - 1, 2^(i+1) - 1) := by
          simp [pow_add]; omega
      simp
    have := (T3'_bound i (hilbert_curve i (n - 3*hilbert_length i)))
    refine ⟨this.1, ?_⟩
    apply le_trans this.2
    omega

def sum_square : ℤ × ℤ → ℤ
| (m, n) => m^2 + n^2

lemma sum_square_eq_0_iff (a : ℤ × ℤ) :
  sum_square a = 0 ↔ a = 0 := by
  rw [sum_square]
  have h : ∀a : ℤ, a^2 = (a^2).natAbs := by
    intro a
    simp only [Int.natCast_natAbs, abs_pow, sq_abs]
  nth_rw 1 [h]
  nth_rw 2 [h]
  norm_cast
  simp [Prod.ext_iff]


def dist' (x y : ℕ × ℕ) : ℕ :=
  ((x.1 : ℤ) - (y.1 : ℤ)).natAbs + ((x.2 : ℤ) - (y.2 : ℤ)).natAbs

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
lemma dist'_T0' (x y : ℕ × ℕ) :
  dist' (T0' x) (T0' y) = dist' x y := by
  simp only [T0']
  exact dist'_flip x y

@[simp]
lemma dist'_T1' (i : ℕ) (x y : ℕ × ℕ) :
  dist' (T1' i x) (T1' i y) = dist' x y := by
  simp [T1', dist'_add]

@[simp]
lemma dist'_T2' (i : ℕ) (x y : ℕ × ℕ) :
  dist' (T2' i x) (T2' i y) = dist' x y := by
  simp [T2', dist'_add]

lemma dist'_cast (x y : ℕ × ℕ) :
  dist' x y = (abs ((x : ℤ × ℤ) - y).1) + (abs ((x : ℤ × ℤ) - y).2):= by
  simp [dist']

@[simp]
lemma dist'_T3' (i : ℕ) (x y : ℕ × ℕ)
  (h1 : x.1 ≤ 2 ^ i - 1) (h2 : x.2 ≤ 2 ^ (i + 1) - 1)
  (h1' : y.1 ≤ 2 ^ i - 1) (h2' : y.2 ≤ 2 ^ (i + 1) - 1) :
  dist' (T3' i x) (T3' i y) = dist' x y := by
  -- We could use dist'_sub too
  zify
  rw [dist'_cast]
  rw [<-T3_cast _ _ h1 h2, <-T3_cast _ _ h1' h2', T3, T3, dist'_cast]
  simp
  rw [add_comm, abs_sub_comm, abs_sub_comm (y.2 : ℤ)]

lemma split_domain (i : ℕ) (n : ℕ) :
  n < hilbert_length (i + 1) ↔
  n < hilbert_length i ∨
  (hilbert_length i ≤ n ∧ n < 2*hilbert_length i) ∨
  (2*hilbert_length i ≤ n ∧ n < 3*hilbert_length i) ∨
  (3*hilbert_length i ≤ n ∧ n < 4*hilbert_length i) := by
  rw [hilbert_length_succ]
  omega  -- I love omega

lemma split_domain' (i : ℕ) (n : ℕ) :
  n < hilbert_length i ∨
  (hilbert_length i ≤ n ∧ n < 2*hilbert_length i) ∨
  (2*hilbert_length i ≤ n ∧ n < 3*hilbert_length i) ∨
  (3*hilbert_length i ≤ n) := by
  omega

lemma n_and_n_succ_adjacent_or_equal (i n : ℕ) :
  let q1 := get_quadrant i n
  let q2 := get_quadrant i (n+1)
  adjacent q1 q2 ∨ q1 = q2 := by
  have nsucc_lt {a : ℕ} (apos : a > 0) (h : n < a * hilbert_length i) :
    n + 1 < a * hilbert_length i ∨ n+1 = a* hilbert_length i := by
    omega
  rcases split_domain' i n with h | h | h | h
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
  simp [this, hilbert_curve_end, T0']

lemma hilbert_end1 (i : ℕ) :
  hilbert_curve (i+1) (hilbert_length i) = (0, 2^i) := by
  unfold hilbert_curve
  have := (top_left_eq i (hilbert_length i)).mpr (by simp [hilbert_length_pos])
  simp [this, T1', hilbert_curve_start]

lemma hilbert_start2 (i : ℕ) :
  hilbert_curve (i+1) (2*hilbert_length i - 1) = (2^i - 1, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_left_eq i (2*hilbert_length i - 1)).mpr (by omega)
  have hilbert_length_minus1 : 2 * hilbert_length i - 1 - hilbert_length i = hilbert_length i - 1 := by
    omega
  simp [this, hilbert_length_minus1, T1', hilbert_curve_end]

lemma hilbert_end2 (i : ℕ) :
  hilbert_curve (i+1) (2*hilbert_length i) = (2^i, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_right_eq i (2*hilbert_length i)).mpr (by omega)
  rw [this]
  simp [Nat.sub_self, hilbert_curve_start, T2']

lemma hilbert_start3 (i : ℕ) :
  hilbert_curve (i+1) (3*hilbert_length i - 1) = (2^(i+1) - 1, 2^i) := by
  unfold hilbert_curve
  have := hilbert_length_pos i
  have := (top_right_eq i (3*hilbert_length i - 1)).mpr (by omega)
  rw [this]
  have : 3 * hilbert_length i - 1 - 2*hilbert_length i = hilbert_length i - 1 := by
    omega
  simp [this, hilbert_curve_end, T2', pow_add, pow_one]
  omega

lemma hilbert_end3 (i : ℕ) :
  hilbert_curve (i+1) (3*hilbert_length i) = (2^(i+1) - 1, 2^i - 1) := by
  unfold hilbert_curve
  have := (bottom_right_eq i (3*hilbert_length i)).mpr (by omega)
  rw [this]
  zify
  simp [<-T3_cast, T3, hilbert_curve_start]

lemma n_and_n_succ_adjacent_or_equal' (i n : ℕ) :
  let q1 := get_quadrant i n
  let q2 := get_quadrant i (n+1)
  at_end i n ∨ q1 = q2 := by
  have nsucc_lt {a : ℕ} (apos : a > 0) (h : n < a * hilbert_length i) :
    n + 1 < a * hilbert_length i ∨ n+1 = a* hilbert_length i := by
    omega
  rcases split_domain' i n with h | h | h | h
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
example (i n : ℕ) : dist' (hilbert_curve i (n + 1)) (hilbert_curve i n) ≤ 1 := by
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
    · rw [dist'_T0']
      exact ih n
    · rw [dist'_T1']
      have := (top_left_eq i n).mp quad.symm
      rw [show n + 1 - hilbert_length i = (n - hilbert_length i) + 1 by omega]
      exact ih (n - hilbert_length i)
    · rw [dist'_T2']
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
    rw [dist'_T3' _ _ _ h_small.1 h_small.2 h'_small.1 h'_small.2]
    exact ih (n - 3*hilbert_length i)


lemma get_quadrant'_T0' (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T0' mn) = Quadrant.BOTTOM_LEFT := by
  simp only [get_quadrant', T0']
  have : 2^i - 1 < 2^i := by simp
  rw [if_pos, if_pos]
  · apply lt_of_le_of_lt h.1 this
  apply lt_of_le_of_lt h.2 this

lemma get_quadrant'_T1' (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T1' i mn) = Quadrant.TOP_LEFT := by
  simp only [get_quadrant', T1']
  have : 2^i - 1 < 2^i := by simp
  rw [if_pos, if_neg]
  · simp
  apply lt_of_le_of_lt h.1 this

lemma get_quadrant'_T2' (i : ℕ) (mn : ℕ × ℕ) :
  get_quadrant' i (T2' i mn) = Quadrant.TOP_RIGHT := by
  simp only [get_quadrant']
  rw [if_neg, if_neg]
  · simp [T2']
  simp [T2']

lemma get_quadrant'_T3' (i : ℕ) (mn : ℕ × ℕ) (h : mn ≤ (2^i - 1, 2^i - 1)) :
  get_quadrant' i (T3' i mn) = Quadrant.BOTTOM_RIGHT := by
  simp only [get_quadrant']
  rw [if_neg, if_pos]
  · suffices (T3' i mn : ℤ × ℤ).2 < 2^i by
      zify
      exact this
    rw [<- T3_cast i _ h.1 (le_trans h.2 (by omega))]
    simp [T3]
    omega
  suffices 2^i ≤ (T3' i mn : ℤ × ℤ).1 by
    zify
    simp [this]
  rw [<- T3_cast i _ h.1 (le_trans h.2 (by omega))]
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
  · apply get_quadrant'_T0'
    exact hilbert_curve_size i n
  · apply get_quadrant'_T1'
    exact hilbert_curve_size i _
  · apply get_quadrant'_T2'
  apply get_quadrant'_T3'
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
    · simp [T0']
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
    have := hilbert_inverse_size i (T1'_inv i mn)
    constructor
    · linarith
    linarith
  · simp [<-q_def]
    have := hilbert_inverse_size i (T2'_inv i mn)
    rw [top_right_eq]
    constructor
    · linarith
    linarith
  simp [<-q_def]
  have := hilbert_inverse_size i (T3'_inv i mn)
  rw [bottom_right_eq]
  linarith

/--
A hilbert curve is injective on its length
-/
example (i : ℕ) (n : ℕ) (h : n < hilbert_length i) :
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
    · simp  [T0'_involutive]
      apply ih
      exact (bottom_left_eq i n).mp (Eq.symm q_def)
    · simp only
      rw [T1'_inv_of_T1']
      have := (top_left_eq i n).mp (Eq.symm q_def)
      rw [ih (n - hilbert_length i)]
      · omega
      omega
    · simp only
      rw [T2'_inv_of_T2']
      have := (top_right_eq i n).mp (Eq.symm q_def)
      rw [ih (n - 2*hilbert_length i)]
      · omega
      omega
    simp only
    have size := hilbert_curve_size i (n - 3 * hilbert_length i)
    rw [T3'_inv_of_T3']
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
example (i : ℕ) (mn : ℕ × ℕ) (h : mn.1 < 2^i) (h' : mn.2 < 2^i) :
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
      rw [ih, T0'_involutive]
      · rw [T0']; exact this.2
      rw [T0']; exact this.1
    · have := (top_left_quad i mn).mp q_def.symm
      zify; rw [<-T1_cast]
      rw [ih]
      · rw [<-T1_inv_cast, T1_of_T1_inv]
        exact this.1
      · simp [T1'_inv, this.2]
      simp [T1'_inv]
      omega
    · have := (top_right_quad i mn).mp q_def.symm
      rw [ih]
      · zify; rw [<-T2_cast, <-T2_inv_cast, T2_of_T2_inv]
        exact this
      · simp [T2'_inv]; omega
      simp [T2'_inv]; omega
    have := (bottom_right_quad i mn).mp q_def.symm
    rw [ih]
    · zify
      rw [<-T3_cast, <-T3_inv_cast, T3_of_T3_inv]
      · omega
      · omega
      · simp [T3'_inv]
      simp [T3'_inv]
    · simp [T3'_inv]
      omega
    simp [T3'_inv]; omega

/--
  Create an SVG visualization of two Hilbert curves of different orders.
-/
def hilbert_curve_with_points (i : ℕ) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  -- Generate points at each coordinate
  let pointElements := (List.range total_points).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale * 2 - 1, y.toFloat / scale * 2 - 1)
    circle p (.abs 0.03) |>.setStroke (0.,0.,0.) (.px 1) |>.setFill (1.,0.,0.) |>.setId s!"point{j}")

  { elements := (lineElements ++ pointElements).toArray }

-- Example: Display a Hilbert curve of order 2 with points
#html (hilbert_curve_with_points 2).toHtml

def compare_hilbert_curves (i j : ℕ) : Svg frame :=
  let total_points_i := hilbert_length i
  let total_points_j := hilbert_length j
  let scale_i := (2^i : Nat).toFloat
  let scale_j := (2^j : Nat).toFloat

  -- Generate line segments for the first curve (red)
  let lineElements_i := (List.range (total_points_i - 1)).map (fun k =>
    let (x1, y1) := hilbert_curve i k
    let (x2, y2) := hilbert_curve i (k+1)
    let p1 := (x1.toFloat / scale_i * 2 - 1, y1.toFloat / scale_i * 2 - 1)
    let p2 := (x2.toFloat / scale_i * 2 - 1, y2.toFloat / scale_i * 2 - 1)
    line p1 p2 |>.setStroke (1., 0., 0.) (.px 4))

  -- Generate line segments for the second curve (blue)
  let lineElements_j := (List.range (total_points_j - 1)).map (fun k =>
    let (x1, y1) := hilbert_curve j k
    let (x2, y2) := hilbert_curve j (k+1)
    let p1 := (x1.toFloat / scale_j * 2 - 1, y1.toFloat / scale_j * 2 - 1)
    let p2 := (x2.toFloat / scale_j * 2 - 1, y2.toFloat / scale_j * 2 - 1)
    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  -- Generate points at each coordinate
  let pointElements_i := (List.range total_points_i).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_i * 2 - 1, y.toFloat / scale_i * 2 - 1)
    circle p (.abs 0.05) |>.setStroke (0.,0.,0.) (.px 2) |>.setFill (1.,0.,0.) |>.setId s!"point{j}")

  -- Generate points at each coordinate
  let pointElements_j := (List.range total_points_j).map (fun k =>
    let (x, y) := hilbert_curve j k
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_j * 2 - 1, y.toFloat / scale_j * 2 - 1)
    circle p (.abs 0.02) |>.setStroke (0.,0.,0.) (.px 1) |>.setFill (0.,1.,0.) |>.setId s!"point{k}")


  { elements := (lineElements_i ++ lineElements_j ++ pointElements_i ++ pointElements_j).toArray }

-- Example: Compare Hilbert curves of order 2 and 3
#html (compare_hilbert_curves 2 3).toHtml

--rw [show b - c + d = b + d - c by rw [tsub_add_tsub_comm]]

/-
Each iteration subdivides each square
-/
example (i n : ℕ) :
  2 * hilbert_curve i (n/4) ≤ hilbert_curve (i+1) n ∧
  hilbert_curve (i+1) n ≤ 2 * hilbert_curve i (n/4) + 1 := by
  induction i generalizing n with
  | zero =>
    simp [hilbert_curve]
    split
    <;> simp [T0', T1', T2', T3', Prod.le_def]
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
      rw [T0', two_swap, swap_one, Prod.swap_le_swap, Prod.swap_le_swap]
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

instance : Coe (ℤ × ℤ) (ℝ × ℝ) where
  coe := fun p => (p.1, p.2)

@[simp, norm_cast]
lemma RtimesR.cast_eq (mn mn' : ℤ × ℤ) : (mn : ℝ × ℝ) = mn' ↔ mn = mn' := by
  simp [Prod.ext_iff]

@[simp, norm_cast]
lemma RtimesR.cast_le (mn mn' : ℤ × ℤ) : (mn : ℝ × ℝ) ≤ mn' ↔  mn ≤ mn' := by
  simp only [Prod.le_def, Int.cast_le]

instance : Coe (ℕ × ℕ) (ℝ × ℝ) where
  coe := fun p => (p.1, p.2)

@[simp, norm_cast]
lemma RtimesR.cast_le_ofNat (mn mn' : ℕ × ℕ) : (mn : ℝ × ℝ) ≤ mn' ↔  mn ≤ mn' := by
  simp only [Int.cast_natCast, Prod.le_def, Nat.cast_le]

@[simp, norm_cast]
lemma RtimesR.cast_eq_ofNat (mn mn' : ℕ × ℕ) : (mn : ℝ × ℝ) = mn' ↔  mn = mn' := by
  simp only [Int.cast_natCast, Prod.ext_iff, Nat.cast_inj]

noncomputable def interpolate_points (f : ℤ → ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  let n := ⌊t⌋
  (AffineMap.lineMap (f n) (f (n+1))) (t - ⌊t⌋)

lemma interpolate_interpolates (f : ℤ → ℝ × ℝ) (i : ℤ) :
  f i = interpolate_points f i := by
  simp [interpolate_points]

lemma interpolate_interpolates_zero (f : ℤ → ℝ × ℝ) :
  f 0 = interpolate_points f 0 := by
  rw [show (0 : ℝ) = (0 : ℤ) by norm_cast]
  exact interpolate_interpolates f 0

lemma interpolate_interpolates_one (f : ℤ → ℝ × ℝ) :
  f 1 = interpolate_points f 1 := by
  rw [show (1 : ℝ) = (1 : ℤ) by norm_cast]
  exact interpolate_interpolates f 1


lemma interpolate_add (i : ℤ) (f : ℤ → ℝ × ℝ) (t : ℝ) :
  (interpolate_points f) (t + i)
  = (interpolate_points (f ∘ (fun x ↦ x + i))) t := by
  simp [interpolate_points]
  rw [show ⌊t⌋ + i + 1 = ⌊t⌋ + 1 + i by group]

lemma interpolate_add' (i : ℤ) (f : ℤ → ℝ × ℝ) :
  (interpolate_points f) ∘  (fun x ↦ x + i)
  = (interpolate_points (f ∘ (fun x ↦ x + i))) := by
  funext t; exact interpolate_add i f t

/-
Interpolate maps to a segment on each [i, i+1]
-/
lemma interpolate_section (i : ℤ) (f : ℤ → ℝ × ℝ) :
  interpolate_points f '' (Set.Icc i (i+1 : ℤ)) = segment ℝ ((interpolate_points f) i) (( interpolate_points f) (i+1 : ℤ)) := by
  -- Segments are lineMaps from [0, 1]
  rw [segment_eq_image_lineMap]
  rw [<-interpolate_interpolates, <-interpolate_interpolates]
  -- The [1] case is quite simple
  suffices interpolate_points f '' (Set.Ico (i : ℝ) ((i+1) : ℤ)) =
    (AffineMap.lineMap (f i) (f (i + 1))) '' (Set.Ico (0 : ℝ) 1) by
    rw [<-Set.Ico_union_right, <-Set.Ico_union_right]
    · rw [Set.image_union, Set.image_union]
      rw [<-this]
      · simp only [Set.image_singleton, Set.union_singleton, interpolate_interpolates,
        AffineMap.lineMap_apply_one]
    · norm_num
    norm_cast
    exact Int.le.intro 1 rfl
  -- The zero case
  have : Set.Ico (i : ℝ) (i+1 : ℤ) = (fun (x : ℝ) => x + i) '' (Set.Ico (0 : ℝ) 1) := by
    simp only [Int.cast_add, Int.cast_one, Set.image_add_right, Set.preimage_add_const_Ico,
      sub_neg_eq_add, zero_add]
    rw [add_comm]
  rw [this]
  rw [Set.image_image]
  apply Set.image_congr
  intro t th
  rw [interpolate_add i f, interpolate_points]
  have : ⌊t⌋ = 0 := by
    exact Int.floor_eq_zero_iff.mpr th
  simp [this]
  rw [add_comm]

lemma icc_accumulate (α : Type) [r : Semiring α] [CharZero α] [LinearOrder α] [IsOrderedRing α]  (n : ℕ) (h : 1 ≤ n) :
  Set.Icc (0 : α) n = Set.Accumulate (fun (i : ℕ) ↦ Set.Icc (i : α) (i+1)) (n-1 : ℕ) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    have : Set.Icc (0 : α) (n+1 : ℕ) = Set.Icc (0 : α) n ∪ Set.Icc n (n+1) := by
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_nonneg, le_add_iff_nonneg_right, zero_le_one,
        Set.Icc_union_Icc_eq_Icc, zero_le_one']
      rw [Set.Icc_union_Icc_eq_Icc]
      · apply le_trans zero_le_one
        norm_cast
      nth_rw 1 [<- add_zero (n : α)]
      apply add_le_add_left zero_le_one
    rw [show n + 1 - 1 = (n - 1) + 1 by omega]
    rw [Set.accumulate_succ]
    rw [<-ih]
    rw [Nat.sub_add_cancel h]
    exact this

lemma icc_accumulate' (n : ℕ) (h : 1 ≤ n) :
  Set.Icc 0 n = Set.Accumulate (fun i ↦ Set.Icc i (i+1)) (n-1 : ℕ) := by
  apply icc_accumulate ℕ n h


lemma image_accumulate (α β γ : Type) [LE α] (s : α → Set β) (x : α) (f : β → γ) :
  f '' (Set.Accumulate s x) = (Set.Accumulate ((fun x ↦ f '' x) ∘ s) x) := by
  unfold Set.Accumulate
  simp [Set.image_eq_iUnion]


lemma interpolate_preserves_monotonic (f : ℤ → ℝ × ℝ) (a b : ℤ) (s : Set (ℝ × ℝ)) :
  Set.MapsTo f (Set.Icc a b) s →
  Set.MapsTo (interpolate_points f) (Set.Icc a b)
  (convexHull ℝ (s : Set (ℝ × ℝ))) := by
  have : b < a ∨ b = a ∨ a < b := by
    rw [<-or_assoc, ← le_iff_lt_or_eq, or_comm]
    apply lt_or_le
  rcases this with h | h | h
  · have : Set.Icc (a : ℝ) b = ∅ := by
      simp only [not_le] at h
      rify at h
      exact Set.Icc_eq_empty_of_lt h
    rw [this]
    simp [Set.MapsTo]
  · rw [h]
    simp only [Set.Icc_self, Set.mapsTo_singleton]
    rw [<-interpolate_interpolates]
    apply subset_convexHull
  rw [
    show Set.Icc a b = (fun i ↦ (i + a)) '' Set.Icc 0 (b - a) by simp,
    show Set.Icc (a : ℝ) b = (fun (i : ℝ) ↦ (i + a)) '' Set.Icc (0 : ℝ) (b - a) by simp
    ]
  rw [<-Int.cast_sub, Set.mapsTo_image_iff, Set.mapsTo_image_iff]
  rw [interpolate_add' a f]
  set l := (b - a).toNat with l_def
  rw [show b - a = l by simp [l_def, le_of_lt h],
    show (l : ℤ) = (l : ℝ) by norm_cast]
  have lgood : 1 ≤ l := by zify; simp [l_def]; linarith
  rw [icc_accumulate (α := ℤ) (h := lgood)]
  rw [icc_accumulate (α := ℝ) (h := lgood)]
  simp only [Set.accumulate_def, Set.mapsTo_iUnion]
  intro h i ih
  rw [Set.mapsTo',
   show (i : ℝ) = (i : ℤ) by norm_cast,
   show ((i : ℤ) + 1 : ℝ) = (i + 1 : ℤ) by norm_cast,
    interpolate_section i]
  apply segment_subset_convexHull <;> {
    rw [<-interpolate_interpolates]
    apply h i ih
    simp
  }

lemma lineMap_reverse (t : ℝ) :
  (AffineMap.lineMap 1 0) (1 - t) = t := by
  simp [AffineMap.lineMap]

lemma interpolate_neg (f : ℤ → ℝ × ℝ) (t : ℝ) :
  (interpolate_points (f ∘ Neg.neg)) t = (interpolate_points f) (-t) := by
  have : (∃ (z : ℤ), t = z) ∨ Int.fract t ≠ 0 := by
    simp [Int.fract_eq_iff, -not_exists]
    apply or_not (p := ∃(z: ℤ), t = z)
  rcases this with ⟨i, h⟩ | h
  · rw [h, <-Int.cast_neg, <-interpolate_interpolates]
    rw [<-interpolate_interpolates]
    simp
  simp [interpolate_points]
  nth_rw 2 [AffineMap.lineMap_symm]
  rw [Int.fract_neg h]
  rw [AffineMap.comp_apply, lineMap_reverse]
  congr
  · suffices -⌊t⌋ = ⌊-t⌋ + (1 : ℝ) by
      exact_mod_cast this
    simp [Int.floor_neg, Int.ceil_eq_add_one_sub_fract h]
    ring_nf
    simp
  suffices (-1 : ℝ) + -⌊t⌋ = ⌊-t⌋ by
    exact_mod_cast this
  simp [Int.floor_neg, Int.ceil_eq_add_one_sub_fract h]
  ring_nf
  simp
  ring_nf

lemma neg_to_normal_eq_univ {α : Type} [Ring α] [LinearOrder α]
  [IsOrderedRing α] [Archimedean α] :
  ⋃ (a : ℕ), Set.Icc (-a : α) a = Set.univ := by
  rw [Set.iUnion_eq_univ_iff]
  simp
  simp_rw [<-abs_le (G := α)]
  intro x;
  apply exists_nat_ge

lemma interpolate_preserves (f : ℤ → ℝ × ℝ)  (s : Set (ℝ × ℝ)) :
   Set.MapsTo f Set.univ s →
   Set.MapsTo (interpolate_points f) Set.univ (convexHull ℝ s) := by
  rw [<-neg_to_normal_eq_univ, <-neg_to_normal_eq_univ]
  rw [Set.mapsTo_iUnion, Set.mapsTo_iUnion]
  intro h i
  exact_mod_cast interpolate_preserves_monotonic f (-i) i s (h i)


lemma interpolate_map (f : ℤ → ℝ × ℝ) (g : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ) :
  (interpolate_points (g ∘ f)) = g ∘ interpolate_points f := by
  funext t
  simp [interpolate_points, AffineMap.apply_lineMap]

lemma interpolate_map' (f : ℤ → ℝ × ℝ) (g : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) :
  (interpolate_points (g ∘ f)) = g ∘ interpolate_points f := by
  apply interpolate_map (g := g.toAffineMap)

-- Interpolate is continuous

/-
#check (inferInstance : Repr ℝ)
unsafe def test (x : ℝ) := x.cauchy

#eval (1 : ℝ).cauchy
-/


-- How would do something like extend the cantorset -> [0, 1] to [0, 1] -> [0, 1]

noncomputable def scale_map (s : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun := fun p => s • p
  map_add' := by simp [smul_add]
  map_smul' a b := by rw [smul_comm, RingHom.id_apply]

noncomputable def normalized_hilbert_curve (i : ℕ) :=
  interpolate_points (
    (scale_map (2^i)⁻¹) ∘ (↑) ∘ hilbert_curve i ∘ (fun x ↦ x.toNat)
  ) ∘ (fun t ↦ t * hilbert_length i)

example (i : ℕ) : normalized_hilbert_curve i 0 = (0, 0) := by
  simp [normalized_hilbert_curve]
  rw [<-interpolate_interpolates_zero]
  simp [hilbert_curve_start]

example (i : ℕ) : normalized_hilbert_curve i ((hilbert_length i - 1)/hilbert_length i) = (1 - 1/2^i, 0) := by
  rw [normalized_hilbert_curve]
  simp
  rw [div_mul_cancel₀ _ (by norm_cast; linarith [hilbert_length_pos i])]
  rw [show (hilbert_length i - 1 : ℝ) = (hilbert_length i - 1 : ℤ) by norm_cast]
  rw [<-interpolate_interpolates]
  dsimp
  simp [hilbert_curve_end, scale_map]
  ring_nf; simp; ring

lemma scale_map_inv (s : ℝ) (hs : s ≠ 0) : (scale_map s⁻¹) ∘ₗ (scale_map s) = LinearMap.id := by
  simp [scale_map, LinearMap.comp]
  congr
  funext x
  simp [hs]

lemma scale_map_inv' (s : ℝ) (hs : s ≠ 0) : (scale_map s) ∘ₗ (scale_map s⁻¹) = LinearMap.id := by
  simp [scale_map, LinearMap.comp]
  congr
  funext x
  simp [hs]


lemma scale_map_preimage (a b : ℝ × ℝ) (s : ℝ) (h : 0 < s) :
  (scale_map s⁻¹)⁻¹' Set.Icc a b = Set.Icc (scale_map s a) (scale_map s b) := by
  apply subset_antisymm
  · rw [<-Set.image_eq_preimage_of_inverse (f := scale_map s)]
    · rw [<-Set.mapsTo']
      intro x xs
      unfold scale_map
      simp at ⊢ xs
      constructor
      . apply smul_le_smul_of_nonneg_left xs.1 (le_of_lt h)
      apply smul_le_smul_of_nonneg_left xs.2 (le_of_lt h)
    · have := scale_map_inv s (Ne.symm (ne_of_lt h))
      rw [Function.LeftInverse]
      intro x; rw [<-LinearMap.comp_apply, this]
      simp only [LinearMap.id_coe, id_eq]
    have := scale_map_inv' s (Ne.symm (ne_of_lt h))
    rw [Function.RightInverse]
    intro x; rw [<-LinearMap.comp_apply, this]
    simp only [LinearMap.id_coe, id_eq]
  rw [<-Set.image_subset_iff, <-Set.mapsTo']
  intro x xs
  simp [scale_map] at ⊢ xs
  constructor
  · rw [le_inv_smul_iff_of_pos h]
    exact xs.1
  rw [inv_smul_le_iff_of_pos h]
  exact xs.2


lemma hilbert_interpolant_range (i : ℕ)  :
  Set.range (normalized_hilbert_curve (i : ℕ)) ⊆ Set.Icc (0, 0) (1, 1) := by
  unfold normalized_hilbert_curve
  set scale_t := fun t ↦ t * (hilbert_length i : ℝ) with scale_def
  rw [Set.range_comp (f := scale_t)]
  have : Set.range scale_t = Set.univ := by
    rw [Set.range_eq_univ]
    intro x
    use x / (hilbert_length i)
    simp only [scale_def]
    rw [div_mul_cancel₀]
    norm_cast
    linarith [hilbert_length_pos i]
  rw [this]
  rw [interpolate_map' (g := (scale_map (2^i)⁻¹))]
  rw [Set.image_comp, Set.image_subset_iff]
  rw [Set.image_subset_iff]
  have preimage_eq : (scale_map (2 ^ i)⁻¹)⁻¹' (Set.Icc (0, 0) (1, 1)) = Set.Icc (0, 0) (2^i, 2^i) := by
    rw [scale_map_preimage (h := by positivity)]
    rw [scale_map]
    dsimp
    rw [show (2^i : ℝ) • (0 : ℝ × ℝ) = (0,0) by simp]
    rw [show (2^i : ℝ) • (1: ℝ × ℝ) = (2^i,2^i) by simp [Prod.smul_def]]
    simp
  rw [preimage_eq, <-Set.image_subset_iff]
  have : Convex ℝ (Set.Icc ((0 : ℝ), (0 : ℝ)) (2^i, 2^i)) := by
    apply convex_Icc
  rw [<-convexHull_eq_self.mpr this, <-Set.mapsTo']
  apply interpolate_preserves
  simp only [Int.cast_natCast, Prod.mk_zero_zero, Set.mapsTo_univ_iff, Function.comp_apply,
    Set.mem_Icc]
  intro n
  rw [show (0 : ℝ × ℝ) = (0,0) by rfl]
  constructor
  · simp [Prod.le_def]
  rw [show (2^i : ℝ) = (2^i : ℕ) by norm_cast]
  apply (RtimesR.cast_le_ofNat _ (2^i, 2^i)).mpr
  apply le_trans (hilbert_curve_size _ _)
  simp


/-
Embedding into the reals + iteration defines a contracting map.
-/

/-
Embedding into the reals + iteration converges to a function.
-/

/-
The limit touches every point in [0,1]×[0,1]
-/

/-
The limit is continuous.
-/

/-
The limit is not injective.
-/
