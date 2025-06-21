import HilbertCurve.HilbertCurveNat
import Mathlib.Data.Real.Basic -- Added import
import Mathlib.Algebra.Order.Archimedean.Basic
import HilbertCurve.LinearInterpolation

/--
scale is smul as a LinearMap
-/
@[reducible]
noncomputable def scale (s : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun x => s • x
    map_add' := by simp
    map_smul' := by simp; ring_nf; simp
  }

lemma scale_def (s : ℝ) : ⇑(scale s) = (fun x => s • x) := by
  simp

lemma scale_toLinear (s : ℝ) :
  ⇑(scale s) = (scale s : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
  simp

/--
An iteration of the Hilbert curve as ℝ → ℝ × ℝ interpolated
and scaled to [0, 1] × [0, 1].
-/
noncomputable def normalized_hilbert_curve (i : ℕ) :=
  interpolate_points (
    scale ((2 : ℝ)^i)⁻¹ ∘ (↑) ∘ hilbert_curve i ∘ (fun x ↦ x.toNat)
  ) ∘ (fun t ↦ t * hilbert_length i)

/--
Every iteration of the hilbert curve starts at 0 when t = 0.
-/
lemma normal_hilbert_start (i : ℕ) : normalized_hilbert_curve i 0 = (0, 0) := by
  simp [normalized_hilbert_curve]
  rw [<-interpolate_interpolates_zero]
  simp [hilbert_curve_start]

/--
Every iteration of the hilbert curve ends at (1, 0) when t = 1.
-/
lemma normal_hilbert_end (i : ℕ) : normalized_hilbert_curve i ((hilbert_length i - 1)/hilbert_length i) = (1 - 1/2^i, 0) := by
  rw [normalized_hilbert_curve, scale_def]
  simp only [Function.comp_apply, one_div]
  rw [div_mul_cancel₀ _ (by norm_cast; linarith [hilbert_length_pos i])]
  rw [show (hilbert_length i - 1 : ℝ) = (hilbert_length i - 1 : ℤ) by norm_cast]
  rw [<-interpolate_interpolates]
  dsimp
  simp [hilbert_curve_end]
  ring_nf; simp; ring

/-
lemma scale_map_inv (s : ℝ) (hs : s ≠ 0) : (s⁻¹ • ·) ∘ₗ (s • ·) = LinearMap.id := by
  simp [scale_map, LinearMap.comp]
  congr
  funext x
  simp [hs]

lemma scale_map_inv' (s : ℝ) (hs : s ≠ 0) : (scale_map s) ∘ₗ (scale_map s⁻¹) = LinearMap.id := by
  simp [scale_map, LinearMap.comp]
  congr
  funext x
  simp [hs]
-/

lemma smul_inv_preimage_Icc (a b : ℝ × ℝ) (s : ℝ) (h : 0 < s) :
  (s⁻¹ • ·)⁻¹' Set.Icc a b = Set.Icc (s • a) (s • b) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc]
  rw (occs := .pos [3, 4]) [show x = s • s⁻¹ • x by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h), one_smul]
  ]
  rw [smul_le_smul_iff_of_pos_left h]
  rw [smul_le_smul_iff_of_pos_left h]


/--
Each real Hilbert iteration lives in [0, 1] × [0, 1].
-/
lemma hilbert_interpolant_range (i : ℕ)  :
  Set.range (normalized_hilbert_curve (i : ℕ)) ⊆ Set.Icc (0, 0) (1, 1) := by
  unfold normalized_hilbert_curve
  set scale_t := fun t ↦ t * (hilbert_length i : ℝ) with scalet_def
  rw [Set.range_comp (f := scale_t)]
  have : Set.range scale_t = Set.univ := by
    rw [Set.range_eq_univ]
    intro x
    use x / (hilbert_length i)
    simp only [scalet_def]
    rw [div_mul_cancel₀]
    norm_cast
    linarith [hilbert_length_pos i]
  rw [this]
  rw [scale_toLinear]
  rw [interpolate_map' (g := (scale (2^i)⁻¹))]
  have preimage_eq : (scale (2 ^ i)⁻¹ : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)⁻¹' (Set.Icc (0, 0) (1, 1)) = Set.Icc (0, 0) (2^i, 2^i) := by
    rw [<-scale_toLinear, scale_def]
    rw [smul_inv_preimage_Icc (h := by positivity)]
    rw [show (2^i : ℝ) • ((0, 0) : ℝ × ℝ) = (0,0) by simp]
    rw [show (2^i : ℝ) • ((1 , 1) : ℝ × ℝ) = (2^i,2^i) by simp [Prod.smul_def]]
  rw [Set.image_comp, Set.image_subset_iff]
  rw [preimage_eq]
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

lemma dist_smul_nonneg (r : ℝ) (x y : ℝ × ℝ) (h : r ≥ 0):
  dist (r • x) (r • y) =
  r * dist x y := by
  rw [@dist_smul₀, Real.norm_eq_abs, abs_of_nonneg h]

lemma div_mul_hilbert_length (i : ℕ) :
  ∀n, (n : ℝ) / hilbert_length i * hilbert_length i = n := by
  intro n
  rw [div_mul_cancel₀]
  norm_cast
  linarith [hilbert_length_pos i]

/--
The real hilbert curve of n/L_i is the (1 / 2^i) of natural number
version when n is an integer.
-/
lemma normal_hilbert_of_int (i : ℕ) (n : ℤ) :
  (normalized_hilbert_curve i (n / hilbert_length i))
    = ((2 : ℝ)^i)⁻¹ • (hilbert_curve i n.toNat) := by
  unfold normalized_hilbert_curve
  dsimp
  rw [div_mul_hilbert_length, <-interpolate_interpolates]
  simp

/--
The real hilbert curve of n/L_i is the (1 / 2^i) of natural number
version when n is a natural number.
-/
lemma normal_hilbert_of_nat (i : ℕ) (n : ℕ) :
  (normalized_hilbert_curve i (n / hilbert_length i))
    = ((2 : ℝ)^i)⁻¹ • (hilbert_curve i n) := by
  unfold normalized_hilbert_curve
  dsimp
  rw [show (n : ℝ) = (n : ℤ) by rfl]
  rw [div_mul_hilbert_length, <-interpolate_interpolates]
  simp

/--
The real hilbert curve's linear segments are all 1/2^i long.
-/
lemma normal_hilbert_diff (i n : ℕ) :
  dist (normalized_hilbert_curve i (n / hilbert_length i))
    (normalized_hilbert_curve i ((n+1) / hilbert_length i)) ≤
  (2^i)⁻¹ := by
  rw [show (n + 1 : ℝ) = (n + 1 : ℕ) by norm_cast]
  rw [normal_hilbert_of_nat, normal_hilbert_of_nat]
  rw [dist_smul_nonneg (h := by positivity)]
  apply mul_le_of_le_one_right (ha := by positivity)
  change dist (hilbert_curve i n : ℤ × ℤ) (hilbert_curve i (n+1)) ≤ 1
  rw [dist_comm]
  rw [<-dist'_cast]
  norm_cast
  apply hilbert_diff

/--
For t ≤ 0, the real hilbert curve is still 0.
-/
lemma normalized_hilbert_curve_nonpos (i : ℕ) (t : ℝ) (h : t ≤ 0) :
  normalized_hilbert_curve i t = normalized_hilbert_curve i 0 := by
  by_cases h' : t = 0
  · rw [h']
  have h'' : t < 0 := by apply lt_of_le_of_ne h h'
  unfold normalized_hilbert_curve
  dsimp
  simp only [zero_mul]
  rw [show (0 : ℝ) = (0 : ℤ) by norm_cast]
  -- The right hand side is exactly hilbert_curve at 0
  rw [<-interpolate_interpolates]
  -- The left hand side interpolates from floor to floor + 1
  rw [interpolate_points]
  -- toNat of the floor is 0
  have : ⌊t * (hilbert_length i)⌋.toNat = 0 := by
    apply Int.toNat_of_nonpos
    rify
    apply le_trans (Int.floor_le (t * hilbert_length i))
    apply mul_nonpos_of_nonpos_of_nonneg h
      (by exact_mod_cast le_of_lt (hilbert_length_pos i))
  dsimp
  rw [this]
  -- toNat of the floor + 1 is 0
  have : (⌊t * (hilbert_length i)⌋ + 1).toNat = 0 := by
    apply Int.toNat_of_nonpos
    suffices ⌊t * hilbert_length i⌋ ≤ -1 by
      linarith
    rw [Int.floor_le_iff]
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_add_cancel]
    apply mul_neg_of_neg_of_pos h'' (by exact_mod_cast hilbert_length_pos i)
  rw [this]
  simp only [AffineMap.lineMap_same, AffineMap.const_apply]

/--
Each iteration of the real Hilbert curve marches between points 1/2^i apart.
-/
lemma normal_hilbert_diff' (i : ℕ) (n : ℤ) :
  dist (normalized_hilbert_curve i (n / hilbert_length i))
    (normalized_hilbert_curve i ((n+1) / hilbert_length i)) ≤
  (2^i)⁻¹ := by
  by_cases h : n < 0
  · rw [normalized_hilbert_curve_nonpos (t := n / hilbert_length i),
      normalized_hilbert_curve_nonpos (t := (n + 1) / hilbert_length i)]
    rotate_left
    · rw [div_nonpos_iff]
      right
      constructor
      · norm_cast
      exact_mod_cast le_of_lt (hilbert_length_pos i)
    · rw [div_nonpos_iff]
      right
      constructor
      · norm_cast; exact le_of_lt h
      exact_mod_cast le_of_lt (hilbert_length_pos i)
    simp
  rw [show n = n.toNat from Eq.symm (Int.toNat_of_nonneg (by linarith [h]))]
  apply normal_hilbert_diff

/--
Each point on a real Hilbert curve iteration is close to an interpolated point.
-/
lemma normal_hilbert_dist (i : ℕ) (t : ℝ) :
  dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve i (⌊t * hilbert_length i⌋ / hilbert_length i)) ≤
  (2^i)⁻¹ := by
  unfold normalized_hilbert_curve
  dsimp
  rw [div_mul_hilbert_length]
  apply le_trans (interpolate_distance _ (t * hilbert_length i))
  suffices dist (normalized_hilbert_curve i (⌊t * hilbert_length i⌋ / hilbert_length i))
    (normalized_hilbert_curve i ((⌊t * hilbert_length i⌋ + 1 : ℤ) / hilbert_length i)) ≤ (2^i)⁻¹ by
    unfold normalized_hilbert_curve at this
    dsimp at this
    rw [div_mul_hilbert_length, div_mul_hilbert_length] at this
    rw [<-interpolate_interpolates, <-interpolate_interpolates] at this
    exact this
  rw [show (⌊t * hilbert_length i⌋ + 1 : ℤ) = ⌊t * hilbert_length i⌋ + (1 : ℝ) by norm_cast]
  apply normal_hilbert_diff' i (n := ⌊t * hilbert_length i⌋)

/--
If you multiply by n, floor, then integer divide by n, then it is the same as floor.
-/
lemma div_floor_mul_eq_floor (t : ℝ) (n : ℕ) (h : 0 ≤ t) (h' : 0 < n):
  ⌊t * n⌋ / n = ⌊t⌋ := by
  set k := ⌊t*n⌋ with k_def
  -- There doesn't seem to be a way to prove this using existing
  -- floor ring lemmas, so we will use the definition of Int.floor.
  symm
  rw [Int.floor_eq_iff]
  symm at k_def
  have k_nonneg : 0 ≤ k := by positivity
  rw [Int.floor_eq_iff] at k_def
  rcases k_def with ⟨k1, k2⟩ -- k ≤ t * n, t * n < k + 1
  have n_pos : 0 < (n : ℝ) := by exact_mod_cast h'
  -- Although it _seems_ like normcast should work, there is some
  -- subtle differences between integer division and real division.
  constructor
  · show (k / n : ℤ) ≤ t
    calc
      ((k / n : ℤ) : ℝ) ≤ (k : ℝ) / n := by
        rw [le_div_iff₀ n_pos]
        suffices (k.toNat / n) * n ≤ k.toNat by
          zify at this
          rw [Int.toNat_of_nonneg] at this
          · exact_mod_cast this
          exact k_nonneg
        apply Nat.div_mul_le_self
      _ ≤ t := by
        exact (div_le_iff₀ n_pos).mpr k1
  show t < (k / n : ℤ) + 1
  calc
    t < (k + 1 : ℝ) / n := by
      rw [lt_div_iff₀]
      · exact k2
      exact_mod_cast h'
    _ ≤ (k/n : ℤ) + 1 := by
      rw [div_le_iff₀ n_pos]
      rw [show k = k.toNat by exact Int.eq_natCast_toNat.mpr k_nonneg]
      norm_cast
      change k.toNat < (k.toNat / n + 1)*n
      rw [mul_comm]
      apply Nat.lt_mul_div_succ
      exact h'

/--
Each real Hilbert curve iteration divides the previous into smaller
deviations only 1/2^(i+1) away from the previous.
-/
lemma normal_hilbert_across_dist (i n : ℕ) :
  dist (normalized_hilbert_curve i ((n/4 : ℕ) / hilbert_length i))
    (normalized_hilbert_curve (i+1) (n / hilbert_length (i+1))) ≤
  (2^(i+1))⁻¹ := by
  -- We can prove this by using subdivision_side where each Hilbert curve divides
  -- a square into pieces along n / 4 (using integer division).
  rw [normal_hilbert_of_nat]
  rw [normal_hilbert_of_nat]
  rw [show ∀x : ℝ × ℝ, ((2 : ℝ)^(i + 1))⁻¹ • x = ((2 : ℝ)^i)⁻¹ • (2 : ℝ)⁻¹ • x by
    intro x
    rw [pow_succ]
    rw [smul_smul]
    ring_nf
  ]
  rw [dist_smul_nonneg (r := (2^i)⁻¹) (h := by positivity)]
  rw [pow_succ, mul_inv]
  rw [mul_le_mul_left (by positivity)]
  suffices
    dist (2 * hilbert_curve i (n/4)) (hilbert_curve (i+1) n) ≤ 1 by
    rw [
      show hilbert_curve i (n/4) = (2 : ℝ)⁻¹ • ((2 * hilbert_curve i (n/4) : ℕ × ℕ) : ℝ × ℝ) by
      simp
    ]
    rw [dist_smul₀]
    simp
    norm_cast
  have subd := subdivision_size i n
  -- The remaaining bits are mainly annoying and obvious algebra
  -- using the definition of dist
  simp only [Prod.le_def] at subd
  rw [dist_comm]
  simp only [dist, sup_le_iff]
  constructor
  · rw [<-Nat.cast_sub subd.1.1]
    simp only [Prod.fst_mul, Prod.fst_ofNat, Nat.abs_cast, Nat.cast_le_one, tsub_le_iff_right]
    rw [add_comm 1 (2 * _)]
    exact subd.2.1
  rw [<-Nat.cast_sub subd.1.2]
  simp only [Prod.snd_mul, Prod.snd_ofNat, Nat.abs_cast, Nat.cast_le_one, tsub_le_iff_right]
  rw [add_comm 1 (2 * _)]
  exact subd.2.2

/--
The real Hilbert curve only moves 1 / 2^(i-1) each iteration for each t.
-/
lemma normal_subdivision_size (i : ℕ) (t : ℝ) :
  dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve (i+1) t) ≤ 2 * (2^i)⁻¹ := by
  -- We'll prove this by the triangle inequality between H_i(t), H_i(n / L_i),
  -- H_{i+1}(n / L_{i+1)}), and finally H_{i+1}(t). We do this instead
  -- of a more obvious subdivision lemma since the edge effects at the boundary
  -- are too annoying.
  apply le_trans (dist_triangle4 _
    (normalized_hilbert_curve i (⌊t * hilbert_length i⌋ / hilbert_length i))
    (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i + 1))))
    _)
  -- Bounding the distance between points t and n / L_i is still easy.
  have t1 : dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve i (↑⌊t * ↑(hilbert_length i)⌋ / ↑(hilbert_length i))) ≤ (2^i)⁻¹ :=
    normal_hilbert_dist i t
  have t3 : dist (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i+1))))
    (normalized_hilbert_curve (i+1) t) ≤ (2^(i+1))⁻¹ := by
    rw [dist_comm]
    exact normal_hilbert_dist (i+1) t
  have t2 : dist (normalized_hilbert_curve i (⌊t * (hilbert_length i)⌋ / (hilbert_length i)))
    (normalized_hilbert_curve (i+1) (⌊t * hilbert_length (i+1)⌋ / (hilbert_length (i+1)))) ≤ (2^(i+1))⁻¹ := by
    -- When t ≤ 0, it's a straightforward calculation.
    by_cases h : t ≤ 0
    · have : ∀n : ℕ, ⌊t * n⌋ / n ≤ (0 : ℝ) :=  by
        intro n
        apply div_nonpos_of_nonpos_of_nonneg
        · norm_cast
          apply Int.floor_nonpos
          apply mul_nonpos_of_nonpos_of_nonneg
          exact h
          simp only [Nat.cast_nonneg]
        simp only [Nat.cast_nonneg]
      rw [normalized_hilbert_curve_nonpos i _ (this (hilbert_length i))]
      rw [normalized_hilbert_curve_nonpos (i+1) _ (this (hilbert_length (i+1)))]
      rw [normal_hilbert_start, normal_hilbert_start]
      simp
    simp only [not_le] at h
    -- Now we can relate the ⌊n⌋ = ⌊4 * n⌋ / 4
    have : ⌊t * hilbert_length i⌋ = ⌊t * hilbert_length (i+1)⌋ / 4 := by
      rw [hilbert_length_succ, mul_comm 4]
      rw [Nat.cast_mul, Nat.cast_ofNat]
      rw [<-mul_assoc]
      symm
      apply div_floor_mul_eq_floor
      · positivity
      norm_num
    rw [this]
    -- We need to deal with some toNat casting to apply normal_hilbert_across_dist
    rw [show ⌊t * hilbert_length (i+1)⌋ = ⌊t * hilbert_length (i+1)⌋.toNat by
      refine Int.eq_natCast_toNat.mpr ?_
      positivity
    ]
    rw [show ⌊t * hilbert_length (i+1)⌋.toNat / (4 : ℤ) = (⌊t * hilbert_length (i+1)⌋.toNat / 4 : ℕ) by
      simp
    ]
    have : ∀n : ℕ, ((n : ℤ) : ℝ) = (n : ℝ) := by intro n; norm_cast
    rw [this, this]
    apply normal_hilbert_across_dist
  rw [show 2  * ((2 : ℝ)^i)⁻¹ = (2^i)⁻¹ + (2^(i+1))⁻¹ + (2^(i+1))⁻¹ by
    rw [pow_add]
    ring
  ]
  linarith

/--
Each real Hilbert curve is continuous.
-/
lemma normal_hilbert_curve_continuous (i : ℕ) :
  Continuous (normalized_hilbert_curve i) := by
  rw [normalized_hilbert_curve]
  set f : ℤ → ℝ × ℝ := (⇑(scale (2 ^ i)⁻¹) ∘ (fun x ↦ (↑x.1, ↑x.2)) ∘ hilbert_curve i ∘ fun x ↦ x.toNat) with f_def
  have := interpolate_is_continuous f
  apply Continuous.comp this
  apply continuous_mul_right

/--
The Hilbert curve iterations form a Cauchy sequence at each t.
-/
lemma normal_is_cauchy (t : ℝ) : CauchySeq (normalized_hilbert_curve · t) := by
  apply cauchySeq_of_le_geometric_two (C := 4)
  intro n
  rw [show 4 / 2 / (2:ℝ)^n = 2 * (2^n)⁻¹ by ring]
  apply normal_subdivision_size

/--
Each iteration also touches most points.
-/
lemma exists_normal_hilbert_approx_inv (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) :
  ∃t, t ∈ Set.Icc 0 1 ∧ dist x (normalized_hilbert_curve i t) ≤ (2^i)⁻¹ := by
  -- We need a custom rounding so we can get something from 0 to n-1.
  have : ∀n > (0 : ℕ), ∀a ∈ Set.Icc (0 : ℝ) n, ∃i ∈ Set.Ico 0 n, dist a (i : ℝ) ≤ 1 := by
    intro n nh a ah
    by_cases h : a = n
    · use (n-1)
      simp [nh, h]
    use ⌊a⌋.toNat
    have : 0 ≤ a := ah.1
    constructor
    · simp only [Set.mem_Ico, zero_le, true_and]
      zify
      rw [Int.toNat_of_nonneg (by positivity)]
      rify
      apply lt_of_le_of_lt (Int.floor_le a)
      apply lt_of_le_of_ne ah.2 h
    rw [show ∀x : ℕ, (x : ℝ) = (x : ℤ) by intro x; norm_cast]
    rw [Int.toNat_of_nonneg (by positivity)]
    simp only [dist]
    rw [abs_of_nonneg]
    · rw [sub_le_iff_le_add, add_comm]
      exact le_of_lt (Int.lt_floor_add_one a)
    rw [sub_nonneg]
    exact Int.floor_le a
  have bound : (x.1 * 2^i, x.2 * 2^i) ∈ Set.Icc 0 (2^i) := by
    simpa only [Set.mem_Icc, Prod.le_def, Prod.fst_zero, Nat.ofNat_pos, pow_pos,
      mul_nonneg_iff_of_pos_right, Prod.snd_zero, Prod.pow_fst, Prod.fst_ofNat,
      mul_le_iff_le_one_left, Prod.pow_snd, Prod.snd_ofNat] using xh
  -- We'll round x
  obtain ⟨i1, i1h, i1h'⟩ := this (2^i) (by positivity) (x.1 * 2^i) ⟨bound.1.1, by exact_mod_cast bound.2.1⟩
  obtain ⟨i2, i2h, i2h'⟩ := this (2^i) (by positivity) (x.2 * 2^i) ⟨bound.1.2, by exact_mod_cast bound.2.2⟩
  -- Now we can use the inverse of the rounded version
  set t : ℝ := (hilbert_inverse i (i1, i2)) / hilbert_length i with t_def
  use t
  constructor
  · show t ∈ Set.Icc 0 1
    rw [t_def]
    simp only [Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast (hilbert_length_pos i))]
    exact_mod_cast le_of_lt (hilbert_inverse_size i _)
  show dist x (normalized_hilbert_curve i t) ≤ (2 ^ i)⁻¹
  rw [t_def]
  rw [normal_hilbert_of_nat i]
  rw [hilbert_curve_of_inverse (h := i1h.2) (h' := i2h.2)]
  -- Now we just need so use that x is close to the rounded version
  rw [show x = ((2 : ℝ)^i)⁻¹ • (x * 2^i) by
    rw [Prod.smul_def, Prod.mul_def]
    field_simp
  ]
  rw [dist_smul_nonneg (h := by positivity), mul_le_iff_le_one_right (by positivity)]
  exact max_le i1h' i2h'

/--
Approximate inverse of normal_hilbert_curve i
-/
noncomputable def norm_hilbert_inv (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) : ℝ :=
  Classical.choose (exists_normal_hilbert_approx_inv i x xh)

/--
Approximate inverse of normal_hilbert_curve i lives in [0, 1]
-/
lemma norm_hilbert_inv_bounded (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) :
  (norm_hilbert_inv i x xh) ∈ Set.Icc 0 1 :=
  (Classical.choose_spec (exists_normal_hilbert_approx_inv i x xh)).1

/--
norm_hilbert_inv is an approximately inverse normalized_hilbert_curve
-/
lemma norm_hilbert_inv_dist (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) :
  dist x (normalized_hilbert_curve i (norm_hilbert_inv i x xh)) ≤ (2^i)⁻¹ :=
  (Classical.choose_spec (exists_normal_hilbert_approx_inv i x xh)).2
