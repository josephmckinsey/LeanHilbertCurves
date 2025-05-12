-- This module serves as the root of the `HilbertCurve` library.
-- Import modules here that should be built as part of the library.

import HilbertCurve.HilbertCurveNat
import Mathlib.Data.Real.Basic -- Added import
import Mathlib.Algebra.Order.Archimedean.Basic
import HilbertCurve.LinearInterpolation

noncomputable def scale_map (s : ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun := fun p => s • p
  map_add' := by simp [smul_add]
  map_smul' a b := by rw [smul_comm, RingHom.id_apply]

noncomputable def normalized_hilbert_curve (i : ℕ) :=
  interpolate_points (
    (scale_map (2^i)⁻¹) ∘ (↑) ∘ hilbert_curve i ∘ (fun x ↦ x.toNat)
  ) ∘ (fun t ↦ t * hilbert_length i)

lemma normal_hilbert_start (i : ℕ) : normalized_hilbert_curve i 0 = (0, 0) := by
  simp [normalized_hilbert_curve]
  rw [<-interpolate_interpolates_zero]
  simp [hilbert_curve_start]

lemma normal_hilbert_end (i : ℕ) : normalized_hilbert_curve i ((hilbert_length i - 1)/hilbert_length i) = (1 - 1/2^i, 0) := by
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

lemma scale_map_dist (r : ℝ) (x y : ℝ × ℝ) (h : r ≥ 0):
  dist ((scale_map r) x) ((scale_map r) y) =
  r * dist x y := by
  unfold scale_map
  dsimp
  rw [@dist_smul₀, Real.norm_eq_abs, abs_of_nonneg h]


lemma div_mul_hilbert_length (i : ℕ) :
  ∀n, (n : ℝ) / hilbert_length i * hilbert_length i = n := by
  intro n
  rw [div_mul_cancel₀]
  norm_cast
  linarith [hilbert_length_pos i]

lemma normal_hilbert_of_int (i : ℕ) (n : ℤ) :
  (normalized_hilbert_curve i (n / hilbert_length i))
    = scale_map (2^i)⁻¹ (hilbert_curve i n.toNat) := by
  unfold normalized_hilbert_curve
  dsimp
  rw [div_mul_hilbert_length, <-interpolate_interpolates]
  simp

lemma normal_hilbert_diff (i n : ℕ) :
  dist (normalized_hilbert_curve i (n / hilbert_length i))
    (normalized_hilbert_curve i ((n+1) / hilbert_length i)) ≤
  (2^i)⁻¹ := by
  rw [show (n : ℝ) + 1 = (n + 1 : ℤ) by norm_cast]
  rw [show (n : ℝ) = (n : ℤ) by norm_cast]
  rw [normal_hilbert_of_int, normal_hilbert_of_int]
  dsimp
  rw [scale_map_dist (h := by positivity)]
  apply mul_le_of_le_one_right (ha := by positivity)
  change dist (hilbert_curve i n : ℤ × ℤ) (hilbert_curve i (n+1)) ≤ 1
  rw [dist_comm]
  rw [<-dist'_cast]
  norm_cast
  apply hilbert_diff

lemma normalized_hilbert_curve_nonpos (i : ℕ) (t : ℝ) (h : t ≤ 0) :
  normalized_hilbert_curve i t = normalized_hilbert_curve i 0 := by
  by_cases h' : t = 0
  · rw [h']
  have h'' : t < 0 := by apply lt_of_le_of_ne h h'
  unfold normalized_hilbert_curve
  dsimp
  simp only [zero_mul]
  rw [show (0 : ℝ) = (0 : ℤ) by norm_cast]
  --rw [show ((t : ℤ) * hilbert_length i : ℝ)= (n * hilbert_length i : ℤ) by norm_cast]
  rw [<-interpolate_interpolates]--, <-interpolate_interpolates]
  rw [interpolate_points]
  have : ⌊t * (hilbert_length i)⌋.toNat = 0 := by
    apply Int.toNat_of_nonpos
    rify
    apply le_trans (Int.floor_le (t * hilbert_length i))
    apply mul_nonpos_of_nonpos_of_nonneg h
      (by exact_mod_cast le_of_lt (hilbert_length_pos i))
  dsimp
  rw [this]
  have : (⌊t * (hilbert_length i)⌋ + 1).toNat = 0 := by
    apply Int.toNat_of_nonpos
    suffices ⌊t * hilbert_length i⌋ ≤ -1 by
      linarith
    rw [Int.floor_le_iff]
    simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_add_cancel]
    apply mul_neg_of_neg_of_pos h'' (by exact_mod_cast hilbert_length_pos i)
  rw [this]
  simp


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

lemma div_floor_mul_eq_floor (t : ℝ) (n : ℕ) (h : 0 ≤ t) (h' : 0 < n):
  ⌊t * n⌋ / n = ⌊t⌋ := by
  set k := ⌊t*n⌋ with k_def
  symm
  rw [Int.floor_eq_iff]
  symm at k_def
  have k_nonneg : 0 ≤ k := by positivity
  rw [Int.floor_eq_iff] at k_def
  rcases k_def with ⟨k1, k2⟩ -- k ≤ t * n, t * n < k + 1
  have n_pos : 0 < (n : ℝ) := by exact_mod_cast h'
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
      rw [show k = k.toNat by exact Int.eq_ofNat_toNat.mpr k_nonneg]
      norm_cast
      change k.toNat < (k.toNat / n + 1)*n
      rw [mul_comm]
      apply Nat.lt_mul_div_succ
      exact h'


--lemma subdivision_size (i n : ℕ) :
  --2 * hilbert_curve i (n/4) ≤ hilbert_curve (i+1) n ∧
  --hilbert_curve (i+1) n ≤ 2 * hilbert_curve i (n/4) + 1 := by

lemma normal_hilbert_across_dist (i n : ℕ) :
  dist (normalized_hilbert_curve i ((n/4 : ℕ) / hilbert_length i))
    (normalized_hilbert_curve (i+1) (n / hilbert_length (i+1))) ≤
  (2^(i+1))⁻¹ := by
  rw [show ((n/4 : ℕ) : ℝ) = ((n/4 : ℕ): ℤ) by norm_cast]
  rw [normal_hilbert_of_int]
  rw [show (n : ℝ) = (n: ℤ) by norm_cast]
  rw [normal_hilbert_of_int]
  rw [
    show ∀x : ℝ × ℝ, scale_map (2^(i+1))⁻¹ x = scale_map (2^i)⁻¹ ((2 : ℝ)⁻¹ • x) by
    rw [scale_map, scale_map, pow_succ, mul_inv]
    intro x
    rw [mul_comm]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_smul]
    exact mul_smul 2⁻¹ (2 ^ i)⁻¹ x
  ]
  rw [scale_map_dist (r := (2^i)⁻¹) (h := by positivity)]
  rw [pow_succ, mul_inv]
  rw [mul_le_mul_left (by positivity)]
  simp only [Nat.cast_ofNat, Int.toNat_ofNat]
  have subd := subdivision_size i n
  suffices
    dist (2 * hilbert_curve i (n/4)) (hilbert_curve (i+1) n) ≤ 1 by
    rw [
      show hilbert_curve i (n/4) = (2 : ℝ)⁻¹ • ((2 * hilbert_curve i (n/4) : ℕ × ℕ) : ℝ × ℝ) by
      simp
    ]
    rw [dist_smul₀]
    simp
    norm_cast
  rw [dist_comm]
  simp only [dist, sup_le_iff]
  constructor
  · rw [<-Nat.cast_sub subd.1.1]
    simp [Prod.le_def] at subd
    simp
    rw [add_comm 1 (2 * _)]
    exact subd.2.1
  rw [<-Nat.cast_sub subd.1.2]
  simp [Prod.le_def] at subd
  simp
  rw [add_comm 1 (2 * _)]
  exact subd.2.2


lemma normal_subdivision_size (i : ℕ) (t : ℝ) :
  dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve (i+1) t) ≤ 2 * (2^i)⁻¹ := by
  apply le_trans (dist_triangle4 _
    (normalized_hilbert_curve i (⌊t * hilbert_length i⌋ / hilbert_length i))
    (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i + 1))))
    _)
  have t1 : dist (normalized_hilbert_curve i t)
    (normalized_hilbert_curve i (↑⌊t * ↑(hilbert_length i)⌋ / ↑(hilbert_length i))) ≤ (2^i)⁻¹ :=
    normal_hilbert_dist i t
  have t3 : dist (normalized_hilbert_curve (i+1) (⌊t * (hilbert_length (i+1))⌋ / (hilbert_length (i+1))))
    (normalized_hilbert_curve (i+1) t) ≤ (2^(i+1))⁻¹ := by
    rw [dist_comm]
    exact normal_hilbert_dist (i+1) t
  have t2 : dist (normalized_hilbert_curve i (⌊t * (hilbert_length i)⌋ / (hilbert_length i)))
    (normalized_hilbert_curve (i+1) (⌊t * hilbert_length (i+1)⌋ / (hilbert_length (i+1)))) ≤ (2^(i+1))⁻¹ := by
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
    have : ⌊t * hilbert_length i⌋ = ⌊t * hilbert_length (i+1)⌋ / 4 := by
      rw [hilbert_length_succ, mul_comm 4]
      rw [Nat.cast_mul, Nat.cast_ofNat]
      rw [<-mul_assoc]
      symm
      apply div_floor_mul_eq_floor
      · positivity
      norm_num
    rw [this]
    rw [show ⌊t * hilbert_length (i+1)⌋ = ⌊t * hilbert_length (i+1)⌋.toNat by
      refine Int.eq_ofNat_toNat.mpr ?_
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

lemma normal_hilbert_curve_continuous (i : ℕ) :
  Continuous (normalized_hilbert_curve i) := by
  rw [normalized_hilbert_curve]
  set f : ℤ → ℝ × ℝ := (⇑(scale_map (2 ^ i)⁻¹) ∘ (fun x ↦ (↑x.1, ↑x.2)) ∘ hilbert_curve i ∘ fun x ↦ x.toNat) with f_def
  have := interpolate_is_continuous f
  apply Continuous.comp this
  apply continuous_mul_right

/-
Embedding into the reals + iteration converges to a function.
-/

lemma normal_is_cauchy (t : ℝ) : CauchySeq (normalized_hilbert_curve · t) := by
  apply cauchySeq_of_le_geometric_two (C := 4)
  intro n
  rw [show 4 / 2 / (2:ℝ)^n = 2 * (2^n)⁻¹ by ring]
  apply normal_subdivision_size


lemma limit_hilbert_curve_exists (t : ℝ) :
  ∃x, Filter.Tendsto (normalized_hilbert_curve · t) Filter.atTop (nhds x) := by
  apply cauchySeq_tendsto_of_complete
  exact normal_is_cauchy t

noncomputable def limit_hilbert_curve (t : ℝ) : ℝ × ℝ :=
  Classical.choose (limit_hilbert_curve_exists t)

lemma limit_hilbert_curve_tendsto (t : ℝ) :
  Filter.Tendsto (normalized_hilbert_curve · t) Filter.atTop (nhds (limit_hilbert_curve t)) :=
  Classical.choose_spec (limit_hilbert_curve_exists t)

lemma eventually_geometric (ε : ℝ) (h : ε > 0): ∀ᶠ (n : ℕ) in Filter.atTop, 4/2^n < ε := by
  suffices ∀ᶠ (n : ℕ) in Filter.atTop, 4 / ε < 2^n by
    apply Filter.Eventually.mono this
    intro n nh
    rw [div_lt_iff₀ (by positivity)]
    rw [mul_comm, <-div_lt_iff₀ h]
    exact nh
  simp only [Filter.eventually_atTop, ge_iff_le]
  obtain ⟨N, Nh⟩ := pow_unbounded_of_one_lt (4/ε) (by norm_num : (1 : ℝ) < 2)
  use N
  intro M Mh
  exact lt_of_lt_of_le Nh (pow_right_mono₀ (by norm_num) Mh)

lemma limit_hilbert_curve_tendstouniformly :
  TendstoUniformly normalized_hilbert_curve limit_hilbert_curve Filter.atTop := by
  suffices ∀n t, dist (normalized_hilbert_curve n t) (limit_hilbert_curve t) ≤ 4 / 2 ^ n by
    rw [Metric.tendstoUniformly_iff]
    intro ε εpos
    have : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ t, dist (normalized_hilbert_curve n t) (limit_hilbert_curve t) ≤ 4 / 2^n := by
      apply Filter.Eventually.of_forall
      exact this
    have := Filter.Eventually.and (eventually_geometric ε εpos) this
    apply Filter.Eventually.mono this
    intro n ⟨h1, h2⟩
    intro t
    rw [dist_comm]
    exact lt_of_le_of_lt (h2 t) h1
  intro n t
  apply dist_le_of_le_geometric_two_of_tendsto (n := n)
  · exact limit_hilbert_curve_tendsto t
  intro n
  rw [show 4 / 2 / (2:ℝ)^n = 2 * (2^n)⁻¹ by ring]
  apply normal_subdivision_size

/-
The limit is continuous.
-/
lemma limit_hilbert_continuous : Continuous limit_hilbert_curve :=
  TendstoUniformly.continuous limit_hilbert_curve_tendstouniformly
  (Filter.Eventually.of_forall normal_hilbert_curve_continuous)

lemma norm_hilbert_inv' (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1):
  ∃t, t ∈ Set.Icc 0 1 ∧ dist x (normalized_hilbert_curve i t) ≤ (2^i)⁻¹ := by
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
  obtain ⟨i1, i1h, i1h'⟩ := this (2^i) (by positivity) (x.1 * 2^i) ⟨bound.1.1, by exact_mod_cast bound.2.1⟩
  obtain ⟨i2, i2h, i2h'⟩ := this (2^i) (by positivity) (x.2 * 2^i) ⟨bound.1.2, by exact_mod_cast bound.2.2⟩
  set t : ℝ := (hilbert_inverse i (i1, i2)) / hilbert_length i with t_def
  use t
  constructor
  · rw [t_def]
    simp only [Set.mem_Icc]
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by exact_mod_cast (hilbert_length_pos i))]
    exact_mod_cast le_of_lt (hilbert_inverse_size i _)
  rw [t_def]
  rw [show
    (hilbert_inverse i (i1, i2) : ℝ) = (hilbert_inverse i (i1, i2) : ℤ) by
    norm_cast]
  rw [normal_hilbert_of_int i]
  simp only [Int.toNat_ofNat]
  rw [hilbert_curve_of_inverse (h := i1h.2) (h' := i2h.2)]
  simp [scale_map]
  rw [show x = ((2 : ℝ)^i)⁻¹ • (x * 2^i) by
    rw [Prod.smul_def, Prod.mul_def]
    field_simp
  ]
  rw [show (((2 : ℝ)^i)⁻¹ * i1, ((2 :ℝ)^i)⁻¹ * i2) = ((2 : ℝ)^i)⁻¹ • (i1, i2) by
    simp]
  rw [dist_smul₀]
  simp only [norm_inv, norm_pow, Real.norm_ofNat, inv_pos, Nat.ofNat_pos, pow_pos,
    mul_le_iff_le_one_right]
  exact max_le i1h' i2h'

noncomputable def norm_hilbert_inv (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) : ℝ :=
  Classical.choose (norm_hilbert_inv' i x xh)

lemma norm_hilbert_inv_bounded (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) :
  (norm_hilbert_inv i x xh) ∈ Set.Icc 0 1 :=
  (Classical.choose_spec (norm_hilbert_inv' i x xh)).1

lemma norm_hilbert_inv_dist (i : ℕ) (x : ℝ × ℝ) (xh : x ∈ Set.Icc 0 1) :
  dist x (normalized_hilbert_curve i (norm_hilbert_inv i x xh)) ≤ (2^i)⁻¹ :=
  (Classical.choose_spec (norm_hilbert_inv' i x xh)).2

/-
The limit touches every point in [0,1]×[0,1]
-/
lemma limit_hilbert_surjective : Set.range limit_hilbert_curve = Set.Icc 0 1 := by
  apply subset_antisymm
  · rw [Set.range_subset_iff]
    intro t
    have limit_def := limit_hilbert_curve_tendsto t
    suffices ∀ᶠ (n : ℕ) in Filter.atTop, (normalized_hilbert_curve n t) ∈ Set.Icc 0 1 by
      have zero_one_closed := isClosed_Icc (a := (0 : ℝ × ℝ)) (b := 1)
      apply zero_one_closed.mem_of_tendsto limit_def this
    apply Filter.Eventually.of_forall
    intro n
    exact hilbert_interpolant_range _ (Set.mem_range_self t)
  intro x xy
  have : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨t, th, φ, φh, h⟩ := this.tendsto_subseq (norm_hilbert_inv_bounded (xh := xy) (x := x))
  use t
  set f := fun n ↦ norm_hilbert_inv n x xy
  have h' : Filter.Tendsto (fun i ↦ normalized_hilbert_curve (φ i) (f (φ i)))
      Filter.atTop (nhds (limit_hilbert_curve t)) :=
      TendstoUniformly.tendsto_comp
        ((tendstoUniformly_iff_seq_tendstoUniformly.mp limit_hilbert_curve_tendstouniformly) φ
          (StrictMono.tendsto_atTop φh))
        (Continuous.continuousAt limit_hilbert_continuous)
        h
  apply tendsto_nhds_unique h'
  apply (Filter.tendsto_iff_seq_tendsto (k := Filter.atTop) (
    f := fun i ↦ normalized_hilbert_curve i (f i)
  )).mp ?_ φ (StrictMono.tendsto_atTop φh)
  -- This might be a good one to split
  --have := norm_hilbert_inv_dist i x xy
  rw [tendsto_iff_dist_tendsto_zero]
  have : Filter.Tendsto (fun n => ((2 : ℝ) ^ n)⁻¹) Filter.atTop (nhds 0) := by
    rw [show (fun n ↦ ((2 : ℝ)^n)⁻¹) = fun n ↦ ((2 : ℝ)⁻¹)^n by
      simp]
    apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    rw [abs]
    norm_num
  apply squeeze_zero (fun n ↦ dist_nonneg) (g0 := this)
  intro n
  rw [dist_comm]
  exact norm_hilbert_inv_dist n x xy


noncomputable def T0_real : ℝ × ℝ →L[ℝ] ℝ × ℝ := LinearMap.toContinuousLinearMap T0
--noncomputable def T3_real : ℝ × ℝ →A[ℝ] ℝ × ℝ := AffineMap.toContinuousAffineMap T3

-- First we'll find a sequence n_i s.t. n_i / hilbert_length i tends to t
lemma floor_toNat_tends_to (t : ℝ) (h : 0 ≤ t) :
  Filter.Tendsto (fun i ↦ (⌊t * hilbert_length i⌋.toNat : ℝ) / hilbert_length i)
  Filter.atTop (nhds t) := by
  have floor_nonneg : ∀i, 0 ≤ ⌊t * hilbert_length i⌋ := by
    intro i; positivity
  have : ∀i, dist
    ((⌊t * hilbert_length i⌋.toNat : ℝ) / hilbert_length i) t ≤
    1 / hilbert_length i := by
    intro i
    rw [dist_comm]
    rw [show (⌊t * ↑(hilbert_length i)⌋.toNat : ℝ)
      = (⌊t * ↑(hilbert_length i)⌋.toNat : ℤ) by norm_cast]
    rw [Int.toNat_of_nonneg (floor_nonneg i)]
    simp only [dist]
    have : (0 : ℝ) < hilbert_length i := by
      exact_mod_cast hilbert_length_pos i
    rw [abs_of_nonneg]
    · rw [le_div_iff₀ this, sub_mul]
      rw [div_mul_cancel₀ _ (Ne.symm (ne_of_lt this))]
      rw [sub_le_iff_le_add, add_comm]
      exact le_of_lt (Int.lt_floor_add_one _)
    apply sub_nonneg_of_le
    rw [div_le_iff₀ this]
    apply Int.floor_le
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (g := fun i ↦ 1 / hilbert_length i)
    (fun t_1 ↦ dist_nonneg) this
  simp_rw [show
    (fun i => (1 : ℝ) / (hilbert_length i : ℝ)) = fun i => (1/4)^i by
    funext i
    simp [hilbert_length, pow_mul]
  ]
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  rw [abs]
  norm_num

/-
The hilbert curve is a fractal just like its construction, i.e.
it can be broken up into 4 copies of itself.
-/
lemma limit_hilbert_recurse_top_left (t : ℝ) (h : t ∈ Set.Icc 0 (1/4)) :
  limit_hilbert_curve t = T0_real (limit_hilbert_curve (4*t)) := by
  set f := fun i ↦ (⌊t * hilbert_length i⌋.toNat / hilbert_length i : ℝ)
  have f_tendsto : Filter.Tendsto f Filter.atTop (nhds t) :=
    floor_toNat_tends_to t h.1
  have lhs_tendsto : Filter.Tendsto
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i))
    Filter.atTop
    (nhds (limit_hilbert_curve t)) := by
    apply TendstoUniformly.tendsto_comp (hg := f_tendsto)
    · apply tendstoUniformly_iff_seq_tendstoUniformly.mp
        limit_hilbert_curve_tendstouniformly
      exact Filter.tendsto_add_atTop_nat 1
    exact limit_hilbert_continuous.continuousAt
  have rhs_tendsto : Filter.Tendsto
    (fun i ↦ T0_real (normalized_hilbert_curve i (4 * f i)))
    Filter.atTop
    (nhds (T0_real (limit_hilbert_curve (4*t)))) := by
    apply TendstoUniformly.tendsto_comp
      (f := (T0_real ∘ limit_hilbert_curve) ∘ ((4 : ℝ) * ·))
      (F := fun i ↦ (T0_real ∘ (normalized_hilbert_curve i)) ∘ (4*·))
      (hg := f_tendsto)
    · apply TendstoUniformly.comp
      apply UniformContinuous.comp_tendstoUniformly ?_ (limit_hilbert_curve_tendstouniformly)
      exact T0_real.uniformContinuous
    apply Continuous.continuousAt
    apply Continuous.comp
    · apply Continuous.comp
      · exact T0_real.continuous
      exact limit_hilbert_continuous
    exact continuous_mul_left 4
  have lhs_eq_rhs :
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i)) =
    (fun i ↦ T0_real (normalized_hilbert_curve i (4 * f i))) := by
    funext i
    sorry
  rw [lhs_eq_rhs] at lhs_tendsto
  apply tendsto_nhds_unique lhs_tendsto rhs_tendsto

/-
The limit is not injective.
-/
lemma limit_hilbert_not_injective : ¬(Set.InjOn limit_hilbert_curve (Set.Icc 0 1)) := by
  sorry

/-
The hilbert curve has Lipschitz constant 2.
-/
