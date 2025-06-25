import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic
import Mathlib.Algebra.Order.Sub.Defs
import HilbertCurve.Basic

@[coe]
def ZtimesZ.toR : ℤ × ℤ → ℝ × ℝ :=
  fun p => (p.1, p.2)

instance coe_ZtoR : Coe (ℤ × ℤ) (ℝ × ℝ) where
  coe := ZtimesZ.toR

@[simp]
theorem ZtimesZ.coe_prod (p : ℤ × ℤ) : (p : ℝ × ℝ) = (↑p.1, ↑p.2) := rfl

@[simp] theorem ZtimesZ.coe_first (p : ℕ × ℕ) : (p : ℝ × ℝ).1 = p.1 := rfl
@[simp] theorem ZtimesZ.coe_second (p : ℕ × ℕ) : (p : ℝ × ℝ).2 = p.2 := rfl


@[simp, norm_cast]
lemma RtimesR.cast_eq (mn mn' : ℤ × ℤ) : (mn : ℝ × ℝ) = mn' ↔ mn = mn' := by
  simp [Prod.ext_iff]

@[simp, norm_cast]
lemma RtimesR.cast_le (mn mn' : ℤ × ℤ) : (mn : ℝ × ℝ) ≤ mn' ↔  mn ≤ mn' := by
  simp [Prod.le_def, Int.cast_le]

@[simp, norm_cast]
lemma RtimesR.cast_le_ofNat (mn mn' : ℕ × ℕ) : (mn : ℝ × ℝ) ≤ mn' ↔  mn ≤ mn' := by
  simp only [coe_prod, Prod.le_def, Nat.cast_le]

@[simp, norm_cast]
lemma RtimesR.cast_eq_ofNat (mn mn' : ℕ × ℕ) : (mn : ℝ × ℝ) = mn' ↔  mn = mn' := by
  simp only [coe_prod, Prod.ext_iff, Nat.cast_inj]

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
    apply lt_or_ge
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

lemma interpolate_eq_affine_map (f : ℤ → ℝ × ℝ) (n : ℤ)
  (t : ℝ) (h : n ≤ t) (h' : t ≤ n+1) :
  interpolate_points f t = AffineMap.lineMap (f n) (f (n+1)) (t - n) := by
  have h₁ : t < (n : ℝ) + 1 ∨ t = (n : ℝ) + 1 := lt_or_eq_of_le h'
  cases h₁ with
  | inl h₁ =>
    have h₃ : ⌊t⌋ = n := by
      rw [Int.floor_eq_iff]
      exact And.symm ⟨h₁, h⟩
    have h₄ : (t - ⌊t⌋ : ℝ) = t - n := by
      rw [h₃]
    rw [interpolate_points, h₃]
  | inr h₁ =>
    have h₃ : ⌊t⌋ = n + 1 := by simp [h₁]
    have h₄ : (t - ⌊t⌋ : ℝ) = 0 := by simp [h₃, h₁]
    rw [interpolate_points, h₄, h₃, h₁]
    simp

lemma interpolate_eq_affine_map' (f : ℤ → ℝ × ℝ) (n : ℤ) :
  Set.EqOn (interpolate_points f) (AffineMap.lineMap (f n) (f (n+1)) ∘ (fun x ↦ x - n))
  (Set.Icc n (n+1)) := fun t th ↦
  interpolate_eq_affine_map (t := t) (f := f)
    (h := th.1) (h' := th.2)

lemma local_finiteness (x : ℝ):
  {(i : ℤ) | (Set.Icc (i : ℝ) (i + 1) ∩ Set.Ioo (x - 1) (x + 1)).Nonempty}.Finite := by
  have h1 : ∀i, i ≤ x-2 ∨ x + 2 ≤ i →  (Set.Icc (i : ℝ) (i + 1) ∩ Set.Ioo (x - 1) (x+1)) = ∅ := by
    rintro i (ih | ih) <;>
    { refine Disjoint.inter_eq ?_
      refine Set.disjoint_iff_forall_ne.mpr ?_
      intro a ah b bh q
      simp at ah bh
      linarith }
  have h2 : ∀i : ℤ, (Set.Icc (i : ℝ) (i + 1) ∩ Set.Ioo (x - 1) (x+1)).Nonempty → ↑i ∈ Set.Ioo (x-2) (x+2) := by
    intro i
    contrapose!
    intro h
    apply h1
    contrapose! h
    exact h
  apply Set.Finite.subset (s := {i : ℤ | ↑i ∈ Set.Ioo (x-2) (x+2)})
  · change (((↑) : ℤ → ℝ) ⁻¹' Set.Ioo (x-2) (x+2)).Finite
    simp only [Int.preimage_Ioo, Int.floor_sub_ofNat, Int.ceil_add_ofNat]
    exact Set.finite_Ioo (⌊x⌋ - 2) (⌈x⌉ + 2)
  apply h2

lemma interpolate_is_continuous (f : ℤ → ℝ × ℝ) :
  Continuous (interpolate_points f) := by
  set s : ℤ → Set ℝ := fun i => Set.Icc i (i+1) with s_def
  have : LocallyFinite s := by
    unfold LocallyFinite
    intro x
    use (Set.Ioo (x-1) (x+1))
    constructor
    · exact Ioo_mem_nhds (sub_one_lt x) (lt_add_one x)
    rw [s_def]
    exact local_finiteness x
  apply LocallyFinite.continuous
    (f := s)
    this
    (iUnion_Icc_intCast _)
    (fun i ↦ isClosed_Icc)
  intro i
  rw [s_def]
  dsimp
  apply ContinuousOn.congr (h' := interpolate_eq_affine_map' f i)
  apply Continuous.continuousOn
  unfold Function.comp
  simp_all only [continuous_prodMk, AffineMap.fst_lineMap, AffineMap.snd_lineMap, s]
  apply And.intro
  · apply Continuous.add
    · simp_all only [vsub_eq_sub, LinearMap.coe_toAffineMap, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
        smul_eq_mul]
      apply Continuous.mul
      · apply continuous_add_right
      · apply continuous_const
    · simp_all only [AffineMap.const_apply]
      apply continuous_const
  · apply Continuous.add
    · simp_all only [vsub_eq_sub, LinearMap.coe_toAffineMap, LinearMap.coe_smulRight, LinearMap.id_coe, id_eq,
        smul_eq_mul]
      apply Continuous.mul
      · apply continuous_add_right
      · apply continuous_const
    · simp_all only [AffineMap.const_apply]
      apply continuous_const


lemma affine_distance (x y : ℝ × ℝ) (t : ℝ)
  (h : 0 ≤ t) (h' : t ≤ 1) :
  dist (AffineMap.lineMap x y t) x ≤ dist x y := by
  simp only [dist_lineMap_left, Real.norm_eq_abs]
  have : |t| ≤ 1 := by
    rw [abs_of_nonneg h]
    exact h'
  exact mul_le_of_le_one_left dist_nonneg this

lemma interpolate_distance (f : ℤ → ℝ × ℝ) (t : ℝ) :
  dist (interpolate_points f t) (interpolate_points f ⌊t⌋) ≤
  dist (f ⌊t⌋) (f (⌊t⌋ + 1)) := by
  have floor_le : ⌊t⌋ ≤ t := by exact Int.floor_le t
  have le_floor : t ≤ ⌊t⌋ + 1 := le_of_lt (Int.lt_floor_add_one t)
  rw [<-interpolate_interpolates]
  rw [interpolate_eq_affine_map (h := floor_le) (h' := le_floor)]
  apply affine_distance
  · linarith
  linarith

-- How would do something like extend the cantorset -> [0, 1] to [0, 1] -> [0, 1]
