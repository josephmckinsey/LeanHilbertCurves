-- This module serves as the root of the `HilbertCurve` library.
-- Import modules here that should be built as part of the library.

import Mathlib.Data.Real.Basic
import HilbertCurve.HilbertCurveReal
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap


namespace HilbertCurve

/--
The real Hilbert converges at each point.
-/
lemma limit_hilbert_curve_exists (t : ℝ) :
  ∃x, Filter.Tendsto (normalized_hilbert_curve · t) Filter.atTop (nhds x) := by
  apply cauchySeq_tendsto_of_complete
  exact normal_is_cauchy t

noncomputable def limit_hilbert_curve (t : ℝ) : ℝ × ℝ :=
  Classical.choose (limit_hilbert_curve_exists t)

/--
The limit Hilbert curve is the limit of interpolated Hilbert curve.
-/
lemma limit_hilbert_curve_tendsto (t : ℝ) :
  Filter.Tendsto (normalized_hilbert_curve · t) Filter.atTop (nhds (limit_hilbert_curve t)) :=
  Classical.choose_spec (limit_hilbert_curve_exists t)

/--
Eventually for each ε, 4/2^n < ε
-/
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

/--
The real Hilbert curve iterations converges uniformly to the limit Hilbert curve.
-/
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

/-
The limit is contained in [0,1]×[0,1]
-/
lemma limit_hilbert_curve_size (t : ℝ) :
  limit_hilbert_curve t ∈ Set.Icc 0 1 := by
  have limit_def := limit_hilbert_curve_tendsto t
  suffices ∀ᶠ (n : ℕ) in Filter.atTop, (normalized_hilbert_curve n t) ∈ Set.Icc 0 1 by
    have zero_one_closed := isClosed_Icc (a := (0 : ℝ × ℝ)) (b := 1)
    apply zero_one_closed.mem_of_tendsto limit_def this
  apply Filter.Eventually.of_forall
  intro n
  exact hilbert_interpolant_range _ (Set.mem_range_self t)


/-
The limit touches every point in [0,1]×[0,1]
-/
lemma limit_hilbert_surj_on :
  Set.SurjOn limit_hilbert_curve (Set.Icc 0 1) (Set.Icc 0 1) := by
  intro x xy
  -- Since [0, 1] is compact, we can lift the approximate norm_hilbert_inv to
  -- a convergent subsequence.
  have : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  obtain ⟨t, th, φ, φh, h⟩ := this.tendsto_subseq (norm_hilbert_inv_bounded (xh := xy) (x := x))
  use t, th
  set f := fun n ↦ norm_hilbert_inv n x xy
  -- Now we use the uniform convergence to show that we the hilbert curve converges
  -- on the subsequence of f to limit_hilbert_curve t
  have h' : Filter.Tendsto (fun i ↦ normalized_hilbert_curve (φ i) (f (φ i)))
    Filter.atTop (nhds (limit_hilbert_curve t)) :=
    TendstoUniformly.tendsto_comp
      ((tendstoUniformly_iff_seq_tendstoUniformly.mp limit_hilbert_curve_tendstouniformly) φ
        (StrictMono.tendsto_atTop φh))
      (Continuous.continuousAt limit_hilbert_continuous)
      h
  apply tendsto_nhds_unique h'
  -- Now all that remains is to show that it also converges to x
  apply (Filter.tendsto_iff_seq_tendsto (k := Filter.atTop) (
    f := fun i ↦ normalized_hilbert_curve i (f i)
  )).mp ?_ φ (StrictMono.tendsto_atTop φh)
  -- This might be a good one to split
  --have := norm_hilbert_inv_dist i x xy
  -- We can use the bound from the approximate inverse to guarantee convergence.
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

end HilbertCurve

-- We can decompose every ContinuousAffineMap into
-- a continuous linear map + adding a constant
namespace ContinuousAffineMap

variable {R V W : Type*} [Ring R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]
variable [UniformSpace V] [IsUniformAddGroup V]
variable [UniformSpace W] [IsUniformAddGroup W]

/-
#check ContinuousAffineMap.contLinear  -- (only for normed)

def continuous_linear (f : V →ᴬ[R] W) : V →L[R] W where
  toLinearMap := f.linear
  cont := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [<-AffineMap.continuous_iff]
    exact f.cont

omit [IsUniformAddGroup V] in
lemma decomp_cont (f : V →ᴬ[R] W) : ⇑f = ⇑f.continuous_linear + fun _ ↦ f 0 := by
  unfold continuous_linear
  -- import Mathlib.LinearAlgebra.AffineSpace.AffineMap
  -- After importing more things, this broke
  exact AffineMap.decomp (k := R) (V1 := V) (V2 := W) f

lemma uniformContinuous (f : V →ᴬ[R] W) :
  UniformContinuous f := by
  rw [f.decomp]
  apply UniformContinuous.add
    f.continuous_linear.uniformContinuous
    uniformContinuous_const
-/

end ContinuousAffineMap

section

universe u v w

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

variable [CompleteSpace 𝕜]
variable [T2Space E] [FiniteDimensional 𝕜 E]

def AffineMap.toContinuousAffineMap (f : E →ᵃ[𝕜] F) : E →ᴬ[𝕜] F where
  toAffineMap := f
  cont := by
    rw [AffineMap.toFun_eq_coe, AffineMap.continuous_iff]
    exact LinearMap.continuous_of_finiteDimensional (f := f.linear)
end

section

variable {𝕜 R V W W₂ P Q Q₂ : Type*}
variable [NormedAddCommGroup V] [MetricSpace P] [NormedAddTorsor V P]
variable [NormedAddCommGroup W] [MetricSpace Q] [NormedAddTorsor W Q]
variable [NormedField R] [NormedSpace R V] [NormedSpace R W]
variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W]

lemma ContinuousAffineMap.uniformContinuous (f : P →ᴬ[𝕜] Q) :
  UniformContinuous f := by
  -- We should be able to replace the norm with a uniformity
  -- But I'm a bit unclear on the details
  rw [Metric.uniformContinuous_iff]
  intro ε εpos
  simp_rw [NormedAddTorsor.dist_eq_norm']
  simp_rw [show ∀(a b : P), f a -ᵥ f b = f.linear (a -ᵥ b) by
    intro a b
    rw [show f a = f.toAffineMap a by rfl]
    rw [show f b = f.toAffineMap b by rfl]
    rw [<-AffineMap.linearMap_vsub]
  ]
  have : UniformContinuous f.linear := by
    exact f.contLinear.uniformContinuous
  rw [Metric.uniformContinuous_iff] at this
  specialize this ε εpos
  rcases this with ⟨δ, δpos, cont⟩
  use δ, δpos
  intro a b
  specialize cont (a := 0) (b := a -ᵥ b)
  simp only [dist_zero, map_zero] at cont
  exact cont

end

namespace HilbertCurve

noncomputable def T0_real : ℝ × ℝ →L[ℝ] ℝ × ℝ := (1 / 2 : ℝ)•LinearMap.toContinuousLinearMap T0

noncomputable def T3_real (i : ℕ) : ℝ × ℝ →ᴬ[ℝ] ℝ × ℝ :=
  let id := (LinearMap.id (M := ℝ × ℝ) (R := ℝ))
  let post := (1 / (2^(i+1)) : ℝ) • id
  let pre := (2^i : ℝ) • id
  AffineMap.toContinuousAffineMap <|
    (post.toAffineMap.comp (T3 i)).comp
    pre.toAffineMap

noncomputable def T3_real_lim : ℝ × ℝ →ᴬ[ℝ] ℝ × ℝ :=
  AffineMap.toContinuousAffineMap {
    toFun := fun x ↦ (1, 1/(2 : ℝ)) - (1/2 : ℝ) • x.swap
    linear := -(1/2 : ℝ) • {
      toFun := Prod.swap
      map_add' := by simp
      map_smul' := by simp
    }
    map_vadd' p v := by
      simp
      ring_nf
  }

lemma T3_real_tendsto_uniformly : TendstoUniformly (fun i x ↦ T3_real i x) T3_real_lim (Filter.atTop : Filter ℕ) := by
  suffices ∀i x, dist (T3_real i x) (T3_real_lim x) ≤ 1/2^(i+1) by
    rw [Metric.tendstoUniformly_iff]
    intro ε εpos
    have rate_converge : ∀ᶠ (n : ℕ) in Filter.atTop, ∀ x, dist (T3_real n x) (T3_real_lim x) ≤ 1 / 2^(n+1) := by
      apply Filter.Eventually.of_forall
      exact this
    have pow_converge : ∀ᶠ n in Filter.atTop, 1/ 2^(n+1) < ε := by
      suffices Filter.Tendsto (fun n ↦ 1 / (2 : ℝ)^(n+1)) Filter.atTop (nhds 0) by
        rw [NormedAddCommGroup.tendsto_nhds_zero] at this
        have two_pos : ∀x, 0 < 1 / (2:ℝ)^(x + 1) := by intro x; positivity
        simp_rw [Real.norm_eq_abs, fun x ↦ abs_of_pos (two_pos x)] at this
        exact this ε εpos
      have : ∀n, 1/(2: ℝ)^(n+1) = 2⁻¹ * (2⁻¹)^n := by
        intro n; simp [pow_succ]
      simp_rw [this]
      rw [show 0 = 2⁻¹ * (0 : ℝ) by simp]
      apply Filter.Tendsto.const_mul
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      · norm_num
      norm_num
    filter_upwards [rate_converge, pow_converge]
    intro n h h' x
    rw [dist_comm]
    apply (lt_of_le_of_lt (h x) h')
  intro b x
  simp only [T3_real, AffineMap.toContinuousAffineMap, T3, ContinuousAffineMap.coe_mk,
    AffineMap.coe_comp, LinearMap.coe_toAffineMap, AffineMap.coe_mk, Function.comp_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Prod.smul_swap, T3_real_lim]
  have (b : ℕ) : ((1 / (2 : ℝ) ^ (b + 1)) • (((2 : ℝ) ^ (b + 1) - 1, (2 : ℝ) ^ b - 1) - (2 : ℝ) ^ b • x.swap)) =
    -(1/2^(b+1)) + (1, 1 / 2) - (1 / 2 : ℝ) • x.swap:= by
    rw [smul_sub, smul_smul]
    have one_half : 1/(2 : ℝ)^(b+1) * 2^b = 1/2 := by
      simp [pow_succ]
    rw [one_half]
    have one : 1/(2 : ℝ)^(b+1) * 2^(b+1) = 1 := by
      simp
    rw [Prod.smul_def]
    simp only [smul_eq_mul]
    rw [mul_sub, one, mul_sub, one_half]
    rw [mul_one]
    have : (1 - 1 / (2 : ℝ) ^ (b + 1), 1 / (2 : ℝ) - 1 / 2 ^ (b + 1)) =
      (1, 1/2) - 1/2^(b+1) := by
      simp [Prod.sub_def]
    rw [this]
    nth_rw 2 [sub_eq_add_neg]
    rw [add_comm]
  simp_rw [this]
  simp [Prod.norm_def]


lemma T3_uniform_cont (i : ℕ) : UniformContinuous (T3_real i) := by
  exact (T3_real i).uniformContinuous

lemma floor_toNat_tends_to (t : ℝ) (h : 0 ≤ t) :
  Filter.Tendsto (fun i ↦ (⌊t * hilbert_length i⌋.toNat : ℝ) / hilbert_length i)
  Filter.atTop (nhds t) := by
  have : ∀i, dist
    ((⌊t * hilbert_length i⌋.toNat : ℝ) / hilbert_length i) t ≤
    1 / hilbert_length i := by
    intro i
    rw [dist_comm]
    rw [show (⌊t * ↑(hilbert_length i)⌋.toNat : ℝ)
      = (⌊t * ↑(hilbert_length i)⌋.toNat : ℤ) by norm_cast]
    rw [Int.toNat_of_nonneg (by positivity)]
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

-- These will all very annoying yet trivial limit calculations
lemma sequence_exists (t : ℝ) (n : ℕ) (h : n/4 ≤ t) (h' : t ≤ (n+1)/4)
 : ∃f : ℕ → ℕ, Filter.Tendsto (fun i ↦ (f i : ℝ) / hilbert_length i) Filter.atTop (nhds t) ∧
  ∀i≥1, n * hilbert_length i ≤ 4*(f i) ∧ 4*(f i) < (n+1) * hilbert_length i := by
  -- This second condition gives us the right quadrant
  by_cases nice_case : t = (n+1)/4
  · set f : ℕ → ℕ := fun i =>
      (n+1) * hilbert_length (i - 1) - 1 with f_def
    use f
    constructor
    · rw [nice_case, f_def]
      simp only
      -- This is mainly a matter of annoying algebra in the limit
      have (i : ℕ) (ih : i ≥ 1): (((n+1) * hilbert_length (i-1) - 1 : ℕ) : ℝ) / (hilbert_length i : ℝ) =
        (n+1) / 4 - (1 : ℝ) /hilbert_length i := by
        rw [Nat.cast_sub, Nat.cast_mul]
        rw [sub_div]
        nth_rw 2 [show i = (i - 1) + 1 by omega]
        rw [hilbert_length_succ]
        rw [mul_div_assoc]
        rw [Nat.cast_mul]
        rw [div_mul_cancel_right₀ (ne_of_gt (by exact_mod_cast (hilbert_length_pos _)))]
        norm_cast
        change 0 < (n+1) * hilbert_length (i-1)
        apply mul_pos (by omega) (hilbert_length_pos (i-1))
      -- We use a congruence of limit as the equality holds eventually
      rw [Filter.tendsto_congr' <| Filter.eventually_atTop.mpr (Exists.intro 1 this)]
      -- The rest is annoying limit calculations.
      simp_rw [sub_eq_add_neg]
      rw [<-nice_case]
      nth_rw 2 [show t = t + 0 by simp]
      apply Filter.Tendsto.add tendsto_const_nhds
      rw [show (0 : ℝ) = -0 by simp]
      apply Filter.Tendsto.neg
      simp_rw [show
        (fun i => (1 : ℝ) / (hilbert_length i : ℝ)) = fun i => (1/4)^i by
        funext i
        simp [hilbert_length, pow_mul]
      ]
      apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      rw [abs]
      norm_num
    intro i ih
    rw [f_def]; dsimp
    -- Luckily this is easily true from expanding hilbert_length
    nth_rw 1 [show i = (i - 1) + 1 by omega]
    nth_rw 4 [show i = (i - 1) + 1 by omega]
    rw [hilbert_length_succ]
    ring_nf
    have := hilbert_length_pos (i-1)
    omega
  set f : ℕ → ℕ := fun i => ⌊t * hilbert_length i⌋.toNat with f_def
  use f
  have : 0 ≤ t := le_trans (by positivity) h
  constructor
  · apply floor_toNat_tends_to
    exact this
  intro i ih
  rw [f_def]
  dsimp
  have : hilbert_length i = 4 * hilbert_length (i - 1) := by
    nth_rw 1 [show i = i - 1 + 1 by omega]
    rw [hilbert_length_succ]
  zify
  rw [Int.toNat_of_nonneg (by positivity)]
  constructor
  · rify
    -- Since n * hilbert_length i / 4 is an integer,
    -- n/4 ≤ 4 implies n * (hilbert_length i) ≤ ...
    rw [<-mul_inv_le_iff₀' (by norm_num)]
    rw [this, mul_comm 4]
    rw [mul_assoc, Nat.cast_mul, mul_assoc]
    simp only [Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.mul_inv_cancel, mul_one]
    norm_cast
    rw [Int.le_floor]
    push_cast
    rw [mul_comm _ 4, <-mul_assoc]
    gcongr
    linarith
  rify
  -- Similarly since t < (n+1)/4, 4*⌊t * _⌋ ≤ (n+1) * _
  rw [mul_comm, <-lt_mul_inv_iff₀ (by norm_num)]
  nth_rw 2 [this]
  rw [Nat.cast_mul, Nat.cast_ofNat, mul_comm 4 _]
  rw [mul_assoc]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.mul_inv_cancel_right]
  norm_cast
  rw [Int.floor_lt]
  rw [this, Nat.cast_mul, <-mul_assoc]
  push_cast
  gcongr
  · exact_mod_cast hilbert_length_pos (i-1)
  have := lt_of_le_of_ne h' nice_case
  linarith


lemma T0_real_cast (i : ℕ) (x : ℤ × ℤ) :
  T0_real (((2 : ℝ)^i)⁻¹ • x) = ((2 : ℝ)^(i+1))⁻¹ • (T0 x) := by
  rw [map_smul, T0_real]
  simp only [one_div, ZtimesZ.coe_prod, ContinuousLinearMap.coe_smul',
    LinearMap.coe_toContinuousLinearMap', Pi.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [smul_smul, <-mul_inv, pow_succ]
  rfl


lemma T0_real_cast_nat (i : ℕ) (x : ℕ × ℕ) :
  T0_real ((2^i : ℝ)⁻¹ • x) = (2^(i+1) : ℝ)⁻¹ • (T0_nat x) := by
  rw [<-T0_cast]
  rw [show (x : ℝ × ℝ) = (x : ℤ × ℤ) by rfl]
  rw [T0_real_cast i]
  rfl

lemma normalized_recurse_bottom_left {i : ℕ} {j : ℕ}
  (h : get_quadrant i (4*j) = Quadrant.BOTTOM_LEFT) :
  normalized_hilbert_curve (i + 1) (j / hilbert_length i) =
  T0_real (normalized_hilbert_curve i (4*j / hilbert_length i)) := by
  rw [show 4*(j : ℝ) = (4*j : ℕ) by norm_cast]
  rw [show
    (j / hilbert_length i : ℝ) =
    (4 * j : ℕ) / hilbert_length (i + 1) by
    rw [hilbert_length_succ]
    simp
    ring
  ]
  rw [normal_hilbert_of_nat]
  rw [normal_hilbert_of_nat]
  rw [hilbert_curve]
  dsimp only
  rw [h]
  dsimp only
  rw [<-T0_real_cast_nat]


lemma T3_real_cast (i : ℕ) (x : ℤ × ℤ) :
  T3_real i (((2 : ℝ)^i)⁻¹ • x) = ((2 : ℝ)^(i+1))⁻¹ • (T3 i x) := by
  rw [T3_real]
  rw [AffineMap.toContinuousAffineMap]
  simp [T3]


lemma T3_real_cast_nat (i : ℕ) (x : ℕ × ℕ) (h : x.1 ≤ 2^i - 1) (h' : x.2 ≤ 2^(i+1) - 1):
  T3_real i ((2^i : ℝ)⁻¹ • x) = (2^(i+1) : ℝ)⁻¹ • (T3_nat i x) := by
  rw [<-T3_cast_nat i x h h']
  rw [show (x : ℝ × ℝ) = (x : ℤ × ℤ) by rfl]
  rw [T3_real_cast i]
  simp [T3]


lemma normalized_recurse_bottom_right {i : ℕ} {j : ℕ}
  (h : get_quadrant i (4*j) = Quadrant.BOTTOM_RIGHT) :
  normalized_hilbert_curve (i + 1) (j / hilbert_length i) =
  T3_real i (normalized_hilbert_curve i ((4*j - 3 * hilbert_length i) / hilbert_length i)) := by
  have := (bottom_right_eq i _).mp h
  rw [show 4*(j : ℝ) - 3 * hilbert_length i = (4*j - 3 * hilbert_length i : ℕ) by norm_cast]
  rw [show
    (j / hilbert_length i : ℝ) =
    (4 * j : ℕ) / hilbert_length (i + 1) by
    rw [hilbert_length_succ]
    simp
    ring
  ]
  rw [normal_hilbert_of_nat]
  rw [normal_hilbert_of_nat]
  rw [hilbert_curve]
  dsimp only
  rw [h]
  dsimp only
  rw [T3_real_cast_nat]
  · exact (hilbert_curve_size i _).1
  apply le_trans (hilbert_curve_size i _).2
  omega


/-
The hilbert curve is a fractal just like its construction, i.e.
it can be broken up into 4 copies of itself.
-/
lemma limit_hilbert_recurse_bottom_left (t : ℝ) (h : t ∈ Set.Icc 0 (1/4)) :
  limit_hilbert_curve t = T0_real (limit_hilbert_curve (4*t)) := by
  rcases (sequence_exists t 0 (by linarith [h.1]) (by linarith [h.2]))
    with ⟨fnat, f_tendsto, hf2⟩
  set f := fun i => fnat i / (hilbert_length i : ℝ) with f_def
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
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i)) =ᶠ[Filter.atTop]
    (fun i ↦ T0_real (normalized_hilbert_curve i (4 * f i))) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro i ih
    rw [f_def]
    dsimp
    have : get_quadrant i (4*(fnat i)) = Quadrant.BOTTOM_LEFT := by
      rw [bottom_left_eq]
      have := (hf2 i ih).2
      simpa
    rw [<-mul_div_assoc]
    rw [normalized_recurse_bottom_left this]
  rw [Filter.tendsto_congr' lhs_eq_rhs] at lhs_tendsto
  apply tendsto_nhds_unique lhs_tendsto rhs_tendsto

lemma limit_hilbert_recurse_bottom_right (t : ℝ) (h : t ∈ Set.Icc (3/4) 1) :
  limit_hilbert_curve t = T3_real_lim (limit_hilbert_curve (4*t - 3)) := by
  rcases (sequence_exists t 3 (by linarith [h.1]) (by linarith [h.2]))
    with ⟨fnat, f_tendsto, hf2⟩
  set f := fun i => fnat i / (hilbert_length i : ℝ) with f_def
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
    (fun i ↦ T3_real i (normalized_hilbert_curve i (4 * f i - 3)))
    Filter.atTop
    (nhds (T3_real_lim (limit_hilbert_curve (4*t - 3)))) := by
    have : Filter.Tendsto (fun i ↦ (normalized_hilbert_curve i (4 * f i - 3)))
      Filter.atTop
      (nhds (limit_hilbert_curve (4*t - 3))) := by
      apply TendstoUniformly.tendsto_comp
      · exact limit_hilbert_curve_tendstouniformly
      · exact Continuous.continuousAt limit_hilbert_continuous
      apply Filter.Tendsto.sub_const
      apply Filter.Tendsto.const_mul
      exact f_tendsto
    apply TendstoUniformly.tendsto_comp
      (hf := T3_real_lim.continuous.continuousAt)
      (hg := this)
      (g := (fun i ↦ (normalized_hilbert_curve i (4 * f i - 3))))
      (h := T3_real_tendsto_uniformly)
  have lhs_eq_rhs :
    (fun i ↦ normalized_hilbert_curve (i + 1) (f i)) =ᶠ[Filter.atTop]
    (fun i ↦ T3_real i (normalized_hilbert_curve i (4 * f i - 3))) := by
    apply Filter.eventually_atTop.mpr
    use 1
    intro i ih
    rw [f_def]
    dsimp
    have : get_quadrant i (4*(fnat i)) = Quadrant.BOTTOM_RIGHT := by
      rw [bottom_right_eq]
      exact (hf2 i ih).1
    rw [<-mul_div_assoc]
    rw [normalized_recurse_bottom_right this]
    have : ((4 : ℝ) * fnat i - (3 : ℝ) * (hilbert_length i)) / ↑(hilbert_length i) =
      (4 : ℝ) * fnat i / (hilbert_length i) - (3 : ℝ) := by
      have := hilbert_length_pos i
      field_simp; ring
    rw [this]
  rw [Filter.tendsto_congr' lhs_eq_rhs] at lhs_tendsto
  apply tendsto_nhds_unique lhs_tendsto rhs_tendsto


-- TODO: There are also cases for T1_real and T2_real which we don't prove.

/-
The limit is not injective.
-/
lemma limit_hilbert_not_injective : ¬(Set.InjOn limit_hilbert_curve (Set.Icc 0 1)) := by
  suffices ∃t1 ∈ Set.Icc 0 (1/4), ∃t2 ∈ Set.Icc (3/4) 1, limit_hilbert_curve t1 = limit_hilbert_curve t2 by
    rcases this with ⟨t1, h1, t2, h2, h3⟩
    have : t1 ≠ t2 := by
      linarith [h1.2, h2.1]
    simp [Set.InjOn]
    use t1, (by linarith [h1.1]), (by linarith [h1.2])
    use t2, (by linarith [h2.1]), (by linarith [h2.2])
  set x : ℝ × ℝ := (1/2, 0) with x_def
  obtain ⟨t1, t1h, h1⟩ : ∃t, t ∈ Set.Icc 0 1 ∧ limit_hilbert_curve t = (0, 1) := by
    apply limit_hilbert_surj_on
    simp [Prod.le_def]
  obtain ⟨t2, t2h, h2⟩ : ∃t, t ∈ Set.Icc 0 1 ∧ limit_hilbert_curve t = (1, 1) := by
    apply limit_hilbert_surj_on
    simp [Prod.le_def]
  apply_fun T0_real at h1
  apply_fun T3_real_lim at h2
  rw [show T0_real (0, 1) = (1/2, 0) by
    simp [T0_real, T0]] at h1
  rw [show T3_real_lim (1, 1) = (1/2, 0) by
    simp [T3_real_lim, AffineMap.toContinuousAffineMap,
      Prod.sub_def, Prod.smul_def]
    norm_num] at h2
  rw [show t1 = 4 * (t1 / 4) by ring] at h1
  rw [<-limit_hilbert_recurse_bottom_left] at h1
  rotate_left
  · constructor <;> linarith [t1h.1, t1h.2]
  rw [show t2 = 4 * ((t2 + 3) / 4 ) - 3 by ring] at h2
  rw [<-limit_hilbert_recurse_bottom_right] at h2
  rotate_left
  · constructor <;> linarith [t2h.1, t2h.2]
  refine ⟨t1/4, ?_, (t2 + 3) / 4, ?_, ?_⟩
  · rcases t1h with ⟨t1h1, t1h2⟩
    constructor
    · linarith
    linarith
  · rcases t2h with ⟨t2h1, t2h2⟩
    constructor
    · linarith
    linarith
  rw [h1, h2]

-- TODO: Any continuous function that satisfies the
-- same symmetry properties should be identical
-- as long as f(0) = (0, 0)


/-
The hilbert curve is not Lipschitz.
-/
/-
Eh I'll get around to it.The lipschitz constant at
0 goes up for each iteration: 0, 2, 4, 8, 16.
But you have to look at closer and closer intervals to
find a point where the lipschitz bound ‖f(x) - f(y)‖ ≤ C ‖x - y‖ is violated.

‖f(x) - f(y)‖ ≤ C(‖x - y‖)

Some approximate values (+ a constant)

C(1/4) ∼ 2.
C(1/16) ∼ 4.
C(1/64) ∼ 8.

C(x) = 1/√x

‖f(x) - f(y)‖ ≤ √(x - y)

I suspect the constant is higher, but some bounds
based on the symmetry suggests a constant of 2.

This is Holder continuity with exponent 1/2.

It turns out any Holder continuous map from s with exponent 1/d
can have dimension at most d * dimH s,
so in our case, we know that since the image of the
Hilber curve has dimension 2, then it can't
be Holder continuous with exponent > 1/2, and in particular,
it can't be Lipschitz or differentiable.
-/

end HilbertCurve
