/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Subadditive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.UniformField

/-!
# Extensions of absolute values
-/

@[expose] public noncomputable section

-- todo: PR
instance (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue K)) :=
  IsometryEquiv.completeSpace
  { __ := WithAbs.equiv (NormedField.toAbsoluteValue K)
    isometry_toFun := by simp [AddMonoidHomClass.isometry_iff_norm, WithAbs.norm_eq_apply_ofAbs] }

-- #42607
section gelfand

open scoped Topology

variable {A : Type*}

section SeminormedRing

variable [SeminormedRing A]

/-- The limit `‖a ^ k‖ ^ (1 / k)` of an element `a` in a normed ring. -/
def spectralRadiusLim (a : A) : ℝ :=
  Filter.atTop.limUnder fun k : ℕ ↦ ‖a ^ k‖ ^ (k : ℝ)⁻¹

theorem tendsto_spectralRadiusLim (a : A) :
    Filter.atTop.Tendsto (fun k : ℕ ↦ ‖a ^ k‖ ^ (k : ℝ)⁻¹) (𝓝 (spectralRadiusLim a)) := by
  have h : Submultiplicative fun k ↦ ‖a ^ k‖ :=
    fun m n ↦ by simpa [pow_add] using norm_mul_le (a ^ m) (a ^ n)
  exact tendsto_nhds_limUnder ⟨h.lim, h.tendsto_lim fun n ↦ norm_nonneg (a ^ n)⟩

@[bound]
theorem spectralRadiusLim_nonneg (a : A) : 0 ≤ spectralRadiusLim a :=
  isClosed_Ici.mem_of_tendsto (tendsto_spectralRadiusLim a)
    (.of_forall fun k ↦ by rw [Set.mem_Ici]; positivity)

theorem Commute.spectralRadiusLim_mul_le {a b : A} (h : Commute a b) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b := by
  refine OrderClosedTopology.isClosed_le'.mem_of_tendsto
    ((tendsto_spectralRadiusLim (a * b)).prodMk_nhds
      ((tendsto_spectralRadiusLim a).mul (tendsto_spectralRadiusLim b))) (.of_forall fun n ↦ ?_)
  simp_rw [Set.mem_ofPred_eq, h.mul_pow]
  grw [norm_mul_le, Real.mul_rpow] <;> positivity

theorem spectralRadiusLim_pow_of_ne_zero (a : A) (n : ℕ) (hn : n ≠ 0) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  refine tendsto_nhds_unique (tendsto_spectralRadiusLim (a ^ n)) ((((tendsto_spectralRadiusLim a).comp
    (strictMono_mul_left_of_pos hn.pos).tendsto_atTop).pow n).congr fun k ↦ ?_)
  rw [Function.comp_apply, Nat.cast_mul, mul_inv_rev,
    ← Real.rpow_mul_natCast (by positivity), inv_mul_cancel_right₀ (by simpa), pow_mul]

theorem spectralRadiusLim_pow [NormOneClass A] (a : A) (n : ℕ) :
    spectralRadiusLim (a ^ n) = spectralRadiusLim a ^ n := by
  by_cases hn : n = 0
  · simpa [hn, eq_comm] using tendsto_spectralRadiusLim (1 : A)
  · exact spectralRadiusLim_pow_of_ne_zero a n hn

-- #42607
theorem Commute.spectralRadiusLim_add_le {a b : A} (hc : Commute a b) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b := by
  sorry

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing A]

theorem spectralRadiusLim_mul_le (a b : A) :
    spectralRadiusLim (a * b) ≤ spectralRadiusLim a * spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_mul_le

theorem spectralRadiusLim_add_le (a b : A) :
    spectralRadiusLim (a + b) ≤ spectralRadiusLim a + spectralRadiusLim b :=
  (Commute.all a b).spectralRadiusLim_add_le

end SeminormedCommRing

end gelfand

open TensorProduct

namespace AbsoluteValue

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) (T : Type*) [CommSemiring T] [Algebra T R] [FaithfulSMul T R]

-- #42566
def under : AbsoluteValue T S :=
  v.comp (FaithfulSMul.algebraMap_injective T R)

end AbsoluteValue

-- #42542
namespace AbsoluteValue

section algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v]

theorem WithAbs.isometry_map : Isometry (WithAbs.map v w (algebraMap K L)) := by
  rw [← LiesOver.comp_eq w v]
  exact AddMonoidHomClass.isometry_of_norm _ fun x ↦ rfl

-- will be deprecated by #42634
-- (UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L)) (WithAbs.isometry_map v w).continuous).toAlgebra
@[instance_reducible]
def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (WithAbs.isometry_map v w).mapRingHom.toAlgebra

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion
    (WithAbs.isometry_map v w).isometry_mapRingHom.continuous

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦
    ((WithAbs.isometry_map v w).mapRingHom_coe (WithAbs.toAbs v x)).symm

variable [Algebra v.Completion w.Completion] [ContinuousSMul v.Completion w.Completion]
  [IsScalarTower K v.Completion w.Completion]

theorem algebraMap_eq_mapRingHom :
    algebraMap v.Completion w.Completion = (WithAbs.isometry_map v w).mapRingHom := by
  symm
  apply DFunLike.ext'
  apply UniformSpace.Completion.extension_unique
  · exact (UniformSpace.Completion.uniformContinuous_coe (WithAbs w)).comp
      (WithAbs.isometry_map v w).uniformContinuous
  · apply uniformContinuous_addMonoidHom_of_continuous
    apply continuous_algebraMap
  · intro x
    exact IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs

theorem algebra_eq : ‹_› = algebraOfLiesOver v w := by
  apply Algebra.algebra_ext
  rw [algebraMap_eq_mapRingHom v w]
  intro r
  rw [Isometry.mapRingHom, UniformSpace.Completion.mapRingHom_apply]
  rfl

end algebra

section localDegree

variable {L : Type*} [Field L] (w : AbsoluteValue L ℝ) (K : Type*) [Field K] [Algebra K L]

-- #42566
instance : w.LiesOver (w.under K) := ⟨rfl⟩

def localDegree : ℕ :=
  letI v := w.under K
  letI := algebraOfLiesOver v w
  Module.finrank v.Completion w.Completion

end localDegree

section localDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v] [Algebra v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

theorem localDegree_eq : w.localDegree K = Module.finrank v.Completion w.Completion := by
  have := LiesOver.comp_eq w v
  rw [localDegree, algebra_eq v w]
  subst this
  rfl

end localDegree

section absoluteValuesOver

variable {K S : Type*} [Field K] [PartialOrder S] [Semiring S] (v : AbsoluteValue K S)
  (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]

def absoluteValuesOver : Set (AbsoluteValue L S) :=
  {w | w.LiesOver v}

variable {v L}

@[simp]
theorem mem_absoluteValuesOver {w : AbsoluteValue L S} :
    w ∈ v.absoluteValuesOver L ↔ w.LiesOver v :=
  .rfl

instance (w : absoluteValuesOver v L) : w.val.LiesOver v := w.2

end absoluteValuesOver

section completion

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The extended absolute value on `v.Completion`. -/
def completion : AbsoluteValue v.Completion ℝ := NormedField.toAbsoluteValue v.Completion

-- this might just be a bad lemma
theorem coe_completion : ⇑v.completion = UniformSpace.Completion.extension (v ∘ WithAbs.ofAbs) :=
  rfl

theorem uniformContinuous_completion : UniformContinuous v.completion := uniformContinuous_norm

variable {v}

theorem completion_apply (x : v.Completion) : v.completion x = ‖x‖ :=
  rfl

instance : v.completion.LiesOver v where
  comp_eq := by
    ext x
    exact UniformSpace.Completion.norm_coe (WithAbs.toAbs v x)

instance : CompleteSpace (WithAbs v.completion) :=
  inferInstanceAs (CompleteSpace (WithAbs (NormedField.toAbsoluteValue v.Completion)))

end completion

section extension

-- might be unnecessary
theorem le_one_if_not_isNontrivial {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
    (hv : ¬ v.IsNontrivial) (x : K) : v x ≤ 1 := by
  by_cases hx : x = 0
  sorry

open scoped Topology

theorem foo (K L : Type*) [Field K] [Field L] [Algebra K L]
    (f g : L → ℝ) (Cf Cg : ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : ∀ x, f x ≤ Cf * g x) (hg : ∀ x, g x ≤ Cg * f x)
    (hf' : ∀ x n, f (x ^ n) = f x ^ n) (hg' : ∀ x n, g (x ^ n) = g x ^ n) :
    f = g := by
  rcases le_or_gt Cf 0 with hCf | hCf
  · ext x
    specialize hf x
    specialize hg0 x
    grw [hCf, zero_mul] at hf
    grind [le_antisymm]
  rcases le_or_gt Cg 0 with hCg | hCg
  · ext x
    specialize hf x
    specialize hg x
    specialize hf0 x
    grw [hCg, zero_mul] at hg
    grind [le_antisymm]
  ext x
  have h : ∀ᶠ (n : ℕ) in Filter.atTop, f x ≤ Cf ^ (n : ℝ)⁻¹ * g x ∧ g x ≤ Cg ^ (n : ℝ)⁻¹ * f x := by
    rw [Filter.eventually_atTop]
    use 1
    intro n hn
    specialize hf (x ^ n)
    specialize hg (x ^ n)
    rw [hf', hg', ← Real.rpow_natCast,
      ← Real.le_rpow_inv_iff_of_pos (by bound) (by bound) (by simp; grind),
      Real.mul_rpow (by bound) (by bound), ← Real.rpow_natCast_mul (by bound),
      mul_inv_cancel₀ (by simp; grind), Real.rpow_one] at hf hg
    exact ⟨hf, hg⟩
  replace h := Filter.eventually_and.mp h
  refine le_antisymm ?_ ?_
  -- const would be better
  · refine ge_of_tendsto ?_ h.1
    sorry
  · refine ge_of_tendsto ?_ h.2
    sorry

-- f(x) ≤ C * g(x) by direct estimation
-- g(x) ≤ C * |x|

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]



/-
Let f(x^n)=f(x)^n, f(xy)=f(x)f(y), g(x^n)=g(x)^n, g(x+y)<=g(x)+g(y), and g(xy)<=g(x)g(y). Does it follow that f(x)=g(x)?

-/

def extension [Module.Finite K L] [CompleteSpace (WithAbs v)] : AbsoluteValue L ℝ where
  toFun x := v (Algebra.norm K x) ^ (Module.finrank K L : ℝ)⁻¹
  map_mul' := by simp [Real.mul_rpow]
  nonneg' x := by positivity
  eq_zero' := by simp [Module.finrank_pos.ne']
  add_le' x y := by
    classical
    -- first handle the case where `v` is trivial
    by_cases hv : v.IsNontrivial; swap
    · rw [isNontrivial_iff_ne_trivial v, not_ne_iff] at hv
      simp [hv, AbsoluteValue.trivial, Module.finrank_pos.ne']
      grind
    -- now `L` is a normed vector space over `WithAbs v`
    let : NontriviallyNormedField (WithAbs v) :=
    { non_trivial := by
        obtain ⟨x, hx⟩ := hv.exists_abv_gt_one
        exact ⟨WithAbs.toAbs v x, hx⟩ }
    let := NormedAddCommGroup.induced _ _ _ (Module.finBasis (WithAbs v) L).equivFun.injective
    let := NormedSpace.induced _ _ _ (Module.finBasis (WithAbs v) L).equivFun
    -- let `T x` be multiplication by `x` on `L`
    let T x := (LinearMap.mul (WithAbs v) L x).toContinuousLinearMap
    have key₀ (x : L) : Algebra.norm K x = (Algebra.norm (WithAbs v) x).ofAbs :=
      (Algebra.norm_eq_of_ringEquiv (WithAbs.equiv v) rfl x).symm
    -- probably just keep this version of key:
    have key x : Algebra.norm K x = (T x).toLinearMap.det.ofAbs :=
      (Algebra.norm_eq_of_ringEquiv (WithAbs.equiv v) rfl x).symm
    have key' x y : T (x + y) = T x + T y := by simp [T]
    have key'' x y : Commute (T x) (T y) := by
      ext x
      simp [T]
      grind
    suffices ∀ T : L →L[WithAbs v] L,
        v T.toLinearMap.det.ofAbs ^ (Module.finrank K L : ℝ)⁻¹ = spectralRadiusLim T by
      simp [key, this]
      rw [key']
      exact (key'' x y).spectralRadiusLim_add_le
    -- define spectralRadiusLim as a norm on L (this may also shortcut some of the above)
    -- `|v x| ≤ C * (spectralRadiusLim x) ^ n`
    -- `|v (x ^ k)| ≤ C * (spectralRadiusLim (x ^ k)) ^ n`
    -- `|v x| ^ k ≤ C * ((spectralRadiusLim x) ^ n) ^ k`
    -- `|v x| ≤ C ^ (1 / k) * (spectralRadiusLim x) ^ n`
    -- `|v x| ≤ (spectralRadiusLim x) ^ n`
    --  reverse bound gives equality
    sorry

instance [Module.Finite K L] [CompleteSpace (WithAbs v)] : (v.extension L).LiesOver v where
  comp_eq := by
    ext x
    simp [extension, AbsoluteValue.comp]
    sorry

-- once you have extensions of absolute values on complete fields, the Artinian machinery
-- let's you pick an arbitrary extension if desired

end extension

section sum

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

instance : IsArtinianRing (v.Completion ⊗[K] L) := .of_finite v.Completion (v.Completion ⊗[K] L)

instance : Finite (PrimeSpectrum (v.Completion ⊗[K] L)) := inferInstance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def absoluteValuesOverEquiv : v.absoluteValuesOver L ≃ PrimeSpectrum (v.Completion ⊗[K] L) where
  toFun w := by
    let := algebraOfLiesOver v w.val
     -- can weaken to be over K if desired
    let φ : v.Completion ⊗[K] L →ₐ[v.Completion] w.val.Completion := by
      apply Algebra.TensorProduct.productLeftAlgHom
      · apply Algebra.ofId
      · apply IsScalarTower.toAlgHom
    exact ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  invFun p := by
    let K_v := v.Completion
    let L_w := (K_v ⊗[K] L) ⧸ p.asIdeal
    have : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
    let : Field L_w := Ideal.Quotient.field p.asIdeal
    let v' : AbsoluteValue K_v ℝ := v.completion
    let w : AbsoluteValue L_w ℝ := v'.extension L_w -- extend valuation on K_v to L_w
    refine ⟨w.under L, ?_⟩
    simp
    sorry
  left_inv := by
    sorry
  right_inv := by
    sorry

-- `A = L ⊗[K] K_v = ∏ A_m` is an Artinian ring
-- absolutes values over `L` are in bijection with maximal ideals of `A`
-- `L_w ≃ A_m/m`
-- `∑_w [L_w : K_v] = ∑_m dim_(K_v) (A_m/m) ≤ ∑_m dim_(K_v) A_m = dim_(K_v) A = [L : K]`

instance : Finite (v.absoluteValuesOver L) := Finite.of_equiv _ (v.absoluteValuesOverEquiv L).symm

/-- The fundamental inequality. -/
theorem sum_eq [Fintype (v.absoluteValuesOver L)]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], Algebra v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], ContinuousSMul v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], IsScalarTower K v.Completion w.Completion] :
    ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤ Module.finrank K L := by
  let A := v.Completion ⊗[K] L
  have : Fintype (PrimeSpectrum A) := sorry
  rw [← Module.finrank_baseChange (R := v.Completion), IsArtinianRing.finrank_eq_sum_primeSpectrum]
  change ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤
    ∑ p : PrimeSpectrum A, Module.finrank v.Completion (Localization.AtPrime p.asIdeal)
  -- these are both finranks, want map injective `L_w → A_m`
  sorry

end sum

section ramification

end ramification

end AbsoluteValue
