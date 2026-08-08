/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.UniformField

/-!
# Extensions of absolute values
-/

@[expose] public noncomputable section

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

theorem completion_apply (x : v.Completion) :
    v.completion x = UniformSpace.Completion.extension (v ∘ WithAbs.ofAbs) x :=
  rfl

instance : v.completion.LiesOver v where
  comp_eq := by
    ext x
    exact (v.completion_apply x).trans
      (UniformSpace.Completion.extension_coe uniformContinuous_norm (WithAbs.toAbs v x))

end completion

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
    let L_w := (v.Completion ⊗[K] L) ⧸ p.asIdeal
    have : Algebra K_v L_w := inferInstance
    have : FiniteDimensional K_v L_w := inferInstance
    let v' : AbsoluteValue v.Completion ℝ := v.completion
    let w : AbsoluteValue L_w ℝ := sorry -- extend valuation on K_v to L_w
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
