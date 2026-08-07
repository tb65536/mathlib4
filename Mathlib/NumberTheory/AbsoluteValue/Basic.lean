/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
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

end algebra

section localDegree

variable {L : Type*} [Field L] (w : AbsoluteValue L ℝ) (K : Type*) [Field K] [Algebra K L]

instance : w.LiesOver (w.comp (algebraMap K L).injective) := ⟨rfl⟩

def localDegree : ℕ :=
  letI v := w.comp (algebraMap K L).injective
  letI := algebraOfLiesOver v w
  Module.finrank v.Completion w.Completion

end localDegree

section localDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v] [Algebra v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

theorem algebraMap_eq :
    (WithAbs.isometry_map v w).mapRingHom = algebraMap v.Completion w.Completion := by
  apply DFunLike.ext'
  apply UniformSpace.Completion.extension_unique
  · exact (UniformSpace.Completion.uniformContinuous_coe (WithAbs w)).comp
      (WithAbs.isometry_map v w).uniformContinuous
  · apply uniformContinuous_addMonoidHom_of_continuous
    apply continuous_algebraMap
  · intro x
    exact IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs

theorem algebra_eq :
    ‹_› = algebraOfLiesOver v w := by
  apply Algebra.algebra_ext
  rw [← algebraMap_eq v w]
  intro r
  rfl

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

instance (w : absoluteValuesOver v L) : w.1.LiesOver v := w.2

end absoluteValuesOver

section sum

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

instance : IsArtinianRing (v.Completion ⊗[K] L) := .of_finite v.Completion (v.Completion ⊗[K] L)

instance : Finite (PrimeSpectrum (v.Completion ⊗[K] L)) := inferInstance

def absoluteValuesOverEquiv : v.absoluteValuesOver L ≃ PrimeSpectrum (v.Completion ⊗[K] L) := by
  sorry

-- `A = L ⊗[K] K_v = ∏ A_m` is an Artinian ring
-- absolutes values over `L` are in bijection with maximal ideals of `A`
-- `L_w ≃ A_m/m`
-- `∑_w [L_w : K_v] = ∑_m dim_(K_v) (A_m/m) ≤ ∑_m dim_(K_v) A_m = dim_(K_v) A = [L : K]`

instance : Finite (v.absoluteValuesOver L) := Finite.of_equiv _ (v.absoluteValuesOverEquiv L).symm

theorem sum_eq [Fintype (v.absoluteValuesOver L)]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], Algebra v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], ContinuousSMul v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], IsScalarTower K v.Completion w.Completion] :
    ∑ w : v.absoluteValuesOver L,
      Module.finrank v.Completion w.1.Completion ≤ Module.finrank K L := by
  let A := v.Completion ⊗[K] L
  have : Fintype (PrimeSpectrum A) := sorry
  rw [← Module.finrank_baseChange (R := v.Completion), IsArtinianRing.finrank_eq_sum_primeSpectrum]
  sorry

end sum

section ramification

end ramification

end AbsoluteValue
