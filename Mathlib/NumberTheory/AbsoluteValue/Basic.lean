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

namespace Completion

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

instance : CompletableTopField (WithAbs v) :=
  let : NormedField K := v.toNormedField
  NormedField.instCompletableTopField

end Completion

section absoluteValuesOver

variable {K S : Type*} [Field K] [PartialOrder S] [Semiring S] (v : AbsoluteValue K S)
  (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]

def absoluteValuesOver : Set (AbsoluteValue L S) :=
  {w | w.LiesOver v}

end absoluteValuesOver

section algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v]

@[implicit_reducible]
def algebraOfLiesOver : Algebra v.Completion w.Completion := by
  have : v.Completion →+* w.Completion :=
    Isometry.mapRingHom (f := WithAbs.map v w (algebraMap K L)) ?_
  exact this.toAlgebra
  rw [← LiesOver.comp_eq w v]
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  rfl

end algebra

section localDegree

variable {L : Type*} [Field L] (w : AbsoluteValue L ℝ) (K : Type*) [Field K] [Algebra K L]

instance : w.LiesOver (w.comp (algebraMap K L).injective) := ⟨rfl⟩

def localDegree : ℕ :=
  letI v := w.comp (algebraMap K L).injective
  letI : Algebra v.Completion w.Completion := sorry -- todo: extract
  Module.finrank v.Completion w.Completion

end localDegree

section localDegree_eq

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)

theorem localDegree_eq
    [Algebra v.Completion w.Completion]
    [ContinuousSMul v.Completion w.Completion]
    [IsScalarTower K v.Completion w.Completion] :
    w.localDegree K = Module.finrank v.Completion w.Completion := by
  rw [localDegree]
  sorry

end localDegree_eq

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
    ∑ w ∈ v.absoluteValuesOver L, Module.finrank v.Completion w.Completion ≤ Module.finrank K L := by
  sorry

end sum

section ramification

end ramification

end AbsoluteValue
