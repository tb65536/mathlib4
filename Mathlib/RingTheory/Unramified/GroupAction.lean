/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Inertia in unramified algebras

A finite inertia subgroup acts trivially on a principal neighborhood of its prime. A uniform
multiplier outside the prime takes the whole algebra into the fixed points of inertia.
-/

@[expose] public section

namespace Algebra.FormallyUnramified

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [FormallyUnramified A B] [EssFiniteType A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

include A in
/-- In an unramified algebra, finite inertia fixes a principal neighborhood of its prime.
The multiplier can be chosen so that multiplication by it takes values in the inertia-fixed ring. -/
lemma exists_notMem_inertia_smul_mul_eq (P : Ideal B) [P.IsPrime] [Finite (P.inertia G)] :
    ∃ a ∉ P, ∀ (h : P.inertia G) (b : B), h • (a * b) = a * b := by
  apply P.exists_notMem_smul_mul_eq
    (fun h ↦ P.inertia_le_stabilizer h.property)
  intro h
  let f := MulSemiringAction.toAlgHom A B (h : G)
  refine ⟨TensorProduct.productMap (AlgHom.id A B) f (elem A B), ?_, ?_⟩
  · apply (productMap_elem_notMem_iff P (AlgHom.id A B) f).mpr
    intro b
    simpa only [f, AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, neg_sub] using
      P.neg_mem (h.property b)
  · intro b
    exact productMap_elem_mul (AlgHom.id A B) f b

end Algebra.FormallyUnramified
