/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!

-/

@[expose] public section

open CategoryTheory Limits

section

universe u v

open MonObj

def GrpObj.ofInvertible {C : Type*} [Category* C] (G : C) [CartesianMonoidalCategory C] [MonObj G]
    (h : ∀ (X : C) (f : X ⟶ G), Invertible f) : GrpObj G where
  inv := Yoneda.fullyFaithful.preimage ⟨fun X f ↦ (h X.unop f).invOf, fun X Y f ↦ by
    ext g
    simp_rw [yoneda_obj_obj, types_comp_apply, yoneda_obj_map]
    apply invOf_eq_left_inv -- add `rw` version of this?
    rw [← comp_mul, invOf_mul_self', comp_one]⟩
  left_inv := by
    simp_rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, invOf_mul_self, Hom.one_def]
  right_inv := by
    simp_rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, mul_invOf_self, Hom.one_def]

instance {C J : Type*} [Category.{v} C] [SmallCategory J] [CartesianMonoidalCategory C]
    [HasLimitsOfShape J C] [HasLimitsOfShape J MonCat.{v}] :
    PreservesLimitsOfShape J (yonedaMon (C := C)) := by
  convert preservesLimitsOfShape_of_reflects_of_preserves (J := J) (yonedaMon (C := C))
    ((Functor.whiskeringRight _ _ _).obj (forget MonCat))
  · exact inferInstanceAs (PreservesLimitsOfShape J (Mon.forget C ⋙ yoneda))
  · -- extract this as instance (CategoryTheory/Limits/FunctorCategory), next to
    -- `whiskeringRight_preservesLimitsOfShape` (from `ReflectsLimits` to `ReflectsLimits`)
    apply reflectsLimitsOfShape_of_reflectsIsomorphisms

noncomputable instance {C J : Type*} [Category.{v} C] [Small.{v} J] [SmallCategory J]
    [CartesianMonoidalCategory C] [HasLimitsOfShape J C]
    [HasLimitsOfShape J MonCat] [HasLimitsOfShape J GrpCat] :
    CreatesLimitsOfShape J (Grp.forget₂Mon C) := by
  constructor
  intro F
  let G : Grp C :=
  { X := (limit (F ⋙ Grp.forget₂Mon C)).X
    grp := GrpObj.ofInvertible (limit (F ⋙ Grp.forget₂Mon C)).X fun X f ↦ by
      have : PreservesLimits (yoneda (C := C)) := inferInstance
      let G := yonedaMon (C := C) ⋙ (evaluation _ _).obj (.op X)
      have : (F ⋙ Grp.forget₂Mon C) ⋙ G ≅ (F ⋙ yonedaGrp ⋙ (evaluation _ _).obj (.op X)) ⋙
          forget₂ GrpCat MonCat := by
        rfl
      have h1 := CategoryTheory.preservesLimitIso G (F ⋙ Grp.forget₂Mon C) ≪≫
        HasLimit.isoOfNatIso this ≪≫
        (CategoryTheory.preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ yonedaGrp ⋙ (evaluation Cᵒᵖ GrpCat).obj (Opposite.op X))).symm
      suffices Invertible ((h1.symm.hom.hom) (h1.hom.hom f)) by
        rwa [Iso.symm_hom, Iso.hom_inv_id_apply] at this
      suffices Invertible (h1.hom.hom f) by
        exact this.map h1.symm.hom.hom
      refine @invertibleOfGroup _ ?_ _ }
  apply createsLimitOfFullyFaithfulOfIso G
  rfl

noncomputable instance {C J : Type*} [Category.{v} C] [Small.{v} J] [SmallCategory J]
    [CartesianMonoidalCategory C] [HasLimitsOfShape J C]
    [HasLimitsOfShape J MonCat] [HasLimitsOfShape J GrpCat] :
    CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs (CreatesLimitsOfShape J (Grp.forget₂Mon C ⋙ Mon.forget C))

instance foo {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    [HasLimitsOfShape WalkingParallelPair C] : HasKernels (Grp C) := by
  constructor
  intro X Y f
  exact (hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (Grp.forget C)).has_limit
    (parallelPair f 0)

end

namespace AlgebraicGeometry

variable {X : Scheme}

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasInitial (Grp (Over X)) := inferInstance

instance : HasTerminal (Grp (Over X)) := inferInstance

instance : HasZeroObject (Grp (Over X)) := inferInstance

noncomputable instance : HasZeroMorphisms (Grp (Over X)) := inferInstance

instance : HasKernels (Grp (Over X)) := inferInstance

-- todo: define kernels in the unbundled setting

-- kernel is predicate on morphism (immersion + monoid hom) defined pointwise, yoneda-style
--  iff (conjugation factors through)

-- wedhorn Algebraic Geometry II. Cohomology of coherent sheaves

end AlgebraicGeometry
