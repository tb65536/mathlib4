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

-- PRed
def GrpObj.ofInvertible {C : Type*} [Category* C] (G : C) [CartesianMonoidalCategory C] [MonObj G]
    (h : ∀ (X : C) (f : X ⟶ G), Invertible f) : GrpObj G where
  inv := Yoneda.fullyFaithful.preimage ⟨fun X f ↦ (h X.unop f).invOf, fun X Y f ↦ by
    ext g
    simp_rw [yoneda_obj_obj, types_comp_apply, yoneda_obj_map]
    apply invOf_eq_left_inv -- add `rw` version of this?
    rw [← comp_mul, invOf_mul_self', comp_one]⟩
  left_inv := by
    rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, invOf_mul_self, Hom.one_def]
  right_inv := by
    rw [Yoneda.fullyFaithful_preimage, ← Hom.mul_def, mul_invOf_self, Hom.one_def]

-- PRed
instance whiskeringRight_reflectsLimitsOfShape {C : Type*} [Category* C] {D : Type*}
    [Category* D] {E : Type*} [Category* E] {J : Type*} [Category* J]
    [HasLimitsOfShape J D] (F : D ⥤ E) [PreservesLimitsOfShape J F] [F.ReflectsIsomorphisms] :
    ReflectsLimitsOfShape J ((Functor.whiskeringRight C D E).obj F) :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms

instance {C J : Type*} [Category.{v} C] [SmallCategory J] [CartesianMonoidalCategory C]
    [HasLimitsOfShape J C] [HasLimitsOfShape J MonCat.{v}] :
    PreservesLimitsOfShape J (yonedaMon (C := C)) := by
  have : PreservesLimitsOfShape J
      (yonedaMon ⋙ (Functor.whiskeringRight Cᵒᵖ MonCat (Type v)).obj (forget MonCat)) :=
    inferInstanceAs (PreservesLimitsOfShape J (Mon.forget C ⋙ yoneda))
  exact preservesLimitsOfShape_of_reflects_of_preserves (J := J) (yonedaMon (C := C))
    ((Functor.whiskeringRight _ _ _).obj (forget MonCat))

noncomputable instance {C J : Type*} [Category.{v} C] [Small.{v} J] [SmallCategory J]
    [CartesianMonoidalCategory C] [HasLimitsOfShape J C]
    [HasLimitsOfShape J MonCat] [HasLimitsOfShape J GrpCat] :
    CreatesLimitsOfShape J (Grp.forget₂Mon C) := by
  constructor
  intro F
  let G : Grp C :=
  { X := (limit (F ⋙ Grp.forget₂Mon C)).X
    grp := GrpObj.ofInvertible (limit (F ⋙ Grp.forget₂Mon C)).X fun X f ↦ by
      let e := CategoryTheory.preservesLimitIso
        (yonedaMon (C := C) ⋙ (evaluation _ _).obj (.op X)) (F ⋙ Grp.forget₂Mon C) ≪≫
        (CategoryTheory.preservesLimitIso (forget₂ GrpCat MonCat)
        (F ⋙ yonedaGrp ⋙ (evaluation Cᵒᵖ GrpCat).obj (Opposite.op X))).symm
      rw [← e.hom_inv_id_apply f, ← e.symm_hom]
      suffices hf : Invertible (e.hom.hom f) from hf.map e.symm.hom.hom
      exact @invertibleOfGroup  _ ?_ (e.hom.hom f) }
  exact createsLimitOfFullyFaithfulOfIso G (Iso.refl G.toMon)

noncomputable instance {C J : Type*} [Category.{v} C] [Small.{v} J] [SmallCategory J]
    [CartesianMonoidalCategory C] [HasLimitsOfShape J C]
    [HasLimitsOfShape J MonCat] [HasLimitsOfShape J GrpCat] :
    CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs (CreatesLimitsOfShape J (Grp.forget₂Mon C ⋙ Mon.forget C))

instance {C : Type*} [Category* C] [CartesianMonoidalCategory C]
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
