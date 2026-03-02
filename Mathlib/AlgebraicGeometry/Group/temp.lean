/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!

-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (G H : Over X) [GrpObj G] (φ : G ⟶ H)

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasInitial (Grp (Over X)) := inferInstance

instance : HasTerminal (Grp (Over X)) := inferInstance

instance : HasZeroObject (Grp (Over X)) := inferInstance

noncomputable instance : HasZeroMorphisms (Grp (Over X)) := inferInstance

variable {C J : Type*} [Category* C] [SmallCategory J]

instance [SemiCartesianMonoidalCategory C] [HasLimitsOfShape WalkingParallelPair C] :
    HasKernels (Mon C) :=
  inferInstance

open MonObj

def tada (G : C) [CartesianMonoidalCategory C] [MonObj G] (h : ∀ (X : C) (f : X ⟶ G), Invertible f) :
    GrpObj G where
  inv := Yoneda.fullyFaithful.preimage ⟨fun X f ↦ (h X.unop f).invOf, fun X Y f ↦ by
    ext g
    simp only [yoneda_obj_obj, types_comp_apply, yoneda_obj_map]
    apply invOf_eq_left_inv
    rw [← comp_mul, invOf_mul_self', comp_one]⟩
  left_inv := by
    sorry
  right_inv := by
    sorry

noncomputable instance [CartesianMonoidalCategory C] [HasLimitsOfShape J C] :
    CreatesLimitsOfShape J (Grp.forget₂Mon C) := by
  constructor
  intro F
  let G : Grp C :=
  { X := (CategoryTheory.Mon.limit (F ⋙ Grp.forget₂Mon C)).X
    grp := by
      apply tada
      intro X f
      sorry }
  apply createsLimitOfFullyFaithfulOfIso G

noncomputable instance [CartesianMonoidalCategory C] [HasLimitsOfShape J C] :
    CreatesLimitsOfShape J (Grp.forget C) :=
  inferInstanceAs (CreatesLimitsOfShape J (Grp.forget₂Mon C ⋙ Mon.forget C))

instance [CartesianMonoidalCategory C] [HasLimitsOfShape WalkingParallelPair C] :
    HasKernels (Grp C) := by
  infer_instance
  sorry

instance : HasKernels (Grp (Over X)) := inferInstance



end AlgebraicGeometry
