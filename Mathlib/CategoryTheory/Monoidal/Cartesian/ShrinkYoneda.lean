/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Monoidal.Grp_
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# The YonedaMon functor for locally small categories

Let `C` be a locally `w`-small category. We define the YonedaMon embeddings
`shrinkYonedaMon : Mon C ⥤ Cᵒᵖ ⥤ Type w` and `shrinkYonedaGrp : Mon C ⥤ Cᵒᵖ ⥤ Type w`.

-/

@[expose] public section

universe w w' v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [CartesianMonoidalCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- The YonedaMon embedding `C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`. -/
@[simps -isSimp obj map, pp_with_univ]
noncomputable def shrinkYonedaMonMon :
    Mon C ⥤ Cᵒᵖ ⥤ MonCat.{w} where
  obj X :=
  { obj Y := MonCat.of (Shrink (Y.unop ⟶ X.1))
    map f := sorry }
  map f := FunctorToTypes.shrinkMap (yonedaMon.map f)

/-- The type `(shrinkYonedaMon.obj X).obj Y` is equivalent to `Y.unop ⟶ X`. -/
noncomputable def shrinkYonedaMonObjObjEquiv {X : C} {Y : Cᵒᵖ} :
    ((shrinkYonedaMon.{w}.obj X).obj Y) ≃ (Y.unop ⟶ X) :=
  (equivShrink _).symm

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm
    {X : C} {Y Y' : Cᵒᵖ} (g : Y ⟶ Y') (f : Y.unop ⟶ X) :
    (shrinkYonedaMon.obj _).map g (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (g.unop ≫ f) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

lemma shrinkYonedaMonObjObjEquiv_symm_comp {X Y Y' : C} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    shrinkYonedaMonObjObjEquiv.symm (g ≫ f) =
    (shrinkYonedaMon.obj _).map g.op (shrinkYonedaMonObjObjEquiv.symm f) :=
  (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm g.op f).symm

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMon_map_app_shrinkYonedaMonObjObjEquiv_symm
    {X X' : C} {Y : Cᵒᵖ} (f : Y.unop ⟶ X) (g : X ⟶ X') :
    (shrinkYonedaMon.map g).app _ (shrinkYonedaMonObjObjEquiv.symm f) =
      shrinkYonedaMonObjObjEquiv.symm (f ≫ g) := by
  simp [shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- The type of natural transformations `shrinkYonedaMon.{w}.obj X ⟶ P`
with `X : C` and `P : Cᵒᵖ ⥤ Type w` is equivalent to `P.obj (op X)`. -/
noncomputable def shrinkYonedaMonEquiv {X : C} {P : Cᵒᵖ ⥤ Type w} :
    (shrinkYonedaMon.{w}.obj X ⟶ P) ≃ P.obj (op X) where
  toFun τ := τ.app _ (equivShrink.{w} _ (𝟙 X))
  invFun x :=
    { app Y f := P.map ((equivShrink.{w} _).symm f).op x
      naturality Y Z g := by ext; simp [shrinkYonedaMon] }
  left_inv τ := by
    ext Y f
    obtain ⟨f, rfl⟩ := (equivShrink _).surjective f
    simpa [shrinkYonedaMon] using congr_fun (τ.naturality f.op).symm (equivShrink _ (𝟙 X))
  right_inv x := by simp

set_option backward.isDefEq.respectTransparency false in
lemma map_shrinkYonedaMonEquiv {X Y : C} {P : Cᵒᵖ ⥤ Type w} (f : shrinkYonedaMon.obj X ⟶ P)
    (g : Y ⟶ X) : P.map g.op (shrinkYonedaMonEquiv f) =
      f.app (op Y) (shrinkYonedaMonObjObjEquiv.symm g) := by
  simp [shrinkYonedaMonObjObjEquiv, shrinkYonedaMonEquiv, shrinkYonedaMon,
    ← FunctorToTypes.naturality]

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMonEquiv_shrinkYonedaMon_map {X Y : C} (f : X ⟶ Y) :
    shrinkYonedaMonEquiv (shrinkYonedaMon.{w}.map f) = shrinkYonedaMonObjObjEquiv.symm f := by
  simp [shrinkYonedaMonEquiv, shrinkYonedaMon, shrinkYonedaMonObjObjEquiv]

lemma shrinkYonedaMonEquiv_comp {X : C} {P Q : Cᵒᵖ ⥤ Type w} (α : shrinkYonedaMon.obj X ⟶ P)
    (β : P ⟶ Q) :
    shrinkYonedaMonEquiv (α ≫ β) = β.app _ (shrinkYonedaMonEquiv α) := by
  simp [shrinkYonedaMonEquiv]

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaMonEquiv_naturality {X Y : C} {P : Cᵒᵖ ⥤ Type w}
    (f : shrinkYonedaMon.obj X ⟶ P) (g : Y ⟶ X) :
    P.map g.op (shrinkYonedaMonEquiv f) = shrinkYonedaMonEquiv (shrinkYonedaMon.map g ≫ f) := by
  simpa [shrinkYonedaMonEquiv, shrinkYonedaMon]
    using congr_fun (f.naturality g.op).symm ((equivShrink _) (𝟙 _))

@[reassoc]
lemma shrinkYonedaMonEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {P : Cᵒᵖ ⥤ Type w} (t : P.obj X) :
    shrinkYonedaMonEquiv.symm (P.map f t) =
      shrinkYonedaMon.map f.unop ≫ shrinkYonedaMonEquiv.symm t :=
  shrinkYonedaMonEquiv.injective (by
    obtain ⟨t, rfl⟩ := shrinkYonedaMonEquiv.surjective t
    rw [← shrinkYonedaMonEquiv_naturality]
    simp)

lemma shrinkYonedaMonEquiv_symm_app_shrinkYonedaMonObjObjEquiv_symm {X : C} {P : Cᵒᵖ ⥤ Type w}
    (s : P.obj (op X)) {Y : C} (f : Y ⟶ X) :
    (shrinkYonedaMonEquiv.symm s).app (op Y) (shrinkYonedaMonObjObjEquiv.symm f) =
      P.map f.op s := by
  obtain ⟨g, rfl⟩ := shrinkYonedaMonEquiv.surjective s
  simp [map_shrinkYonedaMonEquiv]

variable (C) in
/-- The functor `shrinkYonedaMon : C ⥤ Cᵒᵖ ⥤ Type w` for a locally `w`-small category `C`
is fully faithful. -/
noncomputable def fullyFaithfulShrinkYonedaMon :
    (shrinkYonedaMon.{w} (C := C)).FullyFaithful where
  preimage f := shrinkYonedaMonObjObjEquiv (shrinkYonedaMonEquiv f)
  map_preimage f := by
    obtain ⟨f, rfl⟩ := shrinkYonedaMonEquiv.symm.surjective f
    cat_disch
  preimage_map f := by simp [shrinkYonedaMonEquiv_shrinkYonedaMon_map]

instance : (shrinkYonedaMon.{w} (C := C)).Faithful := (fullyFaithfulShrinkYonedaMon C).faithful

instance : (shrinkYonedaMon.{w} (C := C)).Full := (fullyFaithfulShrinkYonedaMon C).full

/-- `uliftYonedaMon` identifies to `shrinkYonedaMon`. -/
noncomputable def uliftYonedaMonIsoShrinkYonedaMon :
    uliftYonedaMon.{w'} (C := C) ≅ shrinkYonedaMon.{max w' v} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans shrinkYonedaMonObjObjEquiv.symm).toIso) (fun f ↦ by
      ext
      exact (shrinkYonedaMon_obj_map_shrinkYonedaMonObjObjEquiv_symm _ _).symm)) (fun g ↦ by
      ext
      exact (shrinkYonedaMon_map_app_shrinkYonedaMonObjObjEquiv_symm _ _).symm)

end CategoryTheory
