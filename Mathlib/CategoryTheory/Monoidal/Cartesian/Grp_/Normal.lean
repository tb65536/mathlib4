/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_

/-!
# Basic properties of group schemes

-/

@[expose] public section

namespace CategoryTheory.GrpObj

open MonObj MonoidalCategory CartesianMonoidalCategory

variable {X : Type*} [Category* X] [CartesianMonoidalCategory X] {G H : X} [GrpObj G] [GrpObj H]
  (φ : H ⟶ G) [IsMonHom φ]

/-- An `IsMonHom φ : G ⟶ H` is normal if its functor of points has normal ranges. We do not assume
that `φ` is injective, which would correspond to the additional assumption `[Mono φ]`. -/
class IsNormalHom : Prop where
  normal : ∀ S : X, ((yonedaGrp.map (Grp.ofHom φ)).app (.op S)).hom.range.Normal

variable {φ}

theorem isNormalHom_def :
    IsNormalHom φ ↔ ∀ S : X, ((yonedaGrp.map (Grp.ofHom φ)).app (.op S)).hom.range.Normal :=
  ⟨fun h ↦ h.normal, fun h ↦ ⟨h⟩⟩

theorem isNormalHom_iff :
    IsNormalHom φ ↔ ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = whiskerLeft G φ ≫ conj G := by
  rw [isNormalHom_def]
  constructor
  · intro h
    sorry
  · rintro ⟨ψ, hψ⟩ S
    sorry

end CategoryTheory.GrpObj
