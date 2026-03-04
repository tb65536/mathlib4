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
  (φ : G ⟶ H) [IsMonHom φ]

def _root_.CategoryTheory.Grp.ofHom : Grp.mk G ⟶ Grp.mk H :=
  Grp.homMk φ

/-- An `IsMonHom φ : G ⟶ H` is normal if its functor of points has normal ranges. We do not assume
that `φ` is injective, which would correspond to the additional assumption `[Mono φ]`. -/
class IsNormalHom : Prop where
  normal : ∀ S : X, ((yonedaGrp.map (Grp.ofHom φ)).app (.op S)).hom.range.Normal

def conj : G ⊗ G ⟶ G :=
  fst _ _ * snd _ _ * (fst _ _)⁻¹

/- conj `G × G → G` restricted to `G × H` factors through `H`. -/

end CategoryTheory.GrpObj
