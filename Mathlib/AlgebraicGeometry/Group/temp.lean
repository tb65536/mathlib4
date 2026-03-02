/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp_

/-!

-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (G H : Over X) [GrpObj G] (φ : G ⟶ H)

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasFiniteProducts (Grp (Over X)) := inferInstance

instance : HasTerminal (Grp (Over X)) := inferInstance

#synth HasInitial (Grp (Over X))

instance : HasZeroObject (Grp (Over X)) := inferInstance

instance : HasZeroMorphisms (Grp (Over X)) := inferInstance

instance : HasKernels (Grp (Over X)) := inferInstance

end AlgebraicGeometry
