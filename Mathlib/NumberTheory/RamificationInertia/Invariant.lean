/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!

-/

public section

open Pointwise

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]  [Algebra.Unramified A B]
  [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- If `B / A` is unramified with Galois group `G`, then any ideal `I` of `B` that is stable under
`G` satisfies `(I ∩ A) B = I`. -/
theorem map_comap_eq_of_unramified {I : Ideal B} (hI : ∀ σ : G, σ • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  sorry
