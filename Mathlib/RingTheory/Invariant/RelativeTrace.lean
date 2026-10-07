/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.RelativeTrace
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Relative traces in invariant extensions

The relative trace of an element of a stable ideal belongs to the extension of its contraction
to the fixed ring. Only the subgroup used for the trace needs to have finite index.
-/

@[expose] public section

open scoped Pointwise

namespace Algebra.IsInvariant

variable {A B G : Type*} [CommSemiring A] [CommSemiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B] [IsInvariant A B G]

/-- The relative trace of an element of a stable ideal belongs to the ideal extended from its
contraction to the fixed ring. -/
lemma relativeTrace_mem_map_comap (H : Subgroup G) [Finite (G ⧸ H)]
    {I : Ideal B} (hI : ∀ g : G, g • I = I)
    (x : FixedPoints.addSubmonoid H B) (hx : (x : B) ∈ I) :
    (H.relativeTrace x : B) ∈
      Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) I) := by
  have htrace := H.relativeTrace_mem I (fun g b hb ↦ by
    simpa only [hI g] using Ideal.smul_mem_pointwise_smul g b I hb) x hx
  obtain ⟨a, ha⟩ := IsInvariant.isInvariant (A := A) (G := G)
    (H.relativeTrace x : B) (H.relativeTrace x).property
  rw [← ha] at htrace ⊢
  exact Ideal.mem_map_of_mem (algebraMap A B) htrace

end Algebra.IsInvariant
