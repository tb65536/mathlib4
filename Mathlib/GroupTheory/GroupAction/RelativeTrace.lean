/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Relative traces for group actions

For a subgroup of finite index, summing the translates of a fixed element over its left cosets
produces an element fixed by the whole group. Normality of the subgroup is not required.
-/

@[expose] public section

namespace Subgroup

variable {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
  (H : Subgroup G)

/-- The action of a coset representative on an `H`-fixed element is independent of the choice. -/
lemma out_smul_eq (x : FixedPoints.addSubmonoid H M) (g : G) :
    (g : G ⧸ H).out • (x : M) = g • (x : M) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, mul_smul]
  change g • (h • (x : M)) = _
  rw [x.property h]

/-- The relative trace from the fixed points of a subgroup of finite index to the fixed points
of the whole group, obtained by summing over left cosets. -/
noncomputable def relativeTrace [Finite (G ⧸ H)] :
    FixedPoints.addSubmonoid H M →+ FixedPoints.addSubmonoid G M := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  have fixed (x : FixedPoints.addSubmonoid H M) :
      ∑ q : G ⧸ H, q.out • (x : M) ∈ FixedPoints.addSubmonoid G M := by
    intro g
    change g • (∑ q : G ⧸ H, q.out • (x : M)) = _
    calc
      g • (∑ q : G ⧸ H, q.out • (x : M)) =
          ∑ q : G ⧸ H, (g • q).out • (x : M) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro q _
        rw [← mul_smul, ← H.out_smul_eq x (g * q.out),
          ← smul_eq_mul, MulAction.Quotient.coe_smul_out]
      _ = ∑ q : G ⧸ H, q.out • (x : M) :=
        Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H ↦ q.out • (x : M))
  exact
    { toFun := fun x ↦ ⟨∑ q : G ⧸ H, q.out • (x : M), fixed x⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y ↦ Subtype.ext (by
        change (∑ q : G ⧸ H, q.out • ((x : M) + (y : M))) =
          (∑ q : G ⧸ H, q.out • (x : M)) + ∑ q : G ⧸ H, q.out • (y : M)
        simp only [smul_add, Finset.sum_add_distrib]) }

lemma relativeTrace_apply [Fintype (G ⧸ H)] (x : FixedPoints.addSubmonoid H M) :
    (H.relativeTrace x : M) = ∑ q : G ⧸ H, q.out • (x : M) := by
  classical
  unfold relativeTrace
  dsimp
  congr 1
  ext
  simp

/-- Relative trace preserves any invariant additive substructure. This applies to additive
submonoids, additive subgroups, submodules, and ideals. -/
lemma relativeTrace_mem [Finite (G ⧸ H)] {S : Type*} [SetLike S M] [AddSubmonoidClass S M]
    (s : S) (hs : ∀ (g : G) (m : M), m ∈ s → g • m ∈ s)
    (x : FixedPoints.addSubmonoid H M) (hx : (x : M) ∈ s) :
    (H.relativeTrace x : M) ∈ s := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  rw [H.relativeTrace_apply]
  exact sum_mem (fun q _ ↦ hs q.out x hx)

/-- Equivariant additive homomorphisms commute with relative trace. -/
lemma map_relativeTrace [Finite (G ⧸ H)] {N : Type*} [AddCommMonoid N]
    [DistribMulAction G N] (f : M →+[G] N)
    (x : FixedPoints.addSubmonoid H M) (y : FixedPoints.addSubmonoid H N)
    (hxy : f (x : M) = (y : N)) :
    f (H.relativeTrace x : M) = (H.relativeTrace y : N) := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  rw [H.relativeTrace_apply, H.relativeTrace_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, hxy]

end Subgroup
