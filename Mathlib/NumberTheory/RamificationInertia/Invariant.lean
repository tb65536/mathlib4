/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Unramified.Finite

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.RingTheory.Ideal.Colon

/-!
# Stable ideals in unramified invariant extensions

An ideal stable under a finite group action on an unramified invariant algebra is extended
from the base ring. The proof uses a separability tensor, a multiplier on which the inertia
subgroup acts trivially, and a sum over left cosets of the inertia subgroup.

The reusable ingredients are `Algebra.FormallyUnramified.equalizerIdempotent`,
`Algebra.FormallyUnramified.linearize`, `Subgroup.relativeTrace`, and
`Subgroup.inertiaIdempotent`. Relative trace is unnormalized and does not require normality
of the subgroup; the inertia idempotent only requires that subgroup to be finite.
-/

@[expose] public section

open scoped Pointwise TensorProduct

namespace Algebra.FormallyUnramified

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [FormallyUnramified A B] [EssFiniteType A B]

/-- The separability tensor evaluated at two algebra maps. Its support is their equalizer. -/
noncomputable def equalizerIdempotent (f g : B →ₐ[A] C) : C :=
  Algebra.TensorProduct.productMap f g (elem A B)

variable (A B) in
/-- The separability tensor is idempotent. -/
lemma isIdempotentElem_elem : IsIdempotentElem (elem A B) := by
  suffices ∀ t : B ⊗[A] B,
      t * elem A B = (Algebra.TensorProduct.lmul' A t ⊗ₜ[A] (1 : B)) * elem A B by
    simpa [IsIdempotentElem, lmul_elem, ← Algebra.TensorProduct.one_def] using this (elem A B)
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [show a ⊗ₜ[A] b = (a ⊗ₜ[A] (1 : B)) * (1 ⊗ₜ[A] b) by simp,
      mul_assoc, one_tmul_mul_elem, ← mul_assoc]
    simp
  | add t₁ t₂ h₁ h₂ => simp only [map_add, TensorProduct.add_tmul, add_mul, h₁, h₂]

lemma isIdempotentElem_equalizerIdempotent (f g : B →ₐ[A] C) :
    IsIdempotentElem (equalizerIdempotent f g) :=
  (isIdempotentElem_elem A B).map (Algebra.TensorProduct.productMap f g)

lemma equalizerIdempotent_mul (f g : B →ₐ[A] C) (b : B) :
    equalizerIdempotent f g * f b = equalizerIdempotent f g * g b := by
  simpa [equalizerIdempotent, mul_comm] using
    congrArg (Algebra.TensorProduct.productMap f g) (one_tmul_mul_elem (R := A) b).symm

@[simp] lemma equalizerIdempotent_self (f : B →ₐ[A] C) : equalizerIdempotent f f = 1 := by
  have h : Algebra.TensorProduct.productMap f f = f.comp (Algebra.TensorProduct.lmul' A) := by
    ext a <;> simp
  simp [equalizerIdempotent, h, lmul_elem]

/-- The equalizer idempotent is one exactly when the two algebra maps agree. -/
@[simp] lemma equalizerIdempotent_eq_one_iff (f g : B →ₐ[A] C) :
    equalizerIdempotent f g = 1 ↔ f = g := by
  constructor
  · intro h
    ext b
    simpa only [h, one_mul] using equalizerIdempotent_mul f g b
  · rintro rfl
    exact equalizerIdempotent_self f

lemma map_equalizerIdempotent {D : Type*} [CommRing D] [Algebra A D]
    (f g : B →ₐ[A] C) (k : C →ₐ[A] D) :
    k (equalizerIdempotent f g) = equalizerIdempotent (k.comp f) (k.comp g) := by
  have h : k.comp (Algebra.TensorProduct.productMap f g) =
      Algebra.TensorProduct.productMap (k.comp f) (k.comp g) := by
    ext a <;> simp
  exact congrArg (fun F : B ⊗[A] B →ₐ[A] D ↦ F (elem A B)) h

lemma mk_equalizerIdempotent_eq_one_iff (f g : B →ₐ[A] C) (Q : Ideal C) :
    Ideal.Quotient.mk Q (equalizerIdempotent f g) = 1 ↔
      (Ideal.Quotient.mkₐ A Q).comp f = (Ideal.Quotient.mkₐ A Q).comp g := by
  rw [← Ideal.Quotient.mkₐ_eq_mk A Q, map_equalizerIdempotent, equalizerIdempotent_eq_one_iff]

lemma mk_equalizerIdempotent_eq_one (f g : B →ₐ[A] C) (Q : Ideal C)
    (h : ∀ b, f b - g b ∈ Q) : Ideal.Quotient.mk Q (equalizerIdempotent f g) = 1 := by
  rw [mk_equalizerIdempotent_eq_one_iff]
  ext b
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (h b)

open Classical in
/-- Modulo a prime ideal, the equalizer idempotent is the indicator that the maps agree. -/
lemma mk_equalizerIdempotent (f g : B →ₐ[A] C) (Q : Ideal C) [Q.IsPrime] :
    Ideal.Quotient.mk Q (equalizerIdempotent f g) =
      if (Ideal.Quotient.mkₐ A Q).comp f = (Ideal.Quotient.mkₐ A Q).comp g then 1 else 0 := by
  rw [← Ideal.Quotient.mkₐ_eq_mk A Q, map_equalizerIdempotent, ← equalizerIdempotent_eq_one_iff]
  split_ifs with h
  · exact h
  · exact (IsIdempotentElem.iff_eq_zero_or_one.mp
      (isIdempotentElem_equalizerIdempotent _ _)).resolve_right h

section Linearize

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module B M] [IsScalarTower A B M]
  [Module A N] [Module B N] [IsScalarTower A B N]

/-- Separability turns a base-linear map into an algebra-linear map. -/
noncomputable def linearize : (M →ₗ[A] N) →ₗ[B] (M →ₗ[B] N) :=
  (LinearMap.lcomp B N (sec A B M)).comp (LinearMap.liftBaseChangeEquiv B).toLinearMap

lemma linearize_apply (f : M →ₗ[A] N) (x : M) :
    linearize (B := B) f x = _root_.TensorProduct.lift ((Algebra.lsmul A A N).toLinearMap.compl₂
      (f.comp ((Algebra.lsmul A A M).toLinearMap.flip x))) (elem A B) := by
  change f.liftBaseChange B (sec A B M x) = _
  simp only [sec, LinearMap.comp_apply, LinearMap.coe_mk, LinearMap.coe_toAddHom,
    LinearMap.flip_apply, TensorProduct.AlgebraTensorModule.mapBilinear_apply]
  induction elem A B using TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.lsmul_apply]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- Separability linearization preserves conditions of mapping one submodule into another. -/
lemma linearize_mem (f : M →ₗ[A] N) (P : Submodule B M) (Q : Submodule B N)
    (hf : ∀ x ∈ P, f x ∈ Q) {x : M} (hx : x ∈ P) : linearize (B := B) f x ∈ Q := by
  rw [linearize_apply]
  induction elem A B using TensorProduct.inductionOn with
  | tmul a b => exact Q.smul_mem a (hf _ (P.smul_mem b hx))
  | add t₁ t₂ h₁ h₂ => simpa only [map_add] using Q.add_mem h₁ h₂

lemma linearize_comp {L : Type*} [AddCommGroup L] [Module A L] [Module B L]
    [IsScalarTower A B L] (f : M →ₗ[A] N) (g : L →ₗ[B] M) :
    linearize (B := B) (f.comp (g.restrictScalars A)) = (linearize (B := B) f).comp g := by
  ext x
  simp only [linearize_apply, LinearMap.comp_apply]
  congr 1
  ext a b
  simp [g.map_smul]

lemma comp_linearize {P : Type*} [AddCommGroup P] [Module A P] [Module B P]
    [IsScalarTower A B P] (g : N →ₗ[B] P) (f : M →ₗ[A] N) :
    linearize (B := B) ((g.restrictScalars A).comp f) = g.comp (linearize (B := B) f) := by
  change (((g.restrictScalars A).comp f).liftBaseChange B).comp (sec A B M) =
    g.comp ((f.liftBaseChange B).comp (sec A B M))
  rw [← LinearMap.liftBaseChange_comp, LinearMap.comp_assoc]

@[simp] lemma linearize_restrictScalars (f : M →ₗ[B] N) :
    linearize (f.restrictScalars A) = f := by
  have h : linearize (B := B) (LinearMap.id (R := A) (M := M)) = LinearMap.id :=
    comp_sec A B M
  simpa only [LinearMap.comp_id, h] using
    comp_linearize f (LinearMap.id (R := A) (M := M))

@[simp] lemma linearize_algHom_apply (f : B →ₐ[A] B) (x : B) :
    linearize (B := B) f.toLinearMap x = equalizerIdempotent (AlgHom.id A B) f * x := by
  have h : linearize (B := B) f.toLinearMap 1 = equalizerIdempotent (AlgHom.id A B) f := by
    rw [linearize_apply]
    change _ = (Algebra.TensorProduct.productMap (AlgHom.id A B) f).toLinearMap (elem A B)
    congr 1
    ext a b
    simp
  simpa only [smul_eq_mul, h, mul_comm, mul_one] using
    (linearize (B := B) f.toLinearMap).map_smul x (1 : B)

end Linearize

end Algebra.FormallyUnramified

namespace Subgroup

section RelativeTrace

variable {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
  (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The unnormalized relative trace from subgroup-fixed points to group-fixed points. -/
noncomputable def relativeTrace : FixedPoints.addSubmonoid H M →+ FixedPoints.addSubmonoid G M where
  toFun x := ⟨∑ q : G ⧸ H, q.out • (x : M), fun g ↦ by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q ↦ ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
    rw [← smul_eq_mul, MulAction.Quotient.mk_smul_out] at hh
    change g • (q.out • (x : M)) = (g • q).out • (x : M)
    simp only [hh, smul_eq_mul, mul_smul, show (h : G) • (x : M) = x from x.property h]⟩
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp [smul_add, Finset.sum_add_distrib])

lemma relativeTrace_apply (x : FixedPoints.addSubmonoid H M) :
    (H.relativeTrace x : M) = ∑ q : G ⧸ H, q.out • (x : M) := rfl

lemma relativeTrace_mem (P : AddSubmonoid M)
    (hP : ∀ (g : G) (x : M), x ∈ P → g • x ∈ P)
    (x : FixedPoints.addSubmonoid H M) (hx : (x : M) ∈ P) :
    (H.relativeTrace x : M) ∈ P :=
  P.sum_mem fun q _ ↦ hP q.out _ hx

/-- Relative trace is linear over scalars fixed by the ambient group. -/
noncomputable def relativeTraceLinearMap {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] :
    FixedPoints.subalgebra A B H →ₗ[A] FixedPoints.subalgebra A B G where
  __ := H.relativeTrace (M := B)
  map_smul' a x := Subtype.ext <|
    (Finset.sum_congr rfl fun q _ ↦ smul_comm q.out a (x : B)).trans Finset.smul_sum.symm

lemma relativeTraceLinearMap_apply {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B]
    (x : FixedPoints.subalgebra A B H) :
    (H.relativeTraceLinearMap (A := A) (B := B) x : B) = ∑ q : G ⧸ H, q.out • (x : B) := rfl

end RelativeTrace

open Algebra.FormallyUnramified

variable {G : Type*} [Group G] (H : Subgroup G) (A : Type*) {B : Type*}
  [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] [Finite H]

/-- The idempotent whose multiples are fixed by a finite subgroup. -/
noncomputable def inertiaIdempotent : B := by
  classical
  letI := Fintype.ofFinite H
  exact ∏ h : H, equalizerIdempotent (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B (h : G))

lemma isIdempotentElem_inertiaIdempotent : IsIdempotentElem (H.inertiaIdempotent A : B) := by
  classical
  let := Fintype.ofFinite H
  rw [IsIdempotentElem, inertiaIdempotent, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun h _ ↦ (isIdempotentElem_equalizerIdempotent _ _).eq

lemma inertiaIdempotent_mul_smul (h : H) (b : B) :
    H.inertiaIdempotent A * (h • b) = H.inertiaIdempotent A * b := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨w, hw⟩ : equalizerIdempotent (AlgHom.id A B)
      (MulSemiringAction.toAlgHom A B (h : G)) ∣ H.inertiaIdempotent A :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  have he := equalizerIdempotent_mul
    (AlgHom.id A B) (MulSemiringAction.toAlgHom A B (h : G)) b
  change _ * b = _ * (h • b) at he
  rw [hw, mul_right_comm, ← he, mul_right_comm]

@[simp] lemma smul_inertiaIdempotent (h : H) : h • (H.inertiaIdempotent A : B) =
    H.inertiaIdempotent A := by
  have h₁ := (H.inertiaIdempotent_mul_smul A h (H.inertiaIdempotent A : B)).trans
    (H.isIdempotentElem_inertiaIdempotent A).eq
  have h₂ : (h • H.inertiaIdempotent A) * H.inertiaIdempotent A =
      h • (H.inertiaIdempotent A : B) := by
    simpa only [smul_mul', smul_smul, mul_inv_cancel, one_smul] using
      congrArg (h • ·) ((H.inertiaIdempotent_mul_smul A h⁻¹ (H.inertiaIdempotent A : B)).trans
        (H.isIdempotentElem_inertiaIdempotent A).eq)
  exact h₂.symm.trans ((mul_comm _ _).trans h₁)

lemma smul_inertiaIdempotent_mul (h : H) (b : B) :
    h • (H.inertiaIdempotent A * b) = H.inertiaIdempotent A * b := by
  rw [smul_mul', smul_inertiaIdempotent, inertiaIdempotent_mul_smul]

/-- The inertia idempotent is congruent to one precisely when the subgroup acts trivially
modulo the ideal. No primality hypothesis is needed. -/
lemma inertiaIdempotent_sub_one_mem_iff (Q : Ideal B) :
    H.inertiaIdempotent A - 1 ∈ Q ↔ H ≤ Q.inertia G := by
  classical
  let := Fintype.ofFinite H
  rw [← Ideal.Quotient.mk_eq_one_iff_sub_mem]
  constructor
  · intro hu h hh
    apply Q.mem_inertia.mpr
    intro b
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa [hu] using congrArg (Ideal.Quotient.mk Q)
      (H.inertiaIdempotent_mul_smul A ⟨h, hh⟩ b)
  · intro hH
    simp only [inertiaIdempotent, map_prod]
    apply Finset.prod_eq_one
    intro h _
    exact mk_equalizerIdempotent_eq_one _ _ Q fun b ↦
      Q.toAddSubgroup.sub_mem_comm_iff.mpr (Q.mem_inertia.mp (hH h.property) b)

variable [Finite (G ⧸ H)]

/-- The multiplier obtained by linearizing relative trace after multiplication by the inertia
idempotent. It is independent of any ideal. -/
noncomputable def descentMultiplier : B := by
  classical
  letI := Fintype.ofFinite (G ⧸ H)
  exact ∑ q : G ⧸ H, equalizerIdempotent (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B q.out) * H.inertiaIdempotent A

end Subgroup

namespace Ideal

variable {B G : Type*} [CommRing B] [Group G]

variable [MulSemiringAction G B]

open Algebra.FormallyUnramified

/-- A fixed element of an ideal lies in the extension of its contraction. -/
lemma mem_map_comap_of_mem_of_fixed {A : Type*} [CommRing A] [Algebra A B]
    [Algebra.IsInvariant A B G] (I : Ideal B) {x : B} (hx : x ∈ I)
    (hfixed : ∀ g : G, g • x = x) : x ∈ (I.comap (algebraMap A B)).map (algebraMap A B) := by
  obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) x hfixed
  exact Ideal.mem_map_of_mem _ hx

variable (A : Type*) [CommRing A] [Algebra A B] [SMulCommClass G A B]
  [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B]

open Classical in
/-- Modulo a prime ideal, the equalizer idempotent of the identity and a group element
is the indicator of membership in the inertia subgroup. -/
lemma Quotient.mk_equalizerIdempotent (Q : Ideal B) [Q.IsPrime] (g : G) :
    Quotient.mk Q (equalizerIdempotent (AlgHom.id A B)
      (MulSemiringAction.toAlgHom A B g)) = if g ∈ Q.inertia G then 1 else 0 := by
  simp [Algebra.FormallyUnramified.mk_equalizerIdempotent, AlgHom.ext_iff,
    Quotient.mk_eq_mk_iff_sub_mem, Q.toAddSubgroup.sub_mem_comm_iff]

/-- The descent multiplier sends a stable ideal into the extension of its contraction. -/
lemma descentMultiplier_mem_colon [Algebra.IsInvariant A B G]
    (H : Subgroup G) [Finite H] [Finite (G ⧸ H)] (I : Ideal B)
    (hI : ∀ g : G, g • I = I) : H.descentMultiplier A ∈
      ((I.comap (algebraMap A B)).map (algebraMap A B)).colon (I : Set B) := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let J := (I.comap (algebraMap A B)).map (algebraMap A B)
  let u : B := H.inertiaIdempotent A
  let U : B →ₗ[A] FixedPoints.subalgebra A B H :=
    (LinearMap.mulLeft A u).codRestrict (FixedPoints.subalgebra A B H).toSubmodule
      (fun b h ↦ H.smul_inertiaIdempotent_mul A h b)
  let T : B →ₗ[A] B := (FixedPoints.subalgebra A B G).val.toLinearMap.comp
    (H.relativeTraceLinearMap.comp U)
  have hT (x : B) (hx : x ∈ I) : T x ∈ J := by
    apply I.mem_map_comap_of_mem_of_fixed (G := G)
    · exact H.relativeTrace_mem I.toAddSubmonoid
        (fun g x hx ↦ hI g ▸ Ideal.smul_mem_pointwise_smul g x I hx)
        (U x) (I.mul_mem_left u hx)
    · exact (H.relativeTraceLinearMap (A := A) (B := B) (U x)).property
  have hT_eq : T = ∑ q : G ⧸ H, (MulSemiringAction.toAlgHom A B q.out).toLinearMap.comp
      ((LinearMap.mulLeft B u).restrictScalars A) := by
    ext b
    change (∑ q : G ⧸ H, q.out • (u * b)) = _
    simp
  have hF (x : B) : linearize (B := B) T x = H.descentMultiplier A * x := by
    rw [hT_eq, map_sum]
    simp [Subgroup.descentMultiplier, linearize_comp, u, Finset.sum_mul, mul_assoc]
  rw [Submodule.mem_colon]
  intro x hx
  simpa only [hF, smul_eq_mul] using linearize_mem T I J hT hx

/-- Modulo a prime ideal, the descent multiplier for its inertia subgroup is one. -/
lemma Quotient.mk_descentMultiplier_inertia (Q : Ideal B) [Q.IsPrime]
    [Finite (Q.inertia G)] [Finite (G ⧸ Q.inertia G)] :
    Quotient.mk Q ((Q.inertia G).descentMultiplier A) = 1 := by
  classical
  let := Fintype.ofFinite (G ⧸ Q.inertia G)
  simpa [Subgroup.descentMultiplier, Quotient.mk_equalizerIdempotent, ite_mul,
    ← SetLike.mem_coe, ← QuotientGroup.preimage_mk_one] using
    (Quotient.mk_eq_one_iff_sub_mem _).mpr
      (((Q.inertia G).inertiaIdempotent_sub_one_mem_iff A Q).mpr le_rfl)

variable {A} in
/-- In an invariant, formally unramified algebra essentially of finite type, every
stable ideal is extended from the base ring. -/
theorem map_comap_eq_of_isInvariant_of_unramified [Finite G] [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ g : G, g • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  classical
  let J := (I.comap (algebraMap A B)).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  suffices J.colon (I : Set B) = ⊤ from (Submodule.colon_eq_top_iff_subset _).mp this
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  let : m.IsMaximal := hm
  have hc_mem := descentMultiplier_mem_colon A (m.inertia G) I hI
  have hc_one := Quotient.mk_descentMultiplier_inertia A (G := G) m
  have hc_zero : Quotient.mk m ((m.inertia G).descentMultiplier A) = 0 :=
    Quotient.eq_zero_iff_mem.mpr (hKm hc_mem)
  exact zero_ne_one (hc_zero.symm.trans hc_one)

end Ideal
