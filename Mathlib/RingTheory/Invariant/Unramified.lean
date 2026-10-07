/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib Contributors
-/
module

public import Mathlib.RingTheory.Invariant.RelativeTrace
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Unramified.GroupAction

/-!
# Ideal descent in unramified invariant extensions

A stable ideal in an unramified algebra with a finite group action is extended from the fixed ring.
The proof works prime by prime: inertia fixes a neighborhood of the prime, and a relative trace
from inertia gives a multiplier outside the prime taking the ideal into its extension from the base.
Faithfulness of the action and injectivity of the algebra map are not required.
-/

@[expose] public section

open scoped Pointwise TensorProduct

namespace Algebra.IsInvariant

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [IsInvariant A B G]

/-- A stable ideal in an unramified invariant extension is extended from the base ring. -/
theorem map_comap_eq_of_unramified [Algebra.Unramified A B]
    {I : Ideal B} (hI : ∀ g : G, g • I = I) :
    Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) I) = I := by
  classical
  let e (g : G) : B := Algebra.TensorProduct.productMap (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B g) (FormallyUnramified.elem A B)
  let J := Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) I)
  apply le_antisymm Ideal.map_comap_le
  intro z hz
  apply Ideal.mem_of_localization_maximal
  intro P hP
  have := hP
  let H := P.inertia G
  let := Fintype.ofFinite (G ⧸ H)
  let π := Ideal.Quotient.mk P
  obtain ⟨a, ha, hfix⟩ :=
    FormallyUnramified.exists_notMem_inertia_smul_mul_eq (A := A) (G := G) P
  let aH (b : B) : FixedPoints.addSubmonoid H B := ⟨a * b, fun h ↦ hfix h b⟩
  -- The relative trace takes `I` into its extension from the invariant ring.
  let T : B →ₗ[A] B := ∑ q : G ⧸ H,
    (q.out • a) • (MulSemiringAction.toAlgHom A B q.out).toLinearMap
  have hT (b : B) : T b = (H.relativeTrace (aH b) : B) := by
    simp [T, H.relativeTrace_apply, aH, smul_mul']
  have hTJ (b : B) (hb : b ∈ I) : T b ∈ J := by
    rw [hT]
    exact relativeTrace_mem_map_comap H hI (aH b) (I.mul_mem_left a hb)
  -- Averaging makes the trace `B`-linear while preserving this containment.
  let F := FormallyUnramified.average A B T
  let r := F 1
  have hFz : F z = r * z := by
    simpa only [smul_eq_mul, mul_one, mul_comm] using F.map_smul z (1 : B)
  have hrz : r * z ∈ J := by
    rw [← hFz]
    exact FormallyUnramified.average_mem A B T I J hTJ hz
  have hr_sum : r = ∑ q : G ⧸ H, e q.out * q.out • a := by
    simp [r, F, T, FormallyUnramified.average_toLinearMap, e, mul_comm]
  -- The separability element detects which translates belong to inertia.
  have he_one (g : G) (hg : g ∈ H) : π (e g) = 1 := by
    apply (FormallyUnramified.quotient_productMap_elem_eq_one_iff P _ _).mpr
    intro b
    simpa only [AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, neg_sub] using
      P.neg_mem (hg b)
  have he_mem (g : G) (hg : g ∉ H) : e g ∈ P := by
    by_contra heg
    apply hg
    intro b
    change g • b - b ∈ P
    simpa only [AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, neg_sub] using
      P.neg_mem ((FormallyUnramified.productMap_elem_notMem_iff P _ _).mp heg b)
  have hqH (q : G ⧸ H) : q.out ∈ H ↔ q = (1 : G) := by
    simpa only [inv_one, one_mul, QuotientGroup.out_eq', eq_comm] using
      (QuotientGroup.eq (s := H) (a := (1 : G)) (b := q.out)).symm
  -- Modulo `P`, only the identity coset contributes to the multiplier.
  have hr : π r = π a := by
    rw [hr_sum, map_sum]
    rw [Finset.sum_eq_single (↑(1 : G) : G ⧸ H)]
    · rw [map_mul, he_one _ ((hqH _).mpr rfl), one_mul]
      apply congrArg π
      simpa only [aH, mul_one, one_smul] using H.out_smul_eq (aH 1) 1
    · intro q _ hq
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (he_mem _ ((hqH _).not.mpr hq)),
        zero_mul]
    · simp
  have hrP : r ∉ P := by
    intro hrP
    apply ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← hr]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hrP
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl
    (Localization.AtPrime P) J z).mpr ⟨r, hrP, hrz⟩

end Algebra.IsInvariant
