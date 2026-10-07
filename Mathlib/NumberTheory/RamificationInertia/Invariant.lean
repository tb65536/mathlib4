/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Unramified.Finite

import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.RingTheory.Ideal.Colon

/-!
# Stable ideals in unramified invariant extensions

An ideal stable under a finite group action on an unramified invariant algebra is extended
from the base ring. The proof uses a separability tensor, a multiplier on which the inertia
subgroup acts trivially, and a sum over left cosets of the inertia subgroup.

We also prove that congruent maps out of an unramified algebra agree after multiplication
by an element congruent to one, and that a sum of translates of a subgroup-fixed element
over left cosets is fixed by the whole group.
-/

public section

open scoped Pointwise TensorProduct

namespace Algebra.FormallyUnramified

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [FormallyUnramified A B] [EssFiniteType A B]

/-- Two maps out of an unramified algebra which agree modulo an ideal agree after
multiplication by an element congruent to one modulo that ideal. -/
theorem exists_mul_eq_of_sub_mem (f g : B →ₐ[A] C) (Q : Ideal C)
    (h : ∀ b, f b - g b ∈ Q) :
    ∃ u : C, u - 1 ∈ Q ∧ ∀ b, u * f b = u * g b := by
  let μ := Algebra.TensorProduct.productMap f g
  refine ⟨μ (elem A B), ?_, ?_⟩
  · rw [← Ideal.Quotient.mk_eq_one_iff_sub_mem]
    have he : ∀ t : B ⊗[A] B,
        Ideal.Quotient.mk Q (μ t) =
          Ideal.Quotient.mk Q (f (Algebra.TensorProduct.lmul' A t)) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [μ, Algebra.TensorProduct.productMap_apply_tmul,
          Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
        rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (h b)]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [he, lmul_elem, map_one, map_one]
  · intro b
    have he := congrArg μ (one_tmul_mul_elem (R := A) b)
    simp only [map_mul, μ, Algebra.TensorProduct.productMap_apply_tmul, map_one,
      one_mul, mul_one] at he
    simpa only [mul_comm] using he.symm

end Algebra.FormallyUnramified

namespace Subgroup

variable {G M : Type*} [Group G] [AddCommMonoid M] [DistribMulAction G M]
  (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Summing the translates of an `H`-fixed element over left cosets gives a `G`-fixed
element. No normality assumption on `H` is needed. -/
theorem smul_sum_smul_out (x : M) (hx : ∀ h : H, h • x = x) (g : G) :
    g • (∑ q : G ⧸ H, q.out • x) = ∑ q : G ⧸ H, q.out • x := by
  classical
  have he (q : G ⧸ H) : (g • q).out • x = g • (q.out • x) := by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
    rw [show (QuotientGroup.mk (g * q.out) : G ⧸ H) = g • q by
      simpa only [smul_eq_mul] using MulAction.Quotient.mk_smul_out H g q] at hh
    rw [hh, mul_smul, mul_smul, show (h : G) • x = x from hx h]
  simp_rw [Finset.smul_sum, ← he]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ ↦ rfl)

end Subgroup

namespace Ideal

variable {B G : Type*} [CommRing B] [Group G] [Finite G] [MulSemiringAction G B]

/-- For a finite group acting trivially modulo `Q`, an unramified algebra has an element
congruent to one modulo `Q` whose multiples are all fixed by the group. -/
theorem exists_smul_mul_eq_of_inertia_eq_top (A : Type*) [CommRing A] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] [SMulCommClass G A B]
    (Q : Ideal B) (hQ : Q.inertia G = ⊤) :
    ∃ u : B, u - 1 ∈ Q ∧ ∀ (g : G) (b : B), g • (u * b) = u * b := by
  classical
  let := Fintype.ofFinite G
  have hg (g : G) (b : B) : g • b - b ∈ Q :=
    (Q.mem_inertia.mp (hQ ▸ Subgroup.mem_top g)) b
  have hex (g : G) : ∃ v : B, v - 1 ∈ Q ∧ ∀ b, v * (g • b) = v * b :=
    Algebra.FormallyUnramified.exists_mul_eq_of_sub_mem
      (MulSemiringAction.toAlgHom A B g) (AlgHom.id A B) Q (hg g)
  choose v hv hv' using hex
  let s := ∏ g : G, v g
  let u := ∏ g : G, g • s
  have hs : Ideal.Quotient.mk Q s = 1 := by
    simp only [s, map_prod, ← Ideal.Quotient.mk_eq_one_iff_sub_mem] at hv ⊢
    simp only [hv, Finset.prod_const_one]
  have hu : Ideal.Quotient.mk Q u = 1 := by
    have hg' (g : G) : Ideal.Quotient.mk Q (g • s) = 1 :=
      ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hg g s)).trans hs
    simp [u, map_prod, hg']
  refine ⟨u, (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp hu, ?_⟩
  intro g b
  have hsu : s ∣ u := by
    simpa only [one_smul] using
      (Finset.dvd_prod_of_mem (fun g : G ↦ g • s) (Finset.mem_univ (1 : G)))
  have hvs : v g ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
  obtain ⟨w, hw⟩ := hvs.trans hsu
  rw [smul_mul', show g • u = u from Finset.smul_prod_perm s g]
  rw [hw]
  linear_combination w * hv' g b

/-- In an invariant, formally unramified algebra essentially of finite type, every
stable ideal is extended from the base ring. -/
theorem map_comap_eq_of_isInvariant_of_formallyUnramified
    {A : Type*} [CommRing A] [Algebra A B] [SMulCommClass G A B]
    [Algebra.IsInvariant A B G] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType A B] (I : Ideal B)
    (hI : ∀ (g : G) (x : B), x ∈ I → g • x ∈ I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  classical
  let := Fintype.ofFinite G
  let J := (I.comap (algebraMap A B)).map (algebraMap A B)
  apply le_antisymm Ideal.map_comap_le
  suffices J.colon (I : Set B) = ⊤ by
    exact (Submodule.colon_eq_top_iff_subset _).mp this
  by_contra hJ
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal (J.colon (I : Set B)) hJ
  let : m.IsMaximal := hm
  let H := m.inertia G
  let := Fintype.ofFinite H
  let := Fintype.ofFinite (G ⧸ H)
  -- A separability tensor distinguishes the inertia coset from the other cosets.
  let μ (g : G) := Algebra.TensorProduct.productMap (AlgHom.id A B)
    (MulSemiringAction.toAlgHom A B g)
  let d (g : G) := μ g (Algebra.FormallyUnramified.elem A B)
  have hd_mul (g : G) (x : B) : d g * (g • x) = d g * x := by
    have he := congrArg (μ g)
      (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) x)
    simpa only [μ, map_mul, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
      MulSemiringAction.toAlgHom_apply, map_one, one_mul, mul_one, d, mul_comm] using he
  have hd_one (g : G) (hg : g ∈ H) : Ideal.Quotient.mk m (d g) = 1 := by
    have hg' (x : B) : Ideal.Quotient.mk m (g • x) = Ideal.Quotient.mk m x :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (m.mem_inertia.mp hg x)
    have he (t : B ⊗[A] B) : Ideal.Quotient.mk m (μ g t) =
        Ideal.Quotient.mk m (Algebra.TensorProduct.lmul' A t) := by
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [μ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
          MulSemiringAction.toAlgHom_apply, Algebra.TensorProduct.lmul'_apply_tmul,
          map_mul, hg']
      | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    change Ideal.Quotient.mk m (μ g (Algebra.FormallyUnramified.elem A B)) = 1
    rw [he, Algebra.FormallyUnramified.lmul_elem, map_one]
  have hd_zero (g : G) (hg : g ∉ H) : Ideal.Quotient.mk m (d g) = 0 := by
    have hg' : ¬ ∀ x : B, g • x - x ∈ m := fun h ↦ hg (m.mem_inertia.mpr h)
    obtain ⟨x, hx⟩ := not_forall.mp hg'
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ((inferInstance : m.IsPrime).mem_or_mem (by
      rw [mul_sub, hd_mul, sub_self]
      exact m.zero_mem)).resolve_right hx
  -- Kill the inertia action on a principal ideal without dividing by its order.
  have hH : m.inertia H = ⊤ := by
    ext h
    simp only [Subgroup.mem_top, iff_true]
    exact m.mem_inertia.mpr (m.mem_inertia.mp h.property)
  obtain ⟨u, hu, hu_fixed⟩ := m.exists_smul_mul_eq_of_inertia_eq_top A hH
  have hu_one : Ideal.Quotient.mk m u = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr hu
  let c := ∑ q : G ⧸ H, d q.out * (q.out • u)
  have hc_mem : c ∈ J.colon (I : Set B) := by
    rw [Submodule.mem_colon]
    intro x hx
    have htrace (b : B) : (∑ q : G ⧸ H, q.out • (u * b * x)) ∈ J := by
      have hfixed (h : H) : h • (u * b * x) = u * b * x := by
        simpa only [mul_assoc] using hu_fixed h (b * x)
      obtain ⟨z, hz⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G)
        (∑ q : G ⧸ H, q.out • (u * b * x))
        (H.smul_sum_smul_out _ hfixed)
      rw [← hz]
      apply Ideal.mem_map_of_mem
      rw [Ideal.mem_comap, hz]
      exact I.sum_mem fun q _ ↦ hI q.out _ (I.mul_mem_left _ hx)
    have he (t : B ⊗[A] B) :
        (∑ q : G ⧸ H, μ q.out t * (q.out • u) * (q.out • x)) ∈ J := by
      induction t using TensorProduct.inductionOn with
      | tmul a b =>
        have heq : (∑ q : G ⧸ H, μ q.out (a ⊗ₜ[A] b) *
            (q.out • u) * (q.out • x)) = a * ∑ q : G ⧸ H, q.out • (u * b * x) := by
          simp only [μ, Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply,
            MulSemiringAction.toAlgHom_apply, smul_mul', Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _
          ring
        rw [heq]
        exact J.mul_mem_left _ (htrace b)
      | add t₁ t₂ h₁ h₂ =>
        simpa only [map_add, add_mul, Finset.sum_add_distrib] using J.add_mem h₁ h₂
    have heq : c * x = ∑ q : G ⧸ H, d q.out * (q.out • u) * (q.out • x) := by
      rw [show c = ∑ q : G ⧸ H, d q.out * (q.out • u) from rfl, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      calc
        d q.out * (q.out • u) * x = (q.out • u) * (d q.out * x) := by ring
        _ = (q.out • u) * (d q.out * (q.out • x)) := by rw [hd_mul]
        _ = d q.out * (q.out • u) * (q.out • x) := by ring
    rw [smul_eq_mul, heq]
    exact he (Algebra.FormallyUnramified.elem A B)
  have hc_one : Ideal.Quotient.mk m c = 1 := by
    let q₀ : G ⧸ H := (1 : G)
    have hq₀ : q₀.out ∈ H := by
      have he : (QuotientGroup.mk q₀.out : G ⧸ H) = (1 : G) := q₀.out_eq'
      simpa only [QuotientGroup.eq, inv_one, one_mul] using he.symm
    have hq (q : G ⧸ H) (hq : q ≠ q₀) : q.out ∉ H := by
      intro h
      apply hq
      rw [← q.out_eq']
      exact QuotientGroup.eq.mpr (by simpa using H.inv_mem h)
    rw [show c = ∑ q : G ⧸ H, d q.out * (q.out • u) from rfl, map_sum]
    rw [Finset.sum_eq_single q₀]
    · rw [map_mul, hd_one _ hq₀, one_mul]
      exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
        (m.mem_inertia.mp hq₀ u)).trans hu_one
    · intro q _ hq'
      rw [map_mul, hd_zero _ (hq q hq'), zero_mul]
    · simp
  have : Ideal.Quotient.mk m c = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hKm hc_mem)
  exact zero_ne_one (this.symm.trans hc_one)

end Ideal

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Unramified A B]
  [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/-- If `B / A` is unramified with Galois group `G`, then any ideal `I` of `B` that is stable under
`G` satisfies `(I ∩ A) B = I`. -/
theorem map_comap_eq_of_unramified {I : Ideal B} (hI : ∀ σ : G, σ • I = I) :
    (I.comap (algebraMap A B)).map (algebraMap A B) = I := by
  apply Ideal.map_comap_eq_of_isInvariant_of_formallyUnramified (G := G)
  intro g x hx
  rw [← hI g]
  exact Ideal.smul_mem_pointwise_smul g x I hx
