/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Inertia degree

Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

## Main definitions

* `Ideal.inertiaDeg' q R`: The inertia degree of `q` over `R`.

## Main statements

* `inertiaDeg_eq_inertiaDeg'`: The inertia degree agrees with the usual definition in the case of
  maximal ideals.
* `inertiaDeg'_tower`: Inertia degree is multiplicative in towers.
-/

@[expose] public section

namespace IsLocalRing.ResidueField

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing B] [IsLocalRing C] [Algebra A B] [Algebra A C]


attribute [simp] ResidueField.map_residue

noncomputable def mapAlgHom (e : B →ₐ[A] C) [IsLocalHom e] :
    ResidueField B →ₐ[A] ResidueField C where
  __ := map e
  commutes' x := by
    simp [IsScalarTower.algebraMap_apply A B (ResidueField B),
      IsScalarTower.algebraMap_apply A C (ResidueField C)]

@[simp]
theorem mapAlgHom_residue (e : B →ₐ[A] C) [IsLocalHom e] (x : B) :
    mapAlgHom e (residue B x) = residue C (e x) :=
  rfl

noncomputable def mapAlgEquiv (e : B ≃ₐ[A] C) :
    ResidueField B ≃ₐ[A] ResidueField C where
  __ :=
    haveI : IsLocalHom e.toRingEquiv := inferInstance
    haveI : IsLocalHom (e : B →ₐ[A] C) := ⟨this.map_nonunit⟩
    mapAlgHom e
  invFun := map e.symm
  left_inv x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    simp
  right_inv x := by
    obtain ⟨x, rfl⟩ := residue_surjective x
    simp

@[simp]
theorem mapAlgEquiv_residue (e : B ≃ₐ[A] C) (x : B) :
    mapAlgEquiv e (residue B x) = residue C (e x) :=
  rfl

variable [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)]

noncomputable def mapAlgHom' (e : B →ₐ[A] C) [IsLocalHom e] :
    ResidueField B →ₐ[ResidueField A] ResidueField C :=
  (mapAlgHom e).extendScalarsOfSurjective residue_surjective

@[simp]
theorem mapAlgHom'_residue (e : B →ₐ[A] C) [IsLocalHom e] (x : B) :
    mapAlgHom' e (residue B x) = residue C (e x) :=
  rfl

noncomputable def mapAlgEquiv' (e : B ≃ₐ[A] C) :
    ResidueField B ≃ₐ[ResidueField A] ResidueField C :=
  (mapAlgEquiv e).extendScalarsOfSurjective residue_surjective

@[simp]
theorem mapAlgEquiv'_residue (e : B ≃ₐ[A] C) (x : B) :
    mapAlgEquiv' e (residue B x) = residue C (e x) :=
  rfl

end IsLocalRing.ResidueField

namespace Localization

open AtPrime

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  (p : Ideal A) (q : Ideal B) (r : Ideal C) [p.IsPrime] [q.IsPrime] [r.IsPrime]
  [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [IsLiesOverAlgebra p q]
  [r.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime r)] [IsLiesOverAlgebra p r]

noncomputable def localAlgEquiv' (f : B ≃ₐ[A] C) (h : q = r.comap f) :
    Localization.AtPrime q ≃ₐ[Localization.AtPrime p] Localization.AtPrime r where
  __ := localAlgEquiv q r f h
  commutes' := by
    let Ap := Localization.AtPrime p
    let f := (localAlgEquiv q r f h).toAlgHom.comp (IsScalarTower.toAlgHom A Ap _)
    let g := IsScalarTower.toAlgHom A Ap (Localization.AtPrime r)
    have : f.toRingHom.comp (algebraMap A Ap) = g.toRingHom.comp (algebraMap A Ap) := by simp
    suffices f = g by rwa [DFunLike.ext_iff] at this
    apply Localization.algHom_ext
    rwa [DFunLike.ext_iff] at this ⊢

end Localization

namespace Ideal

open Localization.AtPrime

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  (p : Ideal A) (q : Ideal B) (r : Ideal C) [p.IsPrime] [q.IsPrime] [r.IsPrime]
  [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)] [IsLiesOverAlgebra p q]
  [r.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime r)] [IsLiesOverAlgebra p r]

noncomputable def residueFieldRingEquiv (f : B ≃+* C) (h : q = r.comap f) :
    q.ResidueField ≃+* r.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (Localization.localRingEquiv q r f h)

noncomputable def residueFieldAlgEquiv (f : B ≃ₐ[A] C) (h : q = r.comap f) :
    q.ResidueField ≃ₐ[A] r.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv (Localization.localAlgEquiv q r f h)

noncomputable def residueFieldAlgEquiv' (f : B ≃ₐ[A] C) (h : q = r.comap f) :
    q.ResidueField ≃ₐ[p.ResidueField] r.ResidueField :=
  IsLocalRing.ResidueField.mapAlgEquiv' (Localization.localAlgEquiv' p q r f h)

end Ideal

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Given a prime ideal `q` of an `R`-algebra `S`, the inertia degree of `q` over `R` is defined
to be the degree of the residue field of `q` over the residue field of its preimage `p` in `R`.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.inertiaDeg`. -/
noncomputable def inertiaDeg' : ℕ :=
  if _ : q.IsPrime then
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    Module.finrank (q.under R).ResidueField q.ResidueField else 0

theorem inertiaDeg'_def [hq : q.IsPrime]
    [Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra (q.under R) q] :
    q.inertiaDeg' R = Module.finrank (q.under R).ResidueField q.ResidueField := by
  convert dif_pos hq
  simp [Algebra.algebra_ext_iff, Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]

theorem inertiaDeg'_of_not_isPrime (hq : ¬ q.IsPrime) : q.inertiaDeg' R = 0 :=
  dif_neg hq

theorem inertiaDeg'_pos [hq : q.IsPrime] [Module.Finite R S] : 0 < q.inertiaDeg' R := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  rw [inertiaDeg'_def]
  apply Module.finrank_pos

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem inertiaDeg'_eq [q.LiesOver p] [q.IsPrime] [p.IsPrime]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    q.inertiaDeg' R = Module.finrank p.ResidueField q.ResidueField := by
  have := Ideal.over_def q p
  subst this
  exact inertiaDeg'_def q R

theorem inertiaDeg_eq_inertiaDeg' [q.LiesOver p] [p.IsMaximal] [q.IsMaximal] :
    p.inertiaDeg q = q.inertiaDeg' R := by
  let : Field (R ⧸ p) := Quotient.field p
  let : Field (S ⧸ q) := Quotient.field q
  let := Localization.AtPrime.algebraOfLiesOver p q
  rw [inertiaDeg'_eq p q, inertiaDeg_algebraMap]
  let f := (algebraMap (S ⧸ q) q.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ q))
  let g := (algebraMap p.ResidueField q.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField)
  have h : f = g := by ext; simp [f, g, ← IsScalarTower.algebraMap_apply]
  let : Algebra (R ⧸ p) q.ResidueField := f.toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ q) q.ResidueField := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField q.ResidueField := IsScalarTower.of_algebraMap_eq' h
  rw [← mul_one (Module.finrank (R ⧸ p) (S ⧸ q)),
    ← Module.finrank_of_bijective_algebraMap (bijective_algebraMap_quotient_residueField q),
    Module.finrank_mul_finrank, ← Module.finrank_mul_finrank (R ⧸ p) p.ResidueField q.ResidueField,
    Module.finrank_of_bijective_algebraMap (bijective_algebraMap_quotient_residueField p), one_mul]

theorem inertiaDeg'_tower [r.LiesOver q] :
    r.inertiaDeg' R = q.inertiaDeg' R * r.inertiaDeg' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) r
    let := Localization.AtPrime.algebraOfLiesOver (r.under R) q
    let := Localization.AtPrime.algebraOfLiesOver q r
    rw [inertiaDeg'_def, inertiaDeg'_eq (r.under R), inertiaDeg'_eq q, eq_comm]
    apply Module.finrank_mul_finrank
  · rw [inertiaDeg'_of_not_isPrime r R hr, inertiaDeg'_of_not_isPrime r S hr, mul_zero]

open Pointwise in
theorem inertiaDeg'_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).inertiaDeg' R = q.inertiaDeg' R := by
  by_cases hq : q.IsPrime; swap
  · rw [inertiaDeg'_of_not_isPrime, inertiaDeg'_of_not_isPrime] <;> simpa
  · let p := q.under R
    let f₀ := MulSemiringAction.toAlgAut G R S g
    let := Localization.AtPrime.algebraOfLiesOver p q
    let := Localization.AtPrime.algebraOfLiesOver p (g • q)
    rw [inertiaDeg'_eq p q, inertiaDeg'_eq p (g • q)]
    let e₂ := Ideal.residueFieldAlgEquiv' p (g • q) q f₀.symm (comap_symm f₀.toRingEquiv).symm
    exact e₂.toLinearEquiv.finrank_eq

end

end Ideal
