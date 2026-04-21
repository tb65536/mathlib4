/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Artin L-Functions

In this file, we define Artin L-functions.

## Main definitions

* `Representation.Lfunction`: the L-function of a representation.
-/

@[expose] public section

open scoped Pointwise in
theorem IsArithFrobAt.mem_stabilizer (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g : G) (Q : Ideal S)
    [Q.IsPrime]
    (h : IsArithFrobAt R g Q) : g ∈ MulAction.stabilizer G Q := by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S g)

open scoped Pointwise in
theorem arithFrobAt_mem_stabilizer (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (Q : Ideal S) [Finite G]
    [Algebra.IsInvariant R S G] [Q.IsPrime] [Finite (S ⧸ Q)] :
    arithFrobAt R G Q ∈ MulAction.stabilizer G Q := by
  apply (IsArithFrobAt.arithFrobAt R G Q).mem_stabilizer

namespace Representation

instance
    {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    Module.Finite k ρ.Coinvariants :=
  inferInstanceAs <| Module.Finite k (V ⧸ Coinvariants.ker ρ)

open ArithmeticFunction IsDedekindDomain
open scoped NumberField Pointwise Polynomial

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [Module.Finite k V] (ρ : Representation k G V)
  (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L] [Finite G] (p : HeightOneSpectrum (𝓞 K))

/-- The local polynomial associated to a Galois representation `ρ : Gal(L/K) → GL(V)`, defined as
`det((1 - FrobₚT) | V_Iₚ)` where `V_Iₚ` is the coinvariants of some inertia subgroup `Iₚ` at `p`.

See `localPolynomial_eq` for a proof that this does not depend on the choice of `Iₚ` or `Frobₚ`. -/
noncomputable def localPolynomial : k[X] :=
  letI q : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
  letI D : Subgroup G := MulAction.stabilizer G q
  letI I : Subgroup D := (q.inertia G).subgroupOf D
  letI ρ' : Representation k D V := ρ.comp D.subtype
  letI σ : D := ⟨arithFrobAt (𝓞 K) G q, arithFrobAt_mem_stabilizer (𝓞 K) G q⟩
  (ρ'.quotientToCoinvariants I σ).charpoly.reverse

theorem localPolynomial_def :
    letI q : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k D V := ρ.comp D.subtype
    ∀ (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q),
    letI σ' : D := ⟨σ, hσ.mem_stabilizer⟩
    ρ.localPolynomial K L p = (ρ'.toCoinvariants I σ').charpoly.reverse := by
  let q : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
  let D : Subgroup G := MulAction.stabilizer G q
  let I : Subgroup D := (q.inertia G).subgroupOf D
  let ρ' : Representation k D V := ρ.comp D.subtype
  intro σ hσ
  let σ' : D := ⟨σ, hσ.mem_stabilizer⟩
  letI σ₀ : D := ⟨arithFrobAt (𝓞 K) G q, arithFrobAt_mem_stabilizer (𝓞 K) G q⟩
  change ρ.localPolynomial K L p = (ρ'.quotientToCoinvariants I σ').charpoly.reverse
  have : (σ₀ : D ⧸ I) = (σ' : D ⧸ I) := by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact (IsArithFrobAt.arithFrobAt (𝓞 K) G q).mul_inv_mem_inertia hσ
  rw [localPolynomial]
  congr

theorem localPolynomial_eq (q : Ideal (𝓞 L)) [q.LiesOver p.1] [q.IsMaximal]
    (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q) :
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k D V := ρ.comp D.subtype
    letI σ' : D := ⟨arithFrobAt (𝓞 K) G q, arithFrobAt_mem_stabilizer (𝓞 K) G q⟩
    ρ.localPolynomial K L p = (ρ'.toCoinvariants I σ').charpoly.reverse := by
  let q' : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p.1 q q' G
  let σ' := τ * σ * τ⁻¹
  have hσ' : IsArithFrobAt (𝓞 K) σ' q' := by
    rw [← hτ]
    exact hσ.conj τ
  letI D : Subgroup G := MulAction.stabilizer G q
  letI I : Subgroup D := (q.inertia G).subgroupOf D
  letI ρ' : Representation k D V := ρ.comp D.subtype
  letI σ'' : D := ⟨arithFrobAt (𝓞 K) G q, arithFrobAt_mem_stabilizer (𝓞 K) G q⟩
  change ρ.localPolynomial K L p = (ρ'.toCoinvariants I σ'').charpoly.reverse
  rw [ρ.localPolynomial_def K L p σ' hσ']
  letI D' : Subgroup G := MulAction.stabilizer G q'
  letI I' : Subgroup D' := (q'.inertia G).subgroupOf D'
  letI ρ'' : Representation k D' V := ρ.comp D'.subtype
  letI σ''' : D' := ⟨σ', hσ'.mem_stabilizer⟩
  change (ρ''.toCoinvariants I' σ''').charpoly.reverse = (ρ'.toCoinvariants I σ'').charpoly.reverse
  congr 1
  -- conjugation invariance of `charpoly`
  sorry

/-- The local power series associated to a Galois representation `ρ : Gal(L/K) → GL(V)`. -/
noncomputable def localPowerSeries : PowerSeries k :=
  PowerSeries.invOfUnit (ρ.localPolynomial K L p) 1

/-- The local Euler factor associated to a Galois representation `ρ : Gal(L/K) → GL(V)`. -/
noncomputable def localEulerFactor : ArithmeticFunction k :=
  .ofPowerSeries p.1.absNorm (ρ.localPowerSeries K L p)

/-- The Artin L-function of a Galois representation `ρ : Gal(L/K) → GL(V)` is the product over
places of `1 / fₚ(‖p‖⁻ˢ)` where `fₚ(T) = det((1 - FrobₚT) | V_Iₚ)` where `V_Iₚ` is the coinvariants
of some inertia subgroup `Iₚ` at `p`. -/
noncomputable def LFunction : ArithmeticFunction k :=
  eulerProduct (ρ.localEulerFactor K L)

/-- The Artin L-function of a of a Galois representation `ρ : Gal(L/K) → GL(V)`. -/
protected noncomputable def LSeries [Algebra k ℂ] (s : ℂ) :=
  LSeries (algebraMap k ℂ ∘ ρ.LFunction K L) s

end Representation
