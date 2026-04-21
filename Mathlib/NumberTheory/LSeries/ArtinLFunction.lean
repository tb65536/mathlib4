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

-- PRed
open scoped Pointwise in
theorem IsArithFrobAt.mem_stabilizer (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g : G) (Q : Ideal S)
    [Q.IsPrime]
    (h : IsArithFrobAt R g Q) : g ∈ MulAction.stabilizer G Q := by
  rw [MulAction.mem_stabilizer_iff]
  conv_lhs => rw [← h.comap_eq]
  exact Q.map_comap_eq_self_of_equiv (MulSemiringAction.toRingEquiv G S g)

-- PRed
open scoped Pointwise in
theorem arithFrobAt_mem_stabilizer (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (G : Type*) [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (Q : Ideal S) [Finite G]
    [Algebra.IsInvariant R S G] [Q.IsPrime] [Finite (S ⧸ Q)] :
    arithFrobAt R G Q ∈ MulAction.stabilizer G Q := by
  apply (IsArithFrobAt.arithFrobAt R G Q).mem_stabilizer

namespace Representation

theorem quotientToCoinvariants_apply_coe {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (S : Subgroup G) [S.Normal] (g : G) :
    ρ.quotientToCoinvariants S g = ρ.toCoinvariants S g :=
  rfl

-- PRed
instance
    {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    Module.Finite k ρ.Coinvariants :=
  inferInstanceAs <| Module.Finite k (V ⧸ Coinvariants.ker ρ)

open ArithmeticFunction IsDedekindDomain
open scoped NumberField Pointwise Polynomial

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] (ρ : Representation k G V)
  (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [MulSemiringAction G L] [IsGaloisGroup G K L] (p : HeightOneSpectrum (𝓞 K))

noncomputable def foo1 (q : Ideal (𝓞 L)) [q.IsMaximal] [q.LiesOver p.1] :
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k I V := (ρ.comp D.subtype).comp I.subtype
    Representation k (D ⧸ I) (Coinvariants ρ') :=
  quotientToCoinvariants _ _

noncomputable def foo2 (q : Ideal (𝓞 L)) [q.IsMaximal] [q.LiesOver p.1]
    (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q) :
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k I V := (ρ.comp D.subtype).comp I.subtype
    Module.End k (Coinvariants ρ') :=
  quotientToCoinvariants _ _ (⟨σ, hσ.mem_stabilizer⟩ : MulAction.stabilizer G q)

theorem foo2_congr (q : Ideal (𝓞 L)) [q.IsMaximal] [q.LiesOver p.1]
    (σ₁ σ₂ : G) (hσ₁ : IsArithFrobAt (𝓞 K) σ₁ q) (hσ₂ : IsArithFrobAt (𝓞 K) σ₂ q) :
    ρ.foo2 K L p q σ₁ hσ₁ = ρ.foo2 K L p q σ₂ hσ₂ := by
  let D : Subgroup G := MulAction.stabilizer G q
  let I : Subgroup D := (q.inertia G).subgroupOf D
  let σ₁' : D := ⟨σ₁, hσ₁.mem_stabilizer⟩
  let σ₂' : D := ⟨σ₂, hσ₂.mem_stabilizer⟩
  have : (σ₁' : D ⧸ I) = (σ₂' : D ⧸ I) := by
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact hσ₁.mul_inv_mem_inertia hσ₂
  dsimp only [foo2]
  congr

theorem foo2_congr' (q : Ideal (𝓞 L)) [q.IsMaximal] [q.LiesOver p.1]
    (τ : G) [(τ • q).IsMaximal]
    (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q) :
    letI f₁ := ρ.foo2 K L p q σ hσ
    letI f₂ := ρ.foo2 K L p (τ • q) (τ * σ * τ⁻¹) (hσ.conj τ)
    False := by
  let D₁ : Subgroup G := MulAction.stabilizer G q
  let I₁ : Subgroup D₁ := (q.inertia G).subgroupOf D₁
  let D₂ : Subgroup G := MulAction.stabilizer G (τ • q)
  let I₂ : Subgroup D₂ := ((τ • q).inertia G).subgroupOf D₂
  have key : D₂ = MulAut.conj τ • D₁ :=
    MulAction.stabilizer_smul_eq_stabilizer_map_conj τ q
  have key : (τ • q).inertia G = MulAut.conj τ • q.inertia G := by
    sorry


  -- let σ₁' : D := ⟨σ₁, hσ₁.mem_stabilizer⟩
  -- let σ₂' : D := ⟨σ₂, hσ₂.mem_stabilizer⟩
  -- have : (σ₁' : D ⧸ I) = (σ₂' : D ⧸ I) := by
  --   rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  --   exact hσ₁.mul_inv_mem_inertia hσ₂
  -- dsimp only [foo2]
  -- congr

variable [Module.Finite k V] -- actually, finiteness of `G` should be automatic

/-- The local polynomial associated to a Galois representation `ρ : Gal(L/K) → GL(V)`, defined as
`det((1 - FrobₚT) | V_Iₚ)` where `V_Iₚ` is the coinvariants of some inertia subgroup `Iₚ` at `p`.

See `localPolynomial_eq` for a proof that this does not depend on the choice of `Iₚ` or `Frobₚ`. -/
noncomputable def localPolynomial : k[X] :=
  letI : Finite G := IsGaloisGroup.finite G K L
  letI q : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
  (ρ.foo2 K L p q (arithFrobAt (𝓞 K) G q) (.arithFrobAt (𝓞 K) G q)).charpoly.reverse

theorem localPolynomial_def :
    letI q : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k D V := ρ.comp D.subtype
    ∀ (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q),
    letI σ' : D := ⟨σ, hσ.mem_stabilizer⟩
    ρ.localPolynomial K L p = (ρ'.toCoinvariants I σ').charpoly.reverse := by
  intro σ hσ
  rw [localPolynomial]
  congr 2
  apply foo2_congr
  exact hσ

theorem localPolynomial_eq (q : Ideal (𝓞 L)) [q.LiesOver p.1] [q.IsMaximal]
    (σ : G) (hσ : IsArithFrobAt (𝓞 K) σ q) :
    letI : Finite G := IsGaloisGroup.finite G K L
    letI D : Subgroup G := MulAction.stabilizer G q
    letI I : Subgroup D := (q.inertia G).subgroupOf D
    letI ρ' : Representation k D V := ρ.comp D.subtype
    letI σ' : D := ⟨arithFrobAt (𝓞 K) G q, arithFrobAt_mem_stabilizer (𝓞 K) G q⟩
    ρ.localPolynomial K L p = (ρ'.toCoinvariants I σ').charpoly.reverse := by
  letI : Finite G := IsGaloisGroup.finite G K L
  let q' : Ideal (𝓞 L) := p.1.nonempty_primesOver.some.1
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p.1 q q' G
  let σ' := τ * σ * τ⁻¹
  have hσ' : IsArithFrobAt (𝓞 K) σ' q' := hτ ▸ hσ.conj τ
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
