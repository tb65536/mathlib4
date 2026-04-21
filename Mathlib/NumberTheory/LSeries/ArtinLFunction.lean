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
  apply (IsArithFrobAt.arithFrobAt R G Q).mem_stabilizer R

namespace Representation

instance
    {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k G V) :
    Module.Finite k ρ.Coinvariants :=
  inferInstanceAs <| Module.Finite k (V ⧸ Coinvariants.ker ρ)

open ArithmeticFunction IsDedekindDomain
open scoped NumberField Pointwise Polynomial

variable (L K : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {k G V : Type*}
  [Field k]
  [Group G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  (ρ : Representation k G V)

-- todo: restrict from `k` to algebraic integers
/-- The polynomial associated to a Galois representation. -/
noncomputable def localPolynomial [Finite G] (p : HeightOneSpectrum (𝓞 K)) : k[X] :=
  let q : p.1.primesOver (𝓞 L) := p.1.nonempty_primesOver.some
  let D : Subgroup G := MulAction.stabilizer G q.1
  let I : Subgroup D := (q.1.inertia G).subgroupOf D
  let σ : G := arithFrobAt (𝓞 K) G q.1
  have hσ : σ ∈ D := by apply arithFrobAt_mem_stabilizer
  let σ' : D := ⟨σ, hσ⟩
  let ρ' : Representation k D V := ρ.comp D.subtype
  (ρ'.quotientToCoinvariants I σ').charpoly.reverse -- could drop the quotient, but current formulation makes it easier to prove API

/-- The polynomial associated to a Galois representation. -/
noncomputable def localPowerSeries [Finite G] (p : HeightOneSpectrum (𝓞 K)) : PowerSeries k :=
  PowerSeries.invOfUnit (ρ.localPolynomial L K p) 1

/-- The local Euler factor associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localEulerFactor [Finite G] (p : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction k :=
  .ofPowerSeries p.1.absNorm (ρ.localPowerSeries L K p)

/-- The Artin L-function of a representation `ρ` is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` where `aₚ = ‖p‖ + 1 - |E(K_p)|` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def LFunction : ArithmeticFunction ℤ :=
  eulerProduct fun p : HeightOneSpectrum (𝓞 K) ↦
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

/-- The L-series of a Weierstrass curve. -/
protected noncomputable def LSeries (W : WeierstrassCurve K) (s : ℂ) :=
  LSeries ((↑) ∘ W.LFunction) s

end Representation

namespace WeierstrassCurve

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

open Classical Polynomial in
/-- The polynomial associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localPolynomial : ℤ[X] :=
  letI W' := W.minimal R
  letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
  letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduction R then 1 + X
  else 1

/-- The power series associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localPowerSeries : PowerSeries ℤ :=
  PowerSeries.invOfUnit (W.localPolynomial R) 1

/-- The local Euler factor associated to a Weierstrass curve over a nonarchimedean local field. -/
noncomputable def localEulerFactor : ArithmeticFunction ℤ :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) (W.localPowerSeries R)

end LocalField

section NumberField

open ArithmeticFunction IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of a Weierstrass curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` where `aₚ = ‖p‖ + 1 - |E(K_p)|` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def LFunction : ArithmeticFunction ℤ :=
  eulerProduct fun p : HeightOneSpectrum (𝓞 K) ↦
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

/-- The L-series of a Weierstrass curve. -/
protected noncomputable def LSeries (W : WeierstrassCurve K) (s : ℂ) :=
  LSeries ((↑) ∘ W.LFunction) s

end NumberField

end WeierstrassCurve
