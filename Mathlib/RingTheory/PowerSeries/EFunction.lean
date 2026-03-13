/-
Copyright (c) 2026 Thomas Browning, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# EFunction

We define E-functions.

## Main definitions

* `PowerSeries.IsEFunction`
* `PowerSeries.EFunctions`: the subalgebra of E-functions

-/

@[expose] public section

namespace IsAlgebraic

variable (R : Type*) [CommRing R] [IsPrincipalIdealRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The denominator of an algebraic element. -/
noncomputable def denominator (x : S) : R :=
  Submodule.IsPrincipal.generator ((integralClosure R S).toSubmodule.colon {x})

variable {R}

theorem denominator_dvd_iff {r : R} {x : S} :
    denominator R x ∣ r ↔ IsIntegral R (r • x) := by
  rw [denominator, ← Submodule.IsPrincipal.mem_iff_generator_dvd, Submodule.mem_colon_singleton,
    Subalgebra.mem_toSubmodule, mem_integralClosure_iff]

theorem isIntegral_denominator_smul (x : S) : IsIntegral R (denominator R x • x) :=
  denominator_dvd_iff.mp dvd_rfl

theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : denominator R x ≠ 0 := by
  obtain ⟨r, hr0, hr⟩ := hx.exists_integral_multiple
  exact ne_zero_of_dvd_ne_zero hr0 (denominator_dvd_iff.mpr hr)

theorem denominator_ne_zero_iff [IsReduced R] {x : S} : denominator R x ≠ 0 ↔ IsAlgebraic R x := by
  simp_rw [IsAlgebraic.iff_exists_smul_integral, ← denominator_dvd_iff]
  exact ⟨fun h ↦ ⟨_, h, dvd_rfl⟩, fun ⟨r, hr0, hr⟩ ↦ ne_zero_of_dvd_ne_zero hr0 hr⟩

theorem denominator_eq_zero_iff [IsReduced R] {x : S} : denominator R x = 0 ↔ ¬ IsAlgebraic R x :=
  iff_not_comm.mp denominator_ne_zero_iff.symm

/-- The natural number valued denominator of an algebraic number. -/
noncomputable def natDenominator (x : S) : ℕ :=
  (denominator ℤ x).natAbs

theorem natDenominator_dvd_iff {n : ℕ} {x : S} :
    natDenominator x ∣ n ↔ IsIntegral ℤ (n • x) := by
  rw [natDenominator, ← Int.ofNat_dvd_right, denominator_dvd_iff, natCast_zsmul]

theorem isIntegral_natDenominator_smul (x : S) : IsIntegral ℤ (natDenominator x • x) :=
  natDenominator_dvd_iff.mp dvd_rfl

theorem natDenominator_eq_zero_iff {x : S} : natDenominator x = 0 ↔ ¬ IsAlgebraic ℤ x := by
  rw [natDenominator, Int.natAbs_eq_zero, denominator_eq_zero_iff]

theorem natDenominator_ne_zero_iff {x : S} : natDenominator x ≠ 0 ↔ IsAlgebraic ℤ x :=
  not_iff_comm.mp natDenominator_eq_zero_iff.symm

theorem natDenominator_ne_zero {x : S} (hx : IsAlgebraic ℤ x) : natDenominator x ≠ 0 :=
  natDenominator_ne_zero_iff.mpr hx

end IsAlgebraic

namespace PowerSeries

open Nat Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

set_option backward.isDefEq.respectTransparency false in
/-- An E-Function is a power series `f = ∑ (a_n / n!)` satisfying the following four properties:
* `f` satisfies a linear differential equation,
* the coefficients `a_n` of `f` are algebraic numbers,
* the conjugates of `a_n` in `ℂ` grow at most polynomially in `n`,
* the common denominators of `{a_0,...,a_{n-1}}` grow at most polynomially in `n`. -/
structure IsEFunction (f : R⟦X⟧) : Prop where
  satisfies : ∃ p ∈ nonZeroDivisors R[X], p.aeval (d⁄dX R).toLinearMap f = 0
  algebraic : ∀ n, IsAlgebraic ℤ (f.coeff n)
  growth : ∃ p : ℕ[X], ∀ n k : ℕ, ∀ x ∈ (minpoly ℤ (k • f.coeff n)).aroots ℂ,
    (n)! • ‖x‖ ≤ k • p.eval n
  denominators : ∃ p : ℕ[X], ∀ n,
    ((Multiset.range n).map (fun n ↦ IsAlgebraic.natDenominator ((n)! • f.coeff n))).lcm ≤ p.eval n

namespace IsEFunction

set_option backward.isDefEq.respectTransparency false in
theorem coe_of_isAlgebraic (f : R[X]) (hf : ∀ n, IsAlgebraic ℤ (f.coeff n)) :
    IsEFunction (f : R⟦X⟧) where
  satisfies := by
    use .X ^ (f.natDegree + 1)
    use  pow_mem X_mem_nonzeroDivisors (f.natDegree + 1)
    rw [map_pow, aeval_X, Module.End.coe_pow, Derivation.coeFn_coe]
    change derivativeFun^[f.natDegree + 1] (f : R⟦X⟧) = 0
    have : Polynomial.derivative^[f.natDegree + 1] f = 0 := by
      apply Polynomial.iterate_derivative_eq_zero
      simp
    rw [← coe_inj] at this
    convert this
    sorry
  algebraic := by simpa
  growth := by
    sorry
  denominators := by
    sorry

protected theorem coe [h : Algebra.IsAlgebraic ℤ R] (f : R[X]) :
    IsEFunction (f : R⟦X⟧) :=
  coe_of_isAlgebraic f fun n ↦ h.isAlgebraic (f.coeff n)

protected theorem algebraMap {x : R} (hx : IsAlgebraic ℤ x) :
    IsEFunction (algebraMap R R⟦X⟧ x) := by
  rw [IsScalarTower.algebraMap_apply R R[X] R⟦X⟧]
  apply coe_of_isAlgebraic (algebraMap R R[X] x) fun n ↦ ?_
  cases n
  · simpa
  · simp [isAlgebraic_zero]

protected theorem zero : IsEFunction (0 : R⟦X⟧) := by
  simpa using IsEFunction.algebraMap (R := R) isAlgebraic_zero

protected theorem one : IsEFunction (1 : R⟦X⟧) := by
  simpa using IsEFunction.algebraMap (R := R) isAlgebraic_one

set_option backward.isDefEq.respectTransparency false in
protected theorem add {f g : R⟦X⟧} (hf : IsEFunction f) (hg : IsEFunction g) :
    IsEFunction (f + g) where
  satisfies := by
    obtain ⟨p, hp0, hp⟩ := hf.satisfies
    obtain ⟨q, hq0, hq⟩ := hg.satisfies
    refine ⟨p * q, mul_mem hp0 hq0, ?_⟩
    rw [map_add, mul_comm, map_mul, Module.End.mul_apply, hp, map_zero, zero_add,
      ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hq, map_zero]
  algebraic := fun n ↦ (hf.algebraic n).add (hg.algebraic n)
  growth := by
    obtain ⟨p, hp⟩ := hf.growth
    obtain ⟨q, hq⟩ := hg.growth
    use p + q
    intro n S hn σ
    -- still need to extend `σ` to a larger subalgebra...
    -- or we somehow talk about Galois conjugates directly?
    sorry
  denominators := sorry

variable (R)

/-- E-functions with coefficients in a commutative ring `R` form a subrinf of `R⟦X⟧`. -/
protected def subring : Subring R⟦X⟧ where
  carrier := {f | IsEFunction f}
  zero_mem' := .zero
  one_mem' := .one
  add_mem' := sorry
  neg_mem' := sorry
  mul_mem' := sorry

/-- E-Functions with coefficients in a -/
protected def subalgebra [Algebra.IsAlgebraic ℤ R] : Subalgebra R[X] R⟦X⟧ where
  __ := IsEFunction.subring R
  algebraMap_mem' := .coe

end IsEFunction

end PowerSeries
