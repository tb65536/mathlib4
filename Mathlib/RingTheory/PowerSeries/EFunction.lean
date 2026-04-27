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
public import Mathlib.RingTheory.LaurentSeries
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

theorem denominator_add_dvd_mul {x y : S} :
    denominator R (x + y) ∣ denominator R x * denominator R y := by
  rw [denominator_dvd_iff, smul_add]
  exact (denominator_dvd_iff.mp (dvd_mul_right _ _)).add
    ((denominator_dvd_iff.mp (dvd_mul_left _ _)))

theorem denominator_mul_dvd_mul {x y : S} :
    denominator R (x * y) ∣ denominator R x * denominator R y := by
  rw [denominator_dvd_iff, mul_smul_mul_comm]
  exact (isIntegral_denominator_smul x).mul (isIntegral_denominator_smul y)

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

theorem natDenominator_add_dvd_mul {x y : S} :
    natDenominator (x + y) ∣ natDenominator x * natDenominator y := by
  rw [natDenominator_dvd_iff, smul_add]
  exact (natDenominator_dvd_iff.mp (dvd_mul_right _ _)).add
    ((natDenominator_dvd_iff.mp (dvd_mul_left _ _)))

theorem natDenominator_mul_dvd_mul {x y : S} :
    natDenominator (x * y) ∣ natDenominator x * natDenominator y := by
  rw [natDenominator_dvd_iff, mul_smul_mul_comm]
  exact (isIntegral_natDenominator_smul x).mul (isIntegral_natDenominator_smul y)

end IsAlgebraic

section

theorem Finset.lcm_mul_dvd {α β : Type*} [CommMonoidWithZero β] [NormalizedGCDMonoid β]
    (s : Finset α) (f g : α → β) :
    s.lcm (f * g) ∣ s.lcm f * s.lcm g :=
  Finset.lcm_dvd_iff.mpr fun _ hi ↦ mul_dvd_mul (dvd_lcm hi) (dvd_lcm hi)

theorem Finset.lcm_dvd_lcm {α β : Type*} [CommMonoidWithZero β] [NormalizedGCDMonoid β]
    (s : Finset α) (f g : α → β) (hfg : ∀ a ∈ s, f a ∣ g a) :
    s.lcm f ∣ s.lcm g :=
  Finset.lcm_dvd_iff.mpr fun i hi ↦ (hfg i hi).trans (dvd_lcm hi)


variable {R : Type*} [CommRing R]

open Algebra Polynomial

/-- An E-sequence is a sequence `a₀,a₁,...` in a commutative ring `R` satisfying:
* Each `aᵢ` is algebraic over `ℤ`.
* The conjugates of `aₙ` in `ℂ` grow at most polynomially in `n`.
* The common denominators of `{a₀,...,aₙ₋₁}` grow at most polynomially in `n`.

E-sequences `a₀,a₁,...` are used to define E-functions `∑ aₙzⁿ/n!`.
-/
structure IsESeq (f : ℕ → R) : Prop where
  growth : ∃ p : ℕ[X], ∀ n, ∃ q : ℤ[X], q ≠ 0 ∧ q.aeval (f n) = 0 ∧ ∀ x ∈ q.aroots ℂ, ‖x‖ ≤ p.eval n
  denominators : ∃ p : ℕ[X], ∀ n, (Finset.range n).lcm (IsAlgebraic.natDenominator ∘ f) ≤ p.eval n

namespace IsESeq

protected theorem isAlgebraic {f : ℕ → R} (hf : IsESeq f) (n : ℕ) : IsAlgebraic ℤ (f n) := by
  obtain ⟨p, hp⟩ := hf.growth
  obtain ⟨q, hq0, hq, -⟩ := hp n
  exact ⟨q, hq0, hq⟩

protected theorem add {f g : ℕ → R} (hf : IsESeq f) (hg : IsESeq g) : IsESeq (f + g) where
  growth := by
    obtain ⟨p, hp⟩ := hf.growth
    obtain ⟨q, hq⟩ := hg.growth
    refine ⟨p + q, fun n ↦ ?_⟩
    specialize hp n
    specialize hq n
    sorry
  denominators := by
    obtain ⟨p, hp⟩ := hf.denominators
    obtain ⟨q, hq⟩ := hg.denominators
    refine ⟨p * q, fun n ↦ ?_⟩
    specialize hp n
    specialize hq n
    rw [eval_mul]
    have h1 := (Finset.range n).lcm_mul_dvd
      (IsAlgebraic.natDenominator ∘ f) (IsAlgebraic.natDenominator ∘ g)
    refine le_trans ?_ (mul_le_mul' hp hq)
    apply Nat.le_of_dvd
    · simp_rw [pos_iff_ne_zero, mul_ne_zero_iff, Finset.lcm_ne_zero_iff]
      exact ⟨fun k hk ↦ (hf.isAlgebraic k).natDenominator_ne_zero,
        fun k hk ↦ (hg.isAlgebraic k).natDenominator_ne_zero⟩
    · refine dvd_trans ?_ h1
      apply Finset.lcm_dvd_lcm
      intro i hi
      apply IsAlgebraic.natDenominator_add_dvd_mul

end IsESeq

#check IsAlgebraic.add
#check IsAlgebraic.mul

end

#exit

namespace PowerSeries

open Polynomial

set_option backward.isDefEq.respectTransparency false in
theorem derivative_pow_coe (R : Type*) [CommSemiring R] (f : R[X]) (n : ℕ) :
    ((derivative R).toLinearMap ^ n) f = (Polynomial.derivative ^ n) f := by
  induction n
  case zero => simp
  case succ n ih => simp [pow_succ', ih, derivative_coe]

end PowerSeries

namespace PowerSeries

open Nat Polynomial

variable {F : Type*} [Field F] [CharZero F]

set_option backward.isDefEq.respectTransparency false in
/-- An E-Function is a power series `f = ∑ (a_n / n!)` satisfying the following four properties:
* `f` satisfies a nonzero linear differential equation with algebraic coefficients,
* the coefficients `a_n` of `f` are algebraic numbers,
* the conjugates of `a_n` in `ℂ` grow at most polynomially in `n`,
* the common denominators of `{a_0,...,a_{n-1}}` grow at most polynomially in `n`. -/
structure IsEFunction (f : F⟦X⟧) : Prop where
  satisfies : ∃ p : F[X][X], p ≠ 0 ∧ p.eval₂ (Module.toModuleEnd F F⟦X⟧) (d⁄dX F) f = 0 ∧
    ∀ i j, IsIntegral ℚ ((p.coeff i).coeff j)
  algebraic : ∀ n, IsIntegral ℚ (f.coeff n)
  growth : ∃ p : ℕ[X], ∀ n, ∀ x ∈ (minpoly ℚ ((n)! • f.coeff n)).aroots ℂ, ‖x‖ ≤ p.eval n
  denominators : ∃ p : ℕ[X], ∀ n,
    ((Multiset.range n).map fun n ↦ IsAlgebraic.natDenominator ((n)! • f.coeff n)).lcm ≤ p.eval n

-- replace satisfies with "derivatives span finite dimensional `F[X]`-subspace of `F⟦X⟧`"?

#check Module.Finite (RatFunc F) (LaurentSeries F)

namespace IsEFunction

set_option backward.isDefEq.respectTransparency false in
theorem coe_of_isIntegral (f : F[X]) (hf : ∀ n, IsIntegral ℚ (f.coeff n)) :
    IsEFunction (f : F⟦X⟧) where
  satisfies := by
    refine ⟨.X ^ (f.natDegree + 1), by simp, ?_⟩
    rw [eval₂_X_pow, derivative_pow_coe, Module.End.coe_pow, coe_eq_zero_iff]
    use Polynomial.iterate_derivative_eq_zero f.natDegree.lt_add_one
    intro i j
    simp [apply_ite, ite_apply, Polynomial.coeff_one, isIntegral_zero, isIntegral_one]
  algebraic := by simpa
  growth := by
    sorry
  denominators := by
    sorry

protected theorem coe [h : Algebra.IsAlgebraic ℚ F] (f : F[X]) :
    IsEFunction (f : F⟦X⟧) :=
  coe_of_isIntegral f fun n ↦ h.isIntegral.isIntegral (f.coeff n)

protected theorem algebraMap {x : F} (hx : IsIntegral ℚ x) :
    IsEFunction (algebraMap F F⟦X⟧ x) := by
  rw [IsScalarTower.algebraMap_apply F F[X] F⟦X⟧]
  apply coe_of_isIntegral (algebraMap F F[X] x) fun n ↦ ?_
  cases n
  · simpa
  · simp [isIntegral_zero]

protected theorem zero : IsEFunction (0 : F⟦X⟧) := by
  simpa using IsEFunction.algebraMap (F := F) isIntegral_zero

protected theorem one : IsEFunction (1 : F⟦X⟧) := by
  simpa using IsEFunction.algebraMap (F := F) isIntegral_one

set_option backward.isDefEq.respectTransparency false in
protected theorem add {f g : F⟦X⟧} (hf : IsEFunction f) (hg : IsEFunction g) :
    IsEFunction (f + g) where
  satisfies := by
    obtain ⟨p, hp0, hp⟩ := hf.satisfies
    obtain ⟨q, hq0, hq⟩ := hg.satisfies
    refine ⟨p * q, mul_ne_zero hp0 hq0, ?_⟩
    rw [map_add, mul_comm]
    have := eval₂_mul (p := q) (q := p) (Module.toModuleEnd F F⟦X⟧) (d⁄dX F).toLinearMap
    erw [eval₂_mul]
    rw [map_add, mul_comm, eval₂_mul, Module.End.mul_apply, hp, map_zero, zero_add,
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

variable (F)

/-- E-functions with coefficients in a commutative ring `R` form a subrinf of `R⟦X⟧`. -/
protected def subring : Subring F⟦X⟧ where
  carrier := {f | IsEFunction f}
  zero_mem' := .zero
  one_mem' := .one
  add_mem' := sorry
  neg_mem' := sorry
  mul_mem' := sorry

/-- E-Functions with coefficients in a -/
protected def subalgebra [Algebra.IsAlgebraic ℚ F] : Subalgebra F[X] F⟦X⟧ where
  __ := IsEFunction.subring F
  algebraMap_mem' := .coe

end IsEFunction

end PowerSeries
