/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Polynomial.UnitTrinomial
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.LinearCombination

/-!
# Irreducibility of Selmer Polynomials

This file proves irreducibility of the Selmer polynomials `X ^ n - X - 1`.

## Main results

- `X_pow_sub_X_sub_one_irreducible`: The Selmer polynomials `X ^ n - X - 1` are irreducible.

TODO: Show that the Selmer polynomials have full Galois group.
-/


namespace Polynomial

open scoped Polynomial

variable {n : ℕ}

theorem X_pow_sub_X_sub_one_irreducible_aux (z : ℂ) : ¬(z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) := by
  rintro ⟨h1, h2⟩
  replace h3 : z ^ 3 = 1 := by
    linear_combination (1 - z - z ^ 2 - z ^ n) * h1 + (z ^ n - 2) * h2
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2 := by
    rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]
    have : n % 3 < 3 := Nat.mod_lt n zero_lt_three
    interval_cases n % 3 <;>
    simp only [this, pow_zero, pow_one, eq_self_iff_true, or_true, true_or]
  have z_ne_zero : z ≠ 0 := fun h =>
    zero_ne_one ((zero_pow three_ne_zero).symm.trans (show (0 : ℂ) ^ 3 = 1 from h ▸ h3))
  rcases key with (key | key | key)
  · exact z_ne_zero (by rwa [key, right_eq_add] at h1)
  · exact one_ne_zero (by rwa [key, left_eq_add] at h1)
  · exact z_ne_zero (pow_eq_zero (by rwa [key, add_self_eq_zero] at h2))

theorem X_pow_sub_X_sub_one_irreducible (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℤ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  rw [hp]
  apply IsUnitTrinomial.irreducible_of_coprime' ⟨0, 1, n, zero_lt_one, hn, -1, -1, 1, rfl⟩
  rintro z ⟨h1, h2⟩
  apply X_pow_sub_X_sub_one_irreducible_aux (n := n) z
  rw [trinomial_mirror zero_lt_one hn (-1 : ℤˣ).ne_zero (1 : ℤˣ).ne_zero] at h2
  simp_rw [trinomial, aeval_add, aeval_mul, aeval_X_pow, aeval_C,
    Units.val_neg, Units.val_one, map_neg, map_one] at h1 h2
  replace h1 : z ^ n = z + 1 := by linear_combination h1
  replace h2 := mul_eq_zero_of_left h2 z
  rw [add_mul, add_mul, add_zero, mul_assoc (-1 : ℂ), ← pow_succ, Nat.sub_add_cancel hn.le] at h2
  rw [h1] at h2 ⊢
  exact ⟨rfl, by linear_combination -h2⟩

theorem X_pow_sub_X_sub_one_irreducible_rat (hn1 : n ≠ 1) : Irreducible (X ^ n - X - 1 : ℚ[X]) := by
  by_cases hn0 : n = 0
  · rw [hn0, pow_zero, sub_sub, add_comm, ← sub_sub, sub_self, zero_sub]
    exact Associated.irreducible ⟨-1, mul_neg_one X⟩ irreducible_X
  have hp : (X ^ n - X - 1 : ℤ[X]) = trinomial 0 1 n (-1) (-1) 1 := by
    simp only [trinomial, C_neg, C_1]; ring
  have hn : 1 < n := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast ?_).mp
    (X_pow_sub_X_sub_one_irreducible hn1)
  · rwa [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
      Polynomial.map_X] at h
  · exact hp.symm ▸ (trinomial_monic zero_lt_one hn).isPrimitive

end Polynomial

---------------------------------------------------------------------------------------------------

---- Instances in Lean & Mathlib ----

-- Option 1: Have a type of all fields
theorem mul_add_distrib₁
    (F : Field) (a b c : R) :
    a * (b + c) = a * b + a * c :=
  sorry

-- Option 2: Have a type of all field structures on `F`
theorem mul_add_distrib₂
    {F : Type} (ring_structure_on_R : Field F) (a b c : F) :
    a * (b + c) = a * b + a * c :=
  sorry

example (a b : ℝ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  rw [mul_add_distrib₂ Real.field (a - b) a b] -- painful!
  sorry

-- Option 3: Let Lean fill in the default field structure
theorem mul_add_distrib₃
    {R : Type} [Field R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  sorry

example (a b : ℝ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  rw [mul_add_distrib₃ (a - b) a b] -- no longer painful!
  sorry

-- But how did Lean know the default field structure on `ℝ`?
#check Real.field -- is an `instance`

-- And how did Lean know to track default field structures?
#check Field -- is a `class`

-- How to use instances:
-- Use `class` instead of `structure` in the definition of `Ring`
-- Use `instance` instead than `def` in the definition of `Real.Ring`
-- Use `[Ring R]` instead of `(Ring R)` in theorem variables

-- In the algebraic heirarchy, `extends` is common
-- E.g., `Field` -> `CommRing` -> `Ring` -> ... -> `Distrib`
#check Distrib

-- At the very bottom: `Mul`, `Add`, `One`, `Zero`, `LE` for notation
#check Mul
#check One
#check LE

-- Some typeclasses have data, and some are just predicates
#check Algebra -- used for field extensions

-- Predicate typeclass for commutative diagram of rings/fields
#check IsScalarTower

-- Predicate typeclasses for field of fractions
#check IsFractionRing

-- But sometimes typeclasses get a bit excessive!
#check Ideal.ramificationIdx_eq_of_isGalois
