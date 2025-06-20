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

---- Instances in Mathlib ----

-- Option 1: Have a type of all fields
theorem mul_add_distrib₁ (F : Field) (a b c : R) :
    a * (b + c) = a * b + a * c :=
  sorry

-- Problem: What is the type of `ℝ`?

-- Option 2: Have a type of all field structures on `F`
theorem mul_add_distrib₂ {F : Type}
    (ring_structure_on_R : Field F) (a b c : F) :
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

-- The mathlib algebraic heirarchy is built with `extends`
-- E.g., `Field` -> `CommRing` -> `Ring` -> ... -> `Distrib`
#check Distrib

-- At the very bottom: `Mul`, `Add`, `One`, `Zero`, `LE` give notation
#check Mul
#check One
#check LE

-- Some typeclasses have data, and some are just predicates
#check Algebra -- data for field extension
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

#check IsScalarTower -- predicate for compatible field extensions
variable (F : Type*) [Field F] [Algebra F K] [Algebra F L]
variable [IsScalarTower F K L]

#check IsFractionRing -- predicate for field of fractions
variable (R : Type*) [CommRing R] [Algebra R F]
variable [IsFractionRing R F]

-- (sometimes this starts to feel a bit excessive!)
#check Ideal.ramificationIdx_eq_of_isGalois

-- Common design decision: data vs predicate
#check Inhabited -- Data: Comes with a choice of a term
#check Nonempty  -- Predicate: Existence of a term

#eval Real.instInhabited.default

-- There is a danger to having instances with data: diamonds
-- If there are two ways of producing your instance,
-- and if these two ways produce different data,
-- then you will start running into nasty errors.

-- For example, in Filippo's talk, there are two ways to produce
-- an instance of `TopologicalSpace (ℝ × ℝ)`.
#synth MetricSpace (ℝ × ℝ)
#synth TopologicalSpace (ℝ × ℝ)

-- These turn out to be the same, but this requires a proof.
-- So Lean can't automatically convert between the two.

-- Forgetful inheritance: Rather than having an instance
-- `MetricSpace → TopologicalSpace`, include the data of a
-- topological space in the definition of a metric space
#check MetricSpace
#check PseudoMetricSpace -- includes topological space data

namespace Structures -- Example from Filippo's talk

class SpaceWithMetric (X : Type*) where
  d : X → X → ℝ
  dist_eq_zero (x : X) : d x x = 0
  dist_pos (x y : X) : x ≠ y → 0 < d x y
  symm (x y : X) : d x y = d y x
  triangle (x y z : X) : d x z ≤ d x y + d y z

instance RealMetric : SpaceWithMetric ℝ where
  d := fun x y ↦ |x - y|
  dist_eq_zero _ := by rw [sub_self, abs_zero]
  dist_pos _ _ h := abs_sub_pos.mpr h
  symm := abs_sub_comm
  triangle := abs_sub_le

export SpaceWithMetric (d)

instance metricToTopology (X : Type*) [SpaceWithMetric X] :
    (TopologicalSpace X) where
  IsOpen S := ∀ x ∈ S, ∃ ρ : ℝ, 0 < ρ ∧ {y | d x y < ρ} ⊆ S
  isOpen_univ := sorry
  isOpen_inter := sorry
  isOpen_sUnion := sorry

instance MetricOnProd (X Y : Type*) [SpaceWithMetric X] [SpaceWithMetric Y] :
    SpaceWithMetric (X × Y) where
  d p q := max (d p.1 q.1) (d p.2 q.2)
  dist_eq_zero := sorry
  dist_pos := sorry
  symm := sorry
  triangle := sorry

instance ProdRealTop : TopologicalSpace (ℝ × ℝ) := metricToTopology _

example : Continuous (fun n : ℝ × ℝ ↦ (⟨n.2, n.1⟩ : (ℝ × ℝ))) := by
  rw [continuous_prodMk]
  apply And.intro
  · apply continuous_snd
  · apply continuous_fst

end Structures

-- There are two instances of `Module ℤ ℤ`, one coming from
-- `Semiring.toModule` and another from `AddCommGroup.toIntModule`
#check Semiring.toModule
#check AddCommGroup.toIntModule

-- Mathlib solves this issue by including extra data `nsmul` and `zsmul`
#print Group

-- The definition of `CommGroup Int` overrides `nsmul` and `zsmul`
#check Int.instAddCommGroup

-- Likewise, `Field` includes extra data `qsmul`
#print Field

-- There are still lurking diamonds that haven't been fixed yet
example (a b : ℕ+) : a • b = b • a := by
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

-- We might want to define a
instance (A : Type*) [AddCommSemigroup A] : SMul ℕ+ A where
  smul n a := PNat.recOn n a (fun _ b ↦ b + a)

@[simp]
lemma PNat.one_smul (A : Type*) [AddCommSemigroup A] (a : A) :
    (1 : ℕ+) • a = a := by
  rfl

@[simp]
lemma PNat.succ_smul (A : Type*) [AddCommSemigroup A] (a : A) (n : ℕ+) :
    (n + 1) • a = n • a + a :=
  PNat.recOn_succ n a (fun _ b ↦ b + a)

-- But this leads to a diamond
example (a b : ℕ+) : a • b = b • a := by
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

-- Often mathlib seperates data typeclasses from predicate typeclasses
#check IsTopologicalGroup
variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

#check OrderTopology
variable (X : Type*) [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
