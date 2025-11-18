/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormEqOne
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function.
* `NumberField.dedekindZeta_residue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

namespace NumberField.Dedekind

open NumberField.Units mixedEmbedding mixedEmbedding.fundamentalCone dirichletUnitTheorem

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

-- or perhaps just plug in a lattice? and then dual lattice w.r.t. trace form gives function eq'n.
noncomputable def theta (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ := sorry

-- takes in fundamental domain (e.g., `logMap '' normEqOne K`)
noncomputable def f (F : Set (logSpace K)) (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (t : ℝ) : ℂ :=
  (∫ x in F, theta a sorry) / torsionOrder K

noncomputable def invIdeal (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  (a * Units.mk0 (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)
    (by simp [differentIdeal_ne_bot]))⁻¹

#check differentIdeal ℤ (𝓞 K)

noncomputable def dedekindFEPair (a : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : WeakFEPair ℂ where
  f := f (logMap '' normEqOne K) a -- R → ℂ
  g := f (- logMap '' normEqOne K) (invIdeal a) -- ℝ → ℂ
  k := 1 / 2 -- weight, exponent in functional equation (ℝ)
  ε := 1 -- root number (ℂ)
  f₀ := 2 ^ (Module.finrank ℚ K - 1) * regulator K / torsionOrder K -- constant term at ∞ (E)
  g₀ := sorry -- constant term at ∞ (E)
  hf_int := sorry -- proof of integrability on (0,∞)
  hg_int := sorry -- proof of integrability on (0,∞)
  hk := by positivity -- 0 < k
  hε := one_ne_zero -- ε ≠ 0
  h_feq := sorry -- f (1 / x) = (ε * ↑(x ^ k)) • g x
  hf_top := sorry -- decay at ∞
  hg_top := sorry -- decay at ∞

-- f - f₀ has mellin transform Λ (see `hasMellin`)
-- functional_equation for Λ is `P.Λ (P.k - s) = P.ε • P.symm.Λ s`
/- So just define the WeakFEPair, define completed Dedekind zeta function as Mellin transform,
  define Dedekind zeta function from that, and only afterwards prove the L-series formula? -/

end NumberField.Dedekind

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology nonZeroDivisors

namespace NumberField

open scoped Real

/--
The Dedekind zeta function of a number field. It is defined as the `L`-series with coefficients
the number of integral ideals of norm `n`.
-/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/--
The value of the residue at `s = 1` of the Dedekind zeta function, see
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
-/
def dedekindZeta_residue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

theorem dedekindZeta_residue_def :
    dedekindZeta_residue K =
      (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|) := rfl

theorem dedekindZeta_residue_pos : 0 < dedekindZeta_residue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K)) <|
      Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

theorem dedekindZeta_residue_ne_zero : dedekindZeta_residue K ≠ 0 :=
  (dedekindZeta_residue_pos K).ne'

/--
**Dirichlet class number formula**
-/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ ↦ Nat.cast_nonneg _)
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOf_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

end NumberField
