/-
Copyright (c) 2026 Thomas Browning, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.Algebraic.Denominator
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# EFunction

We define E-functions.

## Main definitions

* `PowerSeries.IsEFunction`
* `PowerSeries.EFunctions`: the subalgebra of E-functions

-/

@[expose] public section

namespace Algebra

variable (R : Type*) [CommRing R] [IsPrincipalIdealRing R] {S : Type*} [CommRing S] [Algebra R S]

variable {R}

theorem denominator_ne_zero {x : S} (hx : IsAlgebraic R x) : denominator R x ≠ 0 := by
  exact IsAlgebraic.denominator_ne_zero R hx

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

theorem natDenominator_eq_zero_iff {x : S} : natDenominator x = 0 ↔ ¬ IsAlgebraic ℤ x := by
  rw [natDenominator_def, Int.natAbs_eq_zero, denominator_eq_zero_iff]

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

end Algebra

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (f g : R[X]) (φ : R →+* S)

/-- A polynomial whose roots are the sums of the roots of `f` and `g`. -/
noncomputable def addRoots : R[X] :=
  ((f.map C).comp (C X - X)).resultant (g.map C)

theorem addRoots_def : f.addRoots g = ((f.map C).comp (C X - X)).resultant (g.map C) := by
  rfl

theorem addRoots_eq (m n : ℕ) (hm : f.natDegree = m) (hn : g.natDegree = n) :
    f.addRoots g = ((f.map C).comp (C X - X)).resultant (g.map C) m n := by
  nontriviality R
  rw [addRoots_def]
  congr
  · by_cases hf : f = 0
    · simpa [hf] using hm
    · rwa [natDegree_comp_eq_of_mul_ne_zero, natDegree_map_eq_of_injective C_injective,
        natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X, mul_one]
      rwa [leadingCoeff_map_of_injective C_injective, leadingCoeff_sub_of_degree_lt' (by simp),
        leadingCoeff_X, ne_eq, mul_neg_one_pow_eq_zero_iff, C_eq_zero, leadingCoeff_eq_zero]
  · rwa [natDegree_map_eq_of_injective C_injective]

theorem addRoots_zero_left (hg : g.natDegree ≠ 0) : addRoots 0 g = 0 := by
  rw [addRoots_def, Polynomial.map_zero, zero_comp, resultant_zero_left,
    natDegree_map_eq_of_injective C_injective, zero_pow hg, zero_mul]

theorem addRoots_zero_right (hf : f.natDegree ≠ 0) : addRoots f 0 = 0 := by
  nontriviality R
  rw [addRoots_def, Polynomial.map_zero, resultant_zero_right, zero_pow, zero_mul]
  rwa [natDegree_comp_eq_of_mul_ne_zero, natDegree_map_eq_of_injective C_injective,
    natDegree_sub, natDegree_sub_C, natDegree_X, mul_one]
  rw [leadingCoeff_map_of_injective C_injective, leadingCoeff_sub_of_degree_lt' (by simp),
    leadingCoeff_X, ne_eq, mul_neg_one_pow_eq_zero_iff, C_eq_zero, leadingCoeff_eq_zero]
  contrapose! hf
  rw [hf, natDegree_zero]

theorem map_comp_neg_X : (f.comp (-X)).map φ = (f.map φ).comp (-X) := by
  rw [map_comp, Polynomial.map_neg, map_X]

theorem natDegree_comp_neg_X : (f.comp (-X)).natDegree = f.natDegree := by
  exact natDegree_eq_of_degree_eq (f.degree_comp_neg_X)

theorem resultant_comp_neg_X : (f.comp (-X)).resultant (g.comp (-X)) = g.resultant f := by
  revert g
  apply induction_of_Splits_of_injective_of_surjective f
  · intro R _ f hf g
    rw [resultant_eq_prod_eval _ _ _ le_rfl hf.comp_neg_X, resultant_comm,
      resultant_eq_prod_eval _ _ _ le_rfl hf, comp_neg_X_leadingCoeff_eq,
      natDegree_comp_neg_X]
    rw [mul_pow, ← pow_mul', ← mul_assoc, roots_comp_neg_X]
    simp
  · intro R S _ _ φ hφ f h g
    apply hφ
    specialize h (g.map φ)
    rw [← map_comp_neg_X, ← map_comp_neg_X, resultant_map_map, resultant_map_map,
      map_comp_neg_X, map_comp_neg_X, natDegree_comp_neg_X, natDegree_comp_neg_X,
      natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ] at h
    rwa [natDegree_comp_neg_X, natDegree_comp_neg_X]
  · intro R S _ _ φ hφ f h g
    obtain ⟨f, rfl, hf'⟩ := exists_natDegree_eq_of_mem_lifts (mem_lifts_of_surjective hφ f)
    obtain ⟨g, rfl, hg'⟩ := exists_natDegree_eq_of_mem_lifts (mem_lifts_of_surjective hφ g)
    rw [← map_comp_neg_X, ← map_comp_neg_X, resultant_map_map, resultant_map_map,
      map_comp_neg_X, map_comp_neg_X, natDegree_comp_neg_X, natDegree_comp_neg_X, ← hf', ← hg',
      ← h, natDegree_comp_neg_X, natDegree_comp_neg_X]

theorem addRoots_comm' : f.addRoots g = g.addRoots f := by
  nontriviality R
  by_cases hf0 : f = 0
  · rw [hf0]
    by_cases hg : g.natDegree = 0
    · rw [addRoots_def, addRoots_def]
      simp [natDegree_map_eq_of_injective C_injective, hg]
      rw [eq_comm, zero_pow_eq_one₀]
      rw [← le_zero_iff]
      grw [natDegree_comp_le]
      rw [natDegree_map_eq_of_injective C_injective, hg, zero_mul]
    · rw [addRoots_zero_left, addRoots_zero_right] <;> exact hg
  rw [addRoots_def, resultant_comm, natDegree_comp_eq_of_mul_ne_zero,
    natDegree_map_eq_of_injective C_injective, natDegree_sub, natDegree_sub_C,
    natDegree_X, mul_one, natDegree_map_eq_of_injective C_injective]
  · congr 1
    rw [addRoots_def]
    rw [← resultant_taylor _ _ X, taylor_apply, Polynomial.comp_assoc,
      sub_comp, C_comp, X_comp, sub_add_cancel_right, taylor_apply]
    rw [← resultant_comp_neg_X, comp_assoc, comp_neg_X_comp_neg_X, add_comp,
      X_comp, C_comp, neg_add_eq_sub]
    rw [← resultant_comm, natDegree_map_eq_of_injective C_injective]
    congr 1
    · rw [natDegree_comp_eq_of_mul_ne_zero]
      · rw [natDegree_map_eq_of_injective C_injective,
          natDegree_sub_eq_right_of_natDegree_lt (by simp), natDegree_X, mul_one]
      · rwa [leadingCoeff_map_of_injective C_injective, leadingCoeff_sub_of_degree_lt' (by simp),
          leadingCoeff_X, ne_eq, mul_neg_one_pow_eq_zero_iff, C_eq_zero, leadingCoeff_eq_zero]
  · rwa [leadingCoeff_map_of_injective C_injective, leadingCoeff_sub_of_degree_lt' (by simp),
      leadingCoeff_X, ne_eq, mul_neg_one_pow_eq_zero_iff, C_eq_zero, leadingCoeff_eq_zero]

noncomputable def map_addRoots
    (hf : (f.map φ).natDegree = f.natDegree) (hg : (g.map φ).natDegree = g.natDegree) :
    (f.addRoots g).map φ = (f.map φ).addRoots (g.map φ) := by
  rw [addRoots_eq f g f.natDegree g.natDegree rfl rfl,
    addRoots_eq (f.map φ) (g.map φ) f.natDegree g.natDegree hf hg, map_map, map_map,
    ← mapRingHom_comp_C, ← map_map, ← map_map, ← coe_mapRingHom φ, ← resultant_map_map,
    map_comp, Polynomial.map_sub, map_C, coe_mapRingHom, map_X, map_X]

noncomputable def map_addRoots_of_injective (hφ : Function.Injective φ) :
    (f.addRoots g).map φ = (f.map φ).addRoots (g.map φ) :=
  map_addRoots f g φ (natDegree_map_eq_of_injective hφ f) (natDegree_map_eq_of_injective hφ g)

theorem addRoots_eq_prod [IsDomain R] (hf : f.Splits) :
    f.addRoots g = (C f.leadingCoeff * (-1) ^ f.natDegree) ^ g.natDegree *
      (f.roots.map fun x ↦ eval (X - C x) (map C g)).prod := by
  have hf' : ((map C f).comp (C X - X)).Splits := by
    have : Invertible (1 : R[X]) := invertibleOne
    have : Invertible (-1 : R[X]) := invertibleNeg 1
    apply (hf.map C).comp_of_natDegree_le_one_of_invertible (by simp [natDegree_sub])
    rwa [leadingCoeff_sub_of_degree_lt' (by simp), leadingCoeff_X]
  by_cases hf0 : f = 0
  · simp [hf0, addRoots_def, natDegree_map_eq_of_injective C_injective]
  rw [addRoots_def, resultant_eq_prod_eval _ _ _ le_rfl hf']
  rw [leadingCoeff_comp (by simp [natDegree_sub]), natDegree_map_eq_of_injective C_injective,
    leadingCoeff_map_of_injective C_injective, leadingCoeff_sub_of_degree_lt' (by simp),
    leadingCoeff_X, natDegree_map_eq_of_injective C_injective, hf.eq_prod_roots,
    Polynomial.map_mul, ← hf.eq_prod_roots, map_C, mul_comp, C_comp,
    Polynomial.map_multiset_prod, Multiset.map_map, roots_C_mul _ (by simpa),
    multiset_prod_comp, Multiset.map_map, roots_multiset_prod, Multiset.bind_map]
  have : ∀ a : R, (C X - X - C (C a)).roots = {X - C a} := by
    intro a
    rw [← roots_neg, neg_sub, sub_sub_eq_add_sub, sub_eq_add_neg, add_assoc, add_comm,
      add_assoc, neg_add_eq_sub, ← add_sub_assoc, ← sub_sub_eq_add_sub, ← map_sub, roots_X_sub_C]
  simp [this]
  simp
  intro a b c
  apply ne_zero_of_natDegree_gt (n := 0)
  simp
  simp [natDegree_sub]

end Polynomial

section

open Polynomial

theorem eval_eval_X_sub_C_map_C {R : Type*} [CommRing R] {x y : R} {f : R[X]} :
    eval x (eval (X - C y) (map C f)) = eval (x - y) f := by
  simp_rw [eval_map, eval₂_def, eval_sum, eval_mul, eval_pow, eval_sub]
  simp [eval_eq_sum]

theorem Polynomial.degree_pos_of_eval_root {R : Type*} [Semiring R] {p : R[X]} (hp : p ≠ 0)
    {z : R} (hz : p.eval z = 0) : 0 < p.degree :=
  degree_pos_of_eval₂_root hp (RingHom.id R) hz (fun _ ↦ id)

theorem Polynomial.natDegree_pos_of_eval_root {R : Type*} [Semiring R] {p : R[X]} (hp : p ≠ 0)
    {z : R} (hz : p.eval z = 0) : 0 < p.natDegree :=
  natDegree_pos_of_eval₂_root hp (RingHom.id R) hz (fun _ ↦ id)

-- todo: use this to prove that addRoots is nonzero
theorem Polynomial.addRoots_eval_eq_zero_iff {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}
    (hf : f ≠ 0) (hf' : f.Splits) {z : R} :
    (addRoots f g).eval z = 0 ↔ ∃ x y, z = x + y ∧ f.eval x = 0 ∧ g.eval y = 0 := by
  rw [addRoots_eq_prod f g hf', eval_mul, mul_eq_zero_iff_left]
  · rw [eval_multiset_prod, Multiset.map_map]
    simp [eval_eval_X_sub_C_map_C, hf]
    grind
  · simp [hf]

-- todo: use this to prove that addRoots is nonzero
theorem Polynomial.addRoots_eval_eq_zero_iff' {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}
    (hf' : f.Splits) (hg' : g.Splits) {z : R} :
    (addRoots f g).eval z = 0 ↔ ∃ x y, z = x + y ∧ f.eval x = 0 ∧ g.eval y = 0 := by
  by_cases hf : f = 0
  · simp [hf]
    by_cases hg : g.natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hg]
      simp [addRoots]
      sorry
    · rw [addRoots_zero_left]
      simp
      · sorry
      assumption

  · apply Polynomial.addRoots_eval_eq_zero_iff
    exact hf
    exact hf'

open Pointwise in
theorem Polynomial.addRoots_ne_zero {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) : addRoots f g ≠ 0 := by
  let F := AlgebraicClosure (FractionRing R)
  have : Function.Injective (algebraMap R F) :=
    algebraMap_injective_of_field_isFractionRing R F (FractionRing R) F
  rw [← Polynomial.map_ne_zero_iff this]
  intro h
  have key : ∀ z : F, (addRoots f g).aeval z = 0 := by
    intro z
    rw [← eval_map_algebraMap, h, eval_zero]
  simp_rw [← eval_map_algebraMap, map_addRoots_of_injective _ _ _ this,
    Polynomial.addRoots_eval_eq_zero_iff (f := f.map (algebraMap R F))
    (g := g.map (algebraMap R F)) (by simpa [Polynomial.map_ne_zero_iff this])
      (IsAlgClosed.splits _)] at key
  replace key : ∀ z : F, z ∈ f.rootSet F + g.rootSet F := by
    intro z
    obtain ⟨x, y, rfl, hx, hy⟩ := key z
    rw [eval_map_algebraMap] at hx hy
    apply Set.add_mem_add
    · rwa [mem_rootSet_of_injective this hf]
    · rwa [mem_rootSet_of_injective this hg]
  replace key : f.rootSet F + g.rootSet F = Set.univ := by rwa [Set.eq_univ_iff_forall]
  have : (f.rootSet F + g.rootSet F).Finite := by
    exact Set.Finite.add (rootSet_finite f F) (rootSet_finite g F)
  rw [key, Set.finite_univ_iff, ← not_infinite_iff_finite] at this
  apply this
  exact IsAlgClosed.instInfinite

open Pointwise in
theorem Polynomial.addRoots_rootSet {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] {f g : R[X]} (hf' : (f.map (algebraMap R S)).Splits) {z : R} :
    (addRoots f g).rootSet S = f.rootSet S + g.rootSet S := by
  have h : Function.Injective (algebraMap R S) := sorry
  by_cases hf0 : f = 0
  · simp [hf0, addRoots, zero_pow_eq]
    split_ifs <;> simp
  by_cases hg0 : g = 0
  · simp [hg0, addRoots, zero_pow_eq]
    split_ifs <;> simp
  ext x
  rw [mem_rootSet', map_addRoots _ _ _ (natDegree_map_eq_of_injective h f)
      (natDegree_map_eq_of_injective h g)]
  have hf0' : f.map (algebraMap R S) ≠ 0 := by rwa [Polynomial.map_ne_zero_iff h]
  have hg0' : g.map (algebraMap R S) ≠ 0 := by rwa [Polynomial.map_ne_zero_iff h]
  rw [and_iff_right (addRoots_ne_zero hf0' hg0'), ← eval_map_algebraMap,
    map_addRoots _ _ _ (natDegree_map_eq_of_injective h f)
      (natDegree_map_eq_of_injective h g), addRoots_eval_eq_zero_iff hf0' hf',
      Set.mem_add]
  simp [mem_rootSet', hf0', hg0']
  grind

theorem Polynomial.addRoots_eval_eq_zero
    {R : Type*} [CommRing R] {f g : R[X]} {x y : R} (hf : f ≠ 0) (hg : g ≠ 0)
    (hx : f.eval x = 0) (hy : g.eval y = 0) : (addRoots f g).eval (x + y) = 0 := by
  revert x y hf g
  apply Polynomial.induction_of_Splits_of_injective_of_surjective f
  · intro R _ f hf g x y hf' hg' hx hy
    rw [addRoots_eval_eq_zero_iff]
    exact ⟨x, y, rfl, hx, hy⟩
    all_goals assumption
  · intro R S _ _ φ hφ f h g x y hf hg hx hy
    specialize @h (g.map φ) (φ x) (φ y) ((Polynomial.map_ne_zero_iff hφ).mpr hf)
      ((Polynomial.map_ne_zero_iff hφ).mpr hg) (by simp [hx]) (by simp [hy])
    rwa [← map_addRoots_of_injective f g φ hφ,
      ← map_add, eval_map_apply, map_eq_zero_iff φ hφ] at h
  · intro R S _ _ φ hφ f h g x y hf hg hx hy
    obtain ⟨f, rfl, hf'⟩ := exists_natDegree_eq_of_mem_lifts (mem_lifts_of_surjective hφ f)
    obtain ⟨g, rfl, hg'⟩ := exists_natDegree_eq_of_mem_lifts (mem_lifts_of_surjective hφ g)
    obtain ⟨x, rfl⟩ := hφ x
    obtain ⟨y, rfl⟩ := hφ y
    replace hf : f - C (f.eval x) ≠ 0 := by
      contrapose! hf
      rw [sub_eq_zero] at hf
      rw [hf, map_C, eval_C] at hx
      rw [hf, map_C, hx, C_0]
    replace hg : g - C (g.eval y) ≠ 0 := by
      contrapose! hg
      rw [sub_eq_zero] at hg
      rw [hg, map_C, eval_C] at hy
      rw [hg, map_C, hy, C_0]
    specialize @h (f - C (f.eval x)) (g - C (g.eval y)) x y hf hg (by simp) (by simp)
    apply_fun φ at h
    rwa [← eval_map_apply, map_addRoots, Polynomial.map_sub, Polynomial.map_sub, map_C, map_C,
      ← eval_map_apply, hx, ← eval_map_apply, hy, C_0, sub_zero, sub_zero, map_zero, map_add] at h
    · simpa using hf'.symm
    · simpa using hg'.symm

variable {R : Type*} [CommRing R]

structure BoundedConjugates (x : R) (B : ℝ) : Prop where
  bounded : ∃ q : ℤ[X], q ≠ 0 ∧ q.aeval x = 0 ∧ ∀ x ∈ q.aroots ℂ, ‖x‖ ≤ B

namespace BoundedConjugates

protected theorem add {x y : R} {B C : ℝ}
    (hx : BoundedConjugates x B) (hy : BoundedConjugates y C) :
    BoundedConjugates (x + y) (B + C) := by
  by_cases h : Function.Injective (algebraMap ℤ R)
  · obtain ⟨f, hf0, hfx, hf⟩ := hx.bounded
    obtain ⟨g, hg0, hgx, hg⟩ := hy.bounded
    refine ⟨f.addRoots g, ?_, ?_, ?_⟩
    · exact addRoots_ne_zero hf0 hg0
    · rw [← eval_map_algebraMap, map_addRoots]
      apply addRoots_eval_eq_zero
      · rwa [Polynomial.map_ne_zero_iff h]
      · rwa [Polynomial.map_ne_zero_iff h]
      · rwa [eval_map_algebraMap]
      · rwa [eval_map_algebraMap]
      · exact natDegree_map_eq_of_injective h f
      · exact natDegree_map_eq_of_injective h g
    · intro x hx
      simp_rw [mem_aroots, ← eval_map_algebraMap] at hx hf hg
      rw [map_addRoots_of_injective _ _ _
        (RingHom.injective_int (algebraMap ℤ ℂ)), addRoots_eval_eq_zero_iff] at hx
      · obtain ⟨a, b, rfl, ha, hb⟩ := hx.2
        specialize hf a
        specialize hg b
        grw [norm_add_le, hf ⟨hf0, ha⟩, hg ⟨hg0, hb⟩]
      · rwa [Polynomial.map_ne_zero_iff]
        exact RingHom.injective_int (algebraMap ℤ ℂ)
      · have : IsAlgClosed ℂ := sorry
        apply IsAlgClosed.splits
  · rw [injective_iff_map_eq_zero, not_forall] at h
    obtain ⟨k, hk⟩ := h
    rw [Classical.not_imp] at hk
    obtain ⟨hk1, hk2⟩ := hk
    exact ⟨.C k, by simpa, by simpa using hk1, by simp⟩

protected theorem mul {x y : R} {B C : ℝ}
    (hx : BoundedConjugates x B) (hy : BoundedConjugates y C) :
    BoundedConjugates (x * y) (B * C) := by
  sorry

end BoundedConjugates

end

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
  growth : ∃ p : ℝ[X], ∀ n, BoundedConjugates (f n) (p.eval n)
  denominators : ∃ p : ℕ[X], ∀ n, (Finset.range n).lcm (Algebra.natDenominator ∘ f) ≤ p.eval n

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
    rw [eval_add]
    exact (hp n).add (hq n)
  denominators := by
    obtain ⟨p, hp⟩ := hf.denominators
    obtain ⟨q, hq⟩ := hg.denominators
    refine ⟨p * q, fun n ↦ ?_⟩
    specialize hp n
    specialize hq n
    rw [eval_mul]
    have h1 := (Finset.range n).lcm_mul_dvd
      (Algebra.natDenominator ∘ f) (Algebra.natDenominator ∘ g)
    refine le_trans ?_ (mul_le_mul' hp hq)
    apply Nat.le_of_dvd
    · simp_rw [pos_iff_ne_zero, mul_ne_zero_iff, Finset.lcm_ne_zero_iff]
      exact ⟨fun k hk ↦ (hf.isAlgebraic k).natDenominator_ne_zero,
        fun k hk ↦ (hg.isAlgebraic k).natDenominator_ne_zero⟩
    · refine dvd_trans ?_ h1
      apply Finset.lcm_dvd_lcm
      intro i hi
      apply Algebra.natDenominator_add_dvd_mul

protected theorem mul {f g : ℕ → R} (hf : IsESeq f) (hg : IsESeq g) : IsESeq (f * g) where
  growth := by
    obtain ⟨p, hp⟩ := hf.growth
    obtain ⟨q, hq⟩ := hg.growth
    refine ⟨p * q, fun n ↦ ?_⟩
    rw [eval_mul]
    exact (hp n).mul (hq n)
  denominators := by
    obtain ⟨p, hp⟩ := hf.denominators
    obtain ⟨q, hq⟩ := hg.denominators
    refine ⟨p * q, fun n ↦ ?_⟩
    specialize hp n
    specialize hq n
    rw [eval_mul]
    have h1 := (Finset.range n).lcm_mul_dvd
      (Algebra.natDenominator ∘ f) (Algebra.natDenominator ∘ g)
    refine le_trans ?_ (mul_le_mul' hp hq)
    apply Nat.le_of_dvd
    · simp_rw [pos_iff_ne_zero, mul_ne_zero_iff, Finset.lcm_ne_zero_iff]
      exact ⟨fun k hk ↦ (hf.isAlgebraic k).natDenominator_ne_zero,
        fun k hk ↦ (hg.isAlgebraic k).natDenominator_ne_zero⟩
    · refine dvd_trans ?_ h1
      apply Finset.lcm_dvd_lcm
      intro i hi
      apply Algebra.natDenominator_mul_dvd_mul

-- also need Cauchy product

end IsESeq

end

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
