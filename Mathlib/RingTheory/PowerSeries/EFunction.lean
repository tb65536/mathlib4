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
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

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

open Polynomial

set_option linter.unusedVariables false in
-- the variable names are used in the code action of `induction`.
/-- An induction principle useful to prove statements about resultants.
Let `P` be a predicate on a polynomial.
If `R → S` injective implies `(∀ p : S[X], P p) → (∀ p : R[X], P p)`,
and if `R → S` surjective implies `(∀ p : R[X], P p) → (∀ p : S[X], P p)`,
then we may reduce to the case where `R` is a field and `p` splits. -/
nonrec lemma Polynomial.induction_of_Splits_of_injective_of_surjective'.{u}
    {R : Type u} [CommRing R] (p q : R[X])
    (P : ∀ {R : Type u} [CommRing R], R[X] → R[X] → Prop)
    (Splits : ∀ (R : Type u) [Field R] (p q : R[X]) (hp : p.Splits) (hq : q.Splits), P p q)
    (injective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Injective φ) (p q : R[X]) (IH : P (p.map φ) (q.map φ)), P p q)
    (surjective : ∀ (R S : Type u) [CommRing R] [CommRing S]
      (φ : R →+* S) (hφ : Function.Surjective φ) (p q : S[X]) (IH : ∀ p q : R[X], P p q), P p q) :
      P p q := by
  wlog hR : IsDomain R generalizing R
  · apply surjective _ _ (MvPolynomial.eval₂Hom (algebraMap ℤ R) id)
      (fun x ↦ ⟨.X x, by simp [MvPolynomial.eval₂Hom]⟩) p q
      (fun _ _ ↦ this _ _ inferInstance)
  wlog hR : IsField R generalizing R
  · apply injective _ _ _ (FaithfulSMul.algebraMap_injective R (FractionRing R)) _ _
      (this _ _ inferInstance (Field.toIsField _))
  wlog hp : p.Splits generalizing R
  · letI inst := hR.toField
    exact injective _ _ _ (algebraMap R p.SplittingField).injective _ _
      (this _ _ inferInstance (Field.toIsField _) (SplittingField.splits _))
  wlog hq : q.Splits generalizing R
  · letI inst := hR.toField
    exact injective _ _ _ (algebraMap R q.SplittingField).injective _ _
      (this _ _ inferInstance (Field.toIsField _) (hp.map _) (SplittingField.splits _))
  letI inst := hR.toField
  exact Splits _ _  _ hp hq

noncomputable def Polynomial.resultantAdd {R : Type*} [CommRing R] (f g : R[X]) : R[X] :=
  ((f.map C).comp (C X - X)).resultant (g.map C)

theorem Polynomial.resultantAdd_def {R : Type*} [CommRing R] (f g : R[X]) (m n : ℕ)
    (hm : f.natDegree = m) (hn : g.natDegree = n) :
    f.resultantAdd g = ((f.map C).comp (C X - X)).resultant (g.map C) m n := by
  nontriviality R
  by_cases hf : f = 0
  · rw [hf, resultantAdd, Polynomial.map_zero, zero_comp]
    rw [resultant, resultant, ← hm, ← hn, hf, natDegree_map_eq_of_injective C_injective]
    rfl
  rw [resultantAdd]
  congr
  · rw [natDegree_comp_eq_of_mul_ne_zero]
    · suffices (C X - X : R[X][X]).natDegree = 1 by
        rwa [this, mul_one, natDegree_map_eq_of_injective C_injective]
      rw [natDegree_sub_eq_right_of_natDegree_lt, natDegree_X]
      simp
    · rw [leadingCoeff_sub_of_degree_lt', leadingCoeff_X]
      · rw [leadingCoeff_map_of_injective C_injective]
        rwa [ne_eq, mul_neg_one_pow_eq_zero_iff, C_eq_zero, leadingCoeff_eq_zero]
      · simp
  · rwa [natDegree_map_eq_of_injective C_injective]


noncomputable def Polynomial.resultantAdd_map {R S : Type*} [CommRing R] [CommRing S] (f g : R[X])
    (φ : R →+* S) (hf : (f.map φ).natDegree = f.natDegree) (hg : (g.map φ).natDegree = g.natDegree) :
    (f.resultantAdd g).map φ = (f.map φ).resultantAdd (g.map φ) := by
  rw [resultantAdd_def f g f.natDegree g.natDegree rfl rfl,
    resultantAdd_def (f.map φ) (g.map φ) f.natDegree g.natDegree hf hg]
  rw [← coe_mapRingHom φ]
  rw [← resultant_map_map _ _ _ _ (mapRingHom φ)]
  congr
  · rw [map_comp, map_map, mapRingHom_comp_C, ← map_map]
    simp
  · rw [map_map, mapRingHom_comp_C, coe_mapRingHom, map_map]

-- maybe need to generalize to say that it's in the span or something?
theorem resultantAdd_eval_eq_zero {R : Type*} [CommRing R] {f g : R[X]} {x y : R}
    (hx : f.eval x = 0) (hy : g.eval y = 0) : (resultantAdd f g).eval (x + y) = 0 := by
  revert x y
  apply Polynomial.induction_of_Splits_of_injective_of_surjective' f g
  · intro R _ f g hf hg x y hx hy
    rw [resultantAdd, Polynomial.resultant_eq_prod_eval]
    ·
      sorry
    · exact le_rfl
    · apply (hf.map C).comp_of_natDegree_le_one_of_invertible
      · compute_degree
      · rw [leadingCoeff_sub_of_degree_lt']
        simp only [monic_X, Monic.leadingCoeff]
        have : Invertible (1 : R[X]) := invertibleOne
        apply invertibleNeg 1
        simp
  · intro R S _ _ φ hφ f g h x y hx hy
    specialize @h (φ x) (φ y) (by simp [hx]) (by simp [hy])
    rwa [← resultantAdd_map f g φ (f.natDegree_map_eq_of_injective hφ)
      (g.natDegree_map_eq_of_injective hφ), ← map_add, eval_map_apply, map_eq_zero_iff φ hφ] at h
  · intro R S _ _ φ hφ f g h x y hx hy
    have hf : f ∈ lifts φ := by exact (lifts_iff_coeff_lifts f).mpr fun n ↦ hφ (f.coeff n)
    have hg : g ∈ lifts φ := by exact (lifts_iff_coeff_lifts g).mpr fun n ↦ hφ (g.coeff n)
    obtain ⟨f, rfl, hf⟩ := Polynomial.exists_degree_eq_of_mem_lifts hf
    obtain ⟨g, rfl, hg⟩ := Polynomial.exists_degree_eq_of_mem_lifts hg
    obtain ⟨x, rfl⟩ := hφ x
    obtain ⟨y, rfl⟩ := hφ y
    rw [← resultantAdd_map f g φ, ← map_add, eval_map_apply]
    sorry

variable {R : Type*} [CommRing R]

structure BoundedConjugates (x : R) (B : ℝ) : Prop where
  bounded : ∃ q : ℤ[X], q ≠ 0 ∧ q.aeval x = 0 ∧ ∀ x ∈ q.aroots ℂ, ‖x‖ ≤ B

namespace BoundedConjugates

protected theorem add {x y : R} {B C : ℝ}
    (hx : BoundedConjugates x B) (hy : BoundedConjugates y C) :
    BoundedConjugates (x + y) (B + C) := by

  sorry

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
      (IsAlgebraic.natDenominator ∘ f) (IsAlgebraic.natDenominator ∘ g)
    refine le_trans ?_ (mul_le_mul' hp hq)
    apply Nat.le_of_dvd
    · simp_rw [pos_iff_ne_zero, mul_ne_zero_iff, Finset.lcm_ne_zero_iff]
      exact ⟨fun k hk ↦ (hf.isAlgebraic k).natDenominator_ne_zero,
        fun k hk ↦ (hg.isAlgebraic k).natDenominator_ne_zero⟩
    · refine dvd_trans ?_ h1
      apply Finset.lcm_dvd_lcm
      intro i hi
      apply IsAlgebraic.natDenominator_mul_dvd_mul

-- also need Cauchy product

end IsESeq

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
