/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.FieldTheory.Normal.Defs

/-!
# The Gelfand radius as an algebra norm

This file uses the Gelfand radius to define an algebra norm on a finite extension of a normed field.

## Main definitions

* `gelfandRadiusNorm K L`: The algebra norm on a finite extension `L` of a normed field `K`.
  The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`.

## Main statements

* `isPowMul_gelfandRadiusNorm`: the Gelfand radius norm is power-multiplicative.
* `gelfandRadiusNorm_algebraMap`: the Gelfand radius norm is invariant under algebra maps.
* `gelfandRadiusNorm_map`: the Gelfand radius norm is invariant under algebra homomorphisms.
-/

public section

variable (K L M : Type*) [NormedField K] [Field L] [Field M] [Algebra K L] [Algebra K M]
  [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K L] [FiniteDimensional K M]

open scoped Matrix.Norms.Operator

/-- The Gelfand radius algebra norm on a finite extension `L` of a normed field `K`.
The norm of `x : L` is defined as the Gelfand radius of multiplication by `x` on `L`. -/
noncomputable def gelfandRadiusNorm : AlgebraNorm K L where
  toFun x := gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x)
  map_zero' := by rw [map_zero, gelfandRadius_zero]
  add_le' x y := by grw [map_add, ((Commute.all x y).map _).gelfandRadius_add_le]
  neg' x := by rw [map_neg, gelfandRadius_neg]
  mul_le' x y := by grw [map_mul, ((Commute.all x y).map _).gelfandRadius_mul_le]
  eq_zero_of_map_eq_zero' x h := by
    have hx := ((Commute.inv_right_self₀ x).map
      (Algebra.leftMulMatrix (Module.finBasis K L))).gelfandRadius_mul_le
    contrapose! hx
    simp [← map_mul, h, hx]
  smul' x y := by rw [map_smul, gelfandRadius_smul]

variable {L} in
theorem gelfandRadiusNorm_def (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix (Module.finBasis K L) x) := by
  rfl

@[simp]
theorem gelfandRadiusNorm_one : gelfandRadiusNorm K L 1 = 1 := by
  rw [gelfandRadiusNorm_def, map_one, gelfandRadius_one]

variable {K} in
@[simp]
theorem gelfandRadiusNorm_eq_norm (x : K) : gelfandRadiusNorm K K x = ‖x‖ := by
  simpa using map_smul_eq_mul (gelfandRadiusNorm K K) x 1

/-- The Gelfand radius norm is power-multiplicative. -/
theorem isPowMul_gelfandRadiusNorm : IsPowMul (gelfandRadiusNorm K L) := by
  intro x k hk
  simp_rw [gelfandRadiusNorm_def, map_pow, gelfandRadius_pow]

variable {K L} in
theorem Module.Basis.gelfandRadiusNorm_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (x : L) :
    gelfandRadiusNorm K L x = gelfandRadius (Algebra.leftMulMatrix b x) :=
  ((Algebra.lmul K L) x).gelfandRadius_toMatrix_eq (finBasis K L) b

variable {L} in
/-- The Gelfand radius norm is invariant under algebra maps. -/
@[simp]
theorem gelfandRadiusNorm_algebraMap (x : L) :
    gelfandRadiusNorm K M (algebraMap L M x) = gelfandRadiusNorm K L x := by
  have : FiniteDimensional L M := .of_restrictScalars_finite K L M
  let bKL := Module.finBasis K L
  let bLM := Module.finBasis L M
  rw [(bKL.smulTower bLM).gelfandRadiusNorm_apply, Algebra.smulTower_leftMulMatrix_algebraMap,
    Matrix.gelfandRadius_blockDiagonal, ciSup_const, bKL.gelfandRadiusNorm_apply]

variable {M K L} in
omit [Algebra L M] [IsScalarTower K L M] in
/-- The Gelfand radius norm is invariant under algebra homomorphisms. -/
@[simp]
theorem gelfandRadiusNorm_map {F : Type*} [FunLike F L M] [AlgHomClass F K L M] (f : F) (x : L) :
    gelfandRadiusNorm K M (f x) = gelfandRadiusNorm K L x :=
  let := (AlgHom.ofClass f).toAlgebra
  gelfandRadiusNorm_algebraMap K M x

theorem IsPowMul.le_gelfandRadiusNorm
    {K L : Type*} [NormedField K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {f : AlgebraNorm K L} (hf : IsPowMul f) (x : L) :
    f x ≤ gelfandRadiusNorm K L x := by
  let b := Module.finBasis K L
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, f x ≤ C * ‖Algebra.leftMulMatrix b x‖ := by
    use ‖⇑(b.repr 1)‖ * ∑ i, f (b i)
    intro x
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
    grw [Finset.map_sum_le_sum]
    simp_rw [map_smul_eq_mul]
    have h : b.repr x = (Algebra.leftMulMatrix b x).mulVec (b.repr 1) := by
      rw [Algebra.leftMulMatrix_mulVec_repr, mul_one]
    grw [norm_le_pi_norm, ← Finset.mul_sum, h, Matrix.linfty_opNorm_mulVec, mul_assoc, mul_comm]
  apply le_gelfandRadius_of_bound _ (C := max C 1)
  intro n
  by_cases! hn : n = 0
  · simp [hn]
  · grw [← hf x hn.pos, hC, map_pow, le_max_left C 1]

def AlgebraNorm.compAlgEquiv {R A B : Type*} [SeminormedCommRing R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] (f : AlgebraNorm R B) (σ : A ≃ₐ[R] B) : AlgebraNorm R A where
  __ := f.toSeminorm.comp σ.toLinearMap
  toFun x := f (σ x)
  mul_le' x y := by grw [map_mul, map_mul_le_mul]
  eq_zero_of_map_eq_zero' x hx := by simpa using eq_zero_of_map_eq_zero f hx

theorem IsPowMul.comp_algEquiv {R A B : Type*} [SeminormedCommRing R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] {f : AlgebraNorm R B} (hf : IsPowMul f) (σ : A ≃ₐ[R] B) :
    IsPowMul (f.compAlgEquiv σ) :=
  fun x n hn ↦ (congr(f $(σ.map_pow x n))).trans (hf (σ x) hn)

theorem IsPowMul.comp {A B F : Type*} [Monoid A] [Monoid B] {f : B → ℝ} (hf : IsPowMul f) (σ : F)
    [FunLike F A B] [MonoidHomClass F A B] : IsPowMul (f ∘ σ) :=
  fun x n hn ↦ (congr(f $(map_pow σ x n))).trans (hf (σ x) hn)

-- todo: do we really need hf_ext?
theorem gelfandRadiusNorm_eq_iSup_of_finiteDimensional_normal
    {K L : Type*} [NormedField K] [Field L] [Algebra K L] [FiniteDimensional K L] [Normal K L]
    {f : AlgebraNorm K L} (hf_pm : IsPowMul f) (hf_ext : ∀ x, f (algebraMap K L x) = ‖x‖) (x : L) :
    gelfandRadiusNorm K L x = ⨆ σ : Gal(L/K), f (σ x) := by
  let F x := ⨆ σ : Gal(L/K), f (σ x)
  change gelfandRadiusNorm K L x = F x
  have hf x n : f (x ^ n) = f x ^ n := by
    by_cases hn : n = 0
    · simpa [hn] using hf_ext 1
    · exact hf_pm x (Nat.one_le_iff_ne_zero.mpr hn)
  have hF x n : F (x ^ n) = F x ^ n := by
    simp_rw [F, map_pow, hf, Real.iSup_pow fun σ : Gal(L/K) ↦ apply_nonneg f (σ x)]
  refine le_antisymm ?_ (ciSup_le fun σ ↦ ?_)
  · let P n := minpoly K (x ^ n)
    have hPs n : ((P n).map (algebraMap K L)).Splits := Normal.splits' (x ^ n)
    have hPd n : (P n).natDegree ≤ Module.finrank K L := minpoly.natDegree_le (x ^ n)
    sorry
  · let fσ := f.compAlgEquiv σ
    have hfσ : IsPowMul fσ := hf_pm.comp σ
    exact hfσ.le_gelfandRadiusNorm x
  -- roots of `P n` are `σ (x ^ n) = σ x ^ n` for `σ : Gal(L/K)`
  -- thus, if `y` is a root of `P n`, then `f y ≤ r ^ n`
  -- this gives a bound on the coefficients of `P n`
  -- now that `P n (x ^ n) = 0` and apply `gelfandRadiusNorm`
  -- moving the lower order terms over, we get `gelfandRadiusNorm x ^ (n * d) ≤ ...`
