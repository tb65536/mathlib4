/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# The L-function of an elliptic curve

In this file, we define the L-function of an elliptic curve.

## Main definitions

* `WeierstrassCurve.Lfunction`: the L-function of a minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
-/

@[expose] public section

namespace ArithmeticFunction

/-- Given a choice of left inverse `a` of `f 1`, this is the Dirichlet inverse of `f`. -/
def dirichletInverseAuxFun {R : Type*} [Ring R] (f : ℕ → R) (a : R) (n : ℕ) : R :=
  if n = 0 then 0
  else if n = 1 then a
  else - a * ∑ d : n.properDivisors,
    have : d < n := (Nat.mem_properDivisors.mp d.2).2
    f (n / d) * dirichletInverseAuxFun f a d

theorem dirichletInverseAuxFun_apply_zero {R : Type*} [Ring R] (f : ℕ → R) (a : R) :
    dirichletInverseAuxFun f a 0 = 0 := by
  rw [dirichletInverseAuxFun, if_pos rfl]

@[simp]
theorem dirichletInverseAuxFun_apply_one {R : Type*} [Ring R] (f : ℕ → R) (a : R) :
    dirichletInverseAuxFun f a 1 = a := by
  rw [dirichletInverseAuxFun, if_neg one_ne_zero, if_pos rfl]

@[simp]
theorem dirichletInverseAuxFun_apply_ne {R : Type*} [Ring R] (f : ℕ → R) (a : R) (n : ℕ)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    dirichletInverseAuxFun f a n =
      - a * ∑ d ∈ n.properDivisors, f (n / d) * dirichletInverseAuxFun f a d := by
  rw [dirichletInverseAuxFun, if_neg hn0, if_neg hn1]
  conv_rhs => rw [← Finset.sum_attach]
  simp


/-- Given a choice of left inverse `a` of `f 1`, this is the Dirichlet inverse of `f`. -/
@[simp]
def dirichletInverseAux {R : Type*} [Ring R] (f : ℕ → R) (a : R) : ArithmeticFunction R :=
  ⟨dirichletInverseAuxFun f a, dirichletInverseAuxFun_apply_zero f a⟩

theorem self_mul_dirichletInverseAux {R : Type*} [Ring R] {f : ArithmeticFunction R} {a : R}
    (ha : f 1 * a = 1) : f * dirichletInverseAux f a = 1 := by
  ext n
  rw [dirichletInverseAux, mul_apply, coe_mk]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y ↦ f x * dirichletInverseAuxFun f a y)]
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simpa [hn1]
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  rw [← Nat.cons_self_properDivisors hn0, Finset.sum_cons, Nat.div_self hn0']
  rw [dirichletInverseAuxFun_apply_ne f a n hn0 hn1, ← mul_assoc, mul_neg, ha, neg_one_mul,
    neg_add_cancel, one_apply_ne hn1]

def dirichletInverse {R : Type*} [CommRing R] (f : ArithmeticFunction R) (hf : Invertible (f 1)) :
    Invertible f where
  invOf := dirichletInverseAux f ⅟(f 1)
  invOf_mul_self := by rw [mul_comm, self_mul_dirichletInverseAux hf.mul_invOf_self]
  mul_invOf_self := by rw [self_mul_dirichletInverseAux hf.mul_invOf_self]

theorem isUnit_iff_isUnit_apply_one {R : Type*} [CommRing R] (f : ArithmeticFunction R) :
    IsUnit f ↔ IsUnit (f 1) := by
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.val 1, f⁻¹.val 1, ?_, ?_⟩, rfl⟩
    · rw [← ArithmeticFunction.mul_apply_one, Units.mul_inv, one_one]
    · rw [← ArithmeticFunction.mul_apply_one, Units.inv_mul, one_one]
  · simpa using Nonempty.map (dirichletInverse f)

end ArithmeticFunction

namespace ArithmeticFunction

/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 - X` and `q = p`, then `f(q⁻ˢ) = 1 - p⁻ˢ`. -/
def ofPolynomial {R : Type*} [CommRing R] (f : Polynomial R) (q : ℕ) :
    ArithmeticFunction R := by
  sorry

/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)⁻¹`.
For example, if `f = 1 - X` and `q = p`, then `f(q⁻ˢ)⁻¹ = (1 - p⁻ˢ)⁻¹ = 1 + p⁻ˢ + p⁻²ˢ + ...`. -/
def ofPolynomialInv {R : Type*} [CommRing R] (f : Polynomial R) (hf : f.eval 0 = 1) (q : ℕ) :
    ArithmeticFunction R :=
  (dirichletInverse (ofPolynomial f q) sorry).invOf

def ofPolynomialProd {R : Type*} [CommRing R] {ι : Type*} (f : ι → Polynomial R) : False := sorry

end ArithmeticFunction

namespace WeierstrassCurve

open NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of an elliptic curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def localPolynomial (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Polynomial ℤ :=
  sorry

noncomputable def localLFactorAux (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ArithmeticFunction ℤ :=
  fun n ↦ if

noncomputable def Lpfunction (p k : ℕ) :=
  sorry

/-- The L-function of an elliptic curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def Lfunction (s : ℂ) :=
  LSeries (fun n ↦ n.factorization.prod fun p k ↦ Lpfunction p k) s

end WeierstrassCurve
