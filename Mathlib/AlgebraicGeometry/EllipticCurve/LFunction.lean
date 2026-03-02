/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

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

variable {R : Type*} [CommRing R] (f : Polynomial R) (q : ℕ)

/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 - X` and `q = p`, then `f(q⁻ˢ) = 1 - p⁻ˢ`.

If `q ≤ 1` then `k ↦ q ^ k` is not injective, so we use a junk value of `1`. -/
noncomputable def ofPolynomial : ArithmeticFunction R :=
  if hq : 1 < q then ⟨Function.extend (q ^ ·) f.coeff 0, by simp [Nat.ne_zero_of_lt hq]⟩ else 1

theorem ofPolynomial_apply (hq : 1 < q) (n : ℕ) :
    ofPolynomial f q n = Function.extend (q ^ ·) f.coeff 0 n := by
  rw [ofPolynomial, dif_pos hq, coe_mk]

theorem ofPolynomial_apply_zero : ofPolynomial f q 0 = 0 := by
  simp

theorem ofPolynomial_apply_one (hq : 1 < q) : ofPolynomial f q 1 = f.coeff 0 := by
  rw [ofPolynomial_apply f q hq, ← pow_zero q, (Nat.pow_right_injective hq).extend_apply]

theorem ofPolynomial_apply_one' (hf : f.coeff 0 = 1) : ofPolynomial f q 1 = 1 := by
  by_cases hq : 1 < q
  · exact (ofPolynomial_apply_one f q hq).trans hf
  · rw [ofPolynomial, dif_neg hq, one_one]

/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)⁻¹`.
For example, if `f = 1 - X` and `q = p`, then `f(q⁻ˢ)⁻¹ = (1 - p⁻ˢ)⁻¹ = 1 + p⁻ˢ + p⁻²ˢ + ...`. -/
noncomputable def ofPolynomialInv (hf : f.coeff 0 = 1) :
    ArithmeticFunction R :=
  dirichletInverse (ofPolynomial f q) (invertibleOne.copy _ (ofPolynomial_apply_one' f q hf))

/-- The arithmetic function corresponding to the Euler product `∏ f(q⁻ˢ)⁻¹`. -/
def eulerProduct {R : Type*} [CommRing R] {ι : Type*} (f : ι → Polynomial R) (q : ι → ℕ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) : ArithmeticFunction R :=
  sorry

end ArithmeticFunction

namespace WeierstrassCurve

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The L-function of an elliptic curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def localPolynomial (W : WeierstrassCurve K)
  (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Polynomial ℤ :=
  sorry

-- can we generalize the hypotheses of `Ideal.finite_setOf_absNorm_le`?
theorem foobar {S : Type u_1} [CommRing S] [Nontrivial S] [IsDedekindDomain S] [Module.Free ℤ S]
  [Module.Finite ℤ S] [CharZero S] : Filter.Tendsto
  (fun p : IsDedekindDomain.HeightOneSpectrum S ↦ p.asIdeal.absNorm) Filter.cofinite Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  rw [Filter.eventually_cofinite]
  refine ((Ideal.finite_setOf_absNorm_le B).preimage
    (f := IsDedekindDomain.HeightOneSpectrum.asIdeal) (Function.Injective.injOn ?_)).subset ?_
  · exact fun _ _ ↦ IsDedekindDomain.HeightOneSpectrum.ext
  · grind

noncomputable def L (W : WeierstrassCurve K) : ArithmeticFunction ℤ :=
  ArithmeticFunction.eulerProduct W.localPolynomial
    (fun p ↦ p.asIdeal.absNorm) foobar

/-- The L-function of an elliptic curve is the product over places of `1 / fₚ(‖p‖⁻ˢ)` where:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` if `E` has good reduction at `p`,
* `fₚ = 1 - T` if `E` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `E` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `E` has additive reduction at `p`.
-/
noncomputable def Lfunction (W : WeierstrassCurve K) (s : ℂ) :=
  LSeries (fun n ↦ W.L n) s

end WeierstrassCurve
