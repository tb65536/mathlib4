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
public import Mathlib.RingTheory.PowerSeries.Inverse

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

#check PowerSeries.invOfUnit

open Filter in
local instance {R : Type*} [Zero R] : UniformSpace (ArithmeticFunction R) := by
  refine UniformSpace.comap ((↑) : ArithmeticFunction R → (ℕ → R)) (UniformSpace.ofCore ?_)
  apply UniformSpace.Core.mk (⨅ s : Finset ℕ, (𝓟 {(f, g) | Set.EqOn f g s}))
  · grind [Set.EqOn, SetRel.id, le_iInf_iff, le_principal_iff, mem_principal]
  · suffices
      Tendsto (_root_.id) (⨅ s : Finset ℕ, 𝓟 {(f, g) : (ℕ → R) × (ℕ → R) | Set.EqOn f g ↑s})
        (⨅ s : Finset ℕ, 𝓟 {(f, g) : (ℕ → R) × (ℕ → R) | Set.EqOn f g ↑s}) by
      simp only [tendsto_iInf, tendsto_principal, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap] at this ⊢
      simp_rw [Set.eqOn_comm]
      exact this
    exact tendsto_id
  · simp only [le_iInf_iff, le_principal_iff]
    rw [SetRel.comp]
    intro i hi
    obtain ⟨s, hs, t, ht, rfl⟩ := Filter.mem_iInf.mp hi
    clear hi
    refine ⟨⋂ k : s, t k, ?_, ?_⟩
    · exact Filter.mem_iInf.mpr ⟨s, hs, t, ht, rfl⟩
    · rintro a b c ⟨d, rfl⟩
      simp only
      specialize ht d
      rw [Filter.mem_principal] at ht
      apply ht
      simp
      rw [SetRel.mem_comp] at b
      obtain ⟨x, y, z⟩ := b

      grind [Filter.mem_iInf, Filter.mem_principal, Set.EqOn, Set.mem_iInter, SetRel.comp]
      sorry


    simp

    sorry

/-- The Euler product of a family of arithmetic functions. -/
noncomputable def eulerProduct {R : Type*} [CommRing R] {ι : Type*} (f : ι → ArithmeticFunction R) :
    ArithmeticFunction R :=
  ∏' i, f i

-- some API ...

theorem eulerProd_ofPowerSeries {R : Type*} [CommRing R] {ι : Type*} (f : ι → PowerSeries R)
    (q : ι → ℕ) (h : Filter.Tendsto q Filter.cofinite Filter.atTop) :
    False := by
  sorry

-- evaluating at s gives tprod ...

end ArithmeticFunction

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 + X + X² + ...` and `q = p`, then `f(q⁻ˢ) = 1 + p⁻ˢ + p⁻²ˢ + ...`.

If `q ≤ 1` then `k ↦ q ^ k` is not injective, so we use a junk value of `f.constantCoeff`. -/
noncomputable def ofPowerSeries (q : ℕ) : PowerSeries R →+* ArithmeticFunction R where
  toFun f := if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      ⟨fun k ↦ if k = 1 then f.constantCoeff else 0, by simp⟩
  map_zero' := by
    split_ifs with hq
    · rw [← coe_inj]
      apply Function.extend_zero
    · ext
      simp
  map_one' := by
    split_ifs with hq
    · ext k
      rw [coe_mk]
      by_cases h : ∃ a, q ^ a = k
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · simp [h, ArithmeticFunction.one_apply_ne (fun H ↦ h ⟨0, H.symm⟩)]
    · ext k
      simp [ArithmeticFunction.one_apply]
  map_add' f g := by
    split_ifs with hq
    · ext k
      by_cases h : ∃ a, q ^ a = k
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply]
      · simp [h]
    · ext k
      by_cases hk : k = 1 <;> simp [hk]
  map_mul' f g := by
    split_ifs with hq
    · ext k
      by_cases h : ∃ a, q ^ a = k
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply]
        let i₀ : ℕ ↪ ℕ := ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
        let i : ℕ × ℕ ↪ ℕ × ℕ := i₀.prodMap i₀
        have hs : (Finset.antidiagonal a).map i ⊆ (q ^ a).divisorsAntidiagonal := by
          intro k hk
          rw [Finset.mem_map] at hk
          obtain ⟨k, hk, rfl⟩ := hk
          rw [Finset.mem_antidiagonal] at hk
          simp [Nat.mem_divisorsAntidiagonal, i, i₀, ← pow_add, hk, ne_zero_of_lt hq]
        rw [PowerSeries.coeff_mul a f g, ← Finset.sum_subset hs, Finset.sum_map]
        · apply Finset.sum_congr rfl
          intro (j, k) h
          simp [i, i₀]
          rw [(Nat.pow_right_injective hq).extend_apply,
            (Nat.pow_right_injective hq).extend_apply]
        · intro k hk h
          by_cases ha : ∃ a, q ^ a = k.1
          · by_cases hb : ∃ b, q ^ b = k.2
            · obtain ⟨a, ha⟩ := ha
              obtain ⟨b, hb⟩ := hb
              rw [Nat.mem_divisorsAntidiagonal, ← ha, ← hb, ← pow_add] at hk
              replace hk := Nat.pow_right_injective hq hk.1
              rw [Finset.mem_map] at h
              simp at h
              specialize h a b hk
              simp [Prod.ext_iff, i, i₀, ← ha, ← hb] at h
            · rw [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
              exact hb
          · rw [Function.extend_apply', Pi.zero_apply, zero_mul]
            exact ha
      · simp [h]
        rw [Finset.sum_eq_zero]
        intro k hk
        rw [Nat.mem_divisorsAntidiagonal] at hk
        by_cases ha : ∃ a, q ^ a = k.1
        · by_cases hb : ∃ b, q ^ b = k.2
          · obtain ⟨a, ha⟩ := ha
            obtain ⟨b, hb⟩ := hb
            push_neg at h
            specialize h (a + b)
            rw [pow_add, ha, hb] at h
            exact (h hk.1).elim
          · rw [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
            exact hb
        · rw [Function.extend_apply', Pi.zero_apply, zero_mul]
          exact ha
    · ext k
      by_cases hk : k = 1
      · simp [hk]
      · rw [coe_mk, if_neg hk, mul_apply, Finset.sum_eq_zero]
        grind [coe_mk, Nat.mem_divisorsAntidiagonal]

theorem ofPowerSeries_apply (q : ℕ) (hq : 1 < q) (f : PowerSeries R) (n : ℕ) :
    ofPowerSeries q f n = Function.extend (q ^ ·) (f.coeff ·) 0 n := by
  simp [ofPowerSeries, dif_pos hq]

theorem ofPowerSeries_apply_zero (q : ℕ) (f : PowerSeries R) : ofPowerSeries q f 0 = 0 := by
  simp

theorem ofPowerSeries_apply_one (q : ℕ) (hq : 1 < q) (f : PowerSeries R) :
    ofPowerSeries q f 1 = f.constantCoeff := by
  rw [ofPowerSeries_apply q hq, ← pow_zero q, (Nat.pow_right_injective hq).extend_apply]
  rw [PowerSeries.coeff_zero_eq_constantCoeff]

theorem ofPowerSeries_apply_one' (q : ℕ) (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    ofPowerSeries q f 1 = 1 := by
  by_cases hq : 1 < q
  · exact (ofPowerSeries_apply_one q hq f).trans hf
  · simpa [ofPowerSeries, dif_neg hq]

end ArithmeticFunction

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
