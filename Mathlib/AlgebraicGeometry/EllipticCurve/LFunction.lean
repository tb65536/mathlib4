/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.FiniteSupport.Basic
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

namespace ArithmeticFunction -- Euler product of Arithmetic Functions

open Filter

/-- A local instance in order to define `eulerProduct` as a `tprod`. -/
local instance {R : Type*} [Zero R] : UniformSpace (ArithmeticFunction R) :=
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) <| .ofCore <|
    .mk (⨅ s : Finset ℕ, (𝓟 {(f, g) | Set.EqOn f g s}))
      (by simp [Set.subset_def, Set.eqOn_refl])
      (tendsto_iInf_iInf fun _ ↦ tendsto_principal_principal.mpr fun _ ↦ Set.EqOn.symm)
      (le_iInf fun s ↦ by
        have key := iInf_le (fun t : Finset ℕ ↦ 𝓟 {(f, g) : (ℕ → R) × (ℕ → R) | Set.EqOn f g t}) s
        exact lift'_le (le_principal_iff.mp key) (by grind [principal_mono, SetRel.comp, Set.EqOn]))

/-- The topology on `ArithmeticFunction` is the topology of pointwise convergence. -/
theorem tendsto_iff {R : Type*} [Zero R] (ι : Type*) (f : ι → ArithmeticFunction R)
    (F : Filter ι) (g : ArithmeticFunction R) :
    Tendsto f F (nhds g) ↔ ∀ n, Filter.Tendsto (fun i ↦ f i n) F (pure (g n)) := by
  sorry

/-- The Euler product of a family of arithmetic functions. -/
noncomputable def eulerProduct {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι → ArithmeticFunction R) :
    ArithmeticFunction R :=
  ∏' i, f i

variable {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι → ArithmeticFunction R)
#check ∀ n, Filter.Tendsto (fun i ↦ f i n) .cofinite (pure ((1 : ArithmeticFunction R) n))
#check ∀ n, Filter.Tendsto (fun s : Finset ι ↦ (∏ i ∈ s, f i) n) .atTop (pure <| eulerProduct f n)
-- plug in n, tendto finset

@[ext]
structure _root_.Nat.Factorizations (n : ℕ) (ι : Type*) where
  f : ι → ℕ
  hf : finprod f = n

instance (n : ℕ) (ι : Type*) : FunLike (Nat.Factorizations n ι) ι ℕ where
  coe := Nat.Factorizations.f
  coe_injective' := by
    intro f g
    exact Nat.Factorizations.ext

theorem eulerProduct_apply {R : Type*} [CommSemiring R] [Nontrivial R]
    {ι : Type*} (f : ι → ArithmeticFunction R) (hf : ∀ i, f i 1 = 1)
    (hf : ∀ (n : ℕ) (d : Nat.Factorizations n ι),
      Function.HasFiniteMulSupport (fun j ↦ f j (d j))) (n : ℕ) :
    eulerProduct f n =
      finsum fun i : n.Factorizations ι ↦ finprod fun j ↦ f j (i.1 j) := by
  by_cases hn : n = 0
  · rw [hn, map_zero, eq_comm]
    apply finsum_eq_zero_of_forall_eq_zero
    rintro ⟨i, hi⟩
    have h0 : (Function.mulSupport fun j ↦ (f j) (i j)) ⊆ Function.mulSupport i := by
      intro x hx
      contrapose! hx
      rw [Function.notMem_mulSupport] at hx ⊢
      rw [hx, hf]
    have h1 : Function.HasFiniteMulSupport i := by
      contrapose! hi
      rw [finprod_of_not_hasFiniteMulSupport hi]
      exact one_ne_zero
    have h2 : Function.HasFiniteMulSupport fun j ↦ f j (i j) := by
      rw [Function.HasFiniteMulSupport] at h1 ⊢
      exact h1.subset h0
    rw [finprod_eq_prod _ h1, Finset.prod_eq_zero_iff] at hi
    obtain ⟨j, hj, hij⟩ := hi
    rw [finprod_eq_prod _ h2]
    apply Finset.prod_eq_zero (i := j)
    · rw [Set.Finite.mem_toFinset] at hj ⊢
      rw [Function.mem_mulSupport, hij, map_zero]
      exact zero_ne_one
    · rw [hij, map_zero]
  · sorry

theorem isMultiplicative_eulerProduct {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι → ArithmeticFunction R) (hf : ∀ i, IsMultiplicative (f i)) :
    IsMultiplicative (eulerProduct f) := by
  -- all finite products are multiplicative,
  -- and a limit of multiplicative functions is multiplicative
  sorry

#check ArithmeticFunction.IsMultiplicative

-- prove multiplicative

theorem eulerProd_ofPowerSeries {R : Type*} [CommRing R] {ι : Type*}
    (q : ι → ℕ) (h : Filter.Tendsto q Filter.cofinite Filter.atTop)
    (f : ι → PowerSeries R) (hf1 : ∀ i, (f i).constantCoeff = 1) :
    eulerProduct  := by
  sorry

-- API: evaluating at s gives tprod ...

end ArithmeticFunction

namespace ArithmeticFunction -- ArithmeticFunction from a PowerSeries

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
      let i₀ : ℕ ↪ ℕ := ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
      let i : ℕ × ℕ ↪ ℕ × ℕ := i₀.prodMap i₀
      simp only [coe_mk, mul_apply]
      by_cases h : ∃ a, q ^ a = k
      · obtain ⟨k, rfl⟩ := h
        rw [(Nat.pow_right_injective hq).extend_apply]
        let ι₀ : ℕ ↪ ℕ := ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
        let ι : ℕ × ℕ ↪ ℕ × ℕ := ι₀.prodMap ι₀
        have hs : (Finset.antidiagonal k).map ι ⊆ (q ^ k).divisorsAntidiagonal := by
          intro k hk
          rw [Finset.mem_map] at hk
          obtain ⟨k, hk, rfl⟩ := hk
          rw [Finset.mem_antidiagonal] at hk
          simp [Nat.mem_divisorsAntidiagonal, ι, ι₀, ← pow_add, hk, ne_zero_of_lt hq]
        rw [PowerSeries.coeff_mul k f g, ← Finset.sum_subset hs]
        · simp [ι, ι₀, (Nat.pow_right_injective hq).extend_apply]
        · intro (a, b) hab h
          by_cases ha : ∃ i, q ^ i = a
          · by_cases hb : ∃ j, q ^ j = b
            · obtain ⟨i, hi⟩ := ha
              obtain ⟨j, hj⟩ := hb
              rw [Nat.mem_divisorsAntidiagonal, ← hi, ← hj, ← pow_add, Nat.pow_right_inj hq] at hab
              simp_rw [Finset.mem_map, not_exists, not_and, Finset.mem_antidiagonal] at h
              specialize h (i, j) hab.1
              simp [ι, ι₀, ← hi, ← hj] at h
            · rw [Function.extend_apply' _ _ _ hb, Pi.zero_apply, mul_zero]
          · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
      · rw [Function.extend_apply' _ _ _ h, Pi.zero_apply, Finset.sum_eq_zero]
        intro (a, b) hk
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hk
        by_cases ha : ∃ i, q ^ i = a
        · by_cases hb : ∃ j, q ^ j = b
          · obtain ⟨i, hi⟩ := ha
            obtain ⟨j, hj⟩ := hb
            contrapose! h
            use i + j
            rwa [pow_add, hi, hj]
          · rw [Function.extend_apply' _ _ _ hb, Pi.zero_apply, mul_zero]
        · rw [Function.extend_apply' _ _ _ ha, Pi.zero_apply, zero_mul]
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

theorem multiplicative_ofPowerSeries
    (q : ℕ) (hq : IsPrimePow q) (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    IsMultiplicative (ofPowerSeries q f) := by
  have hq' : 1 < q := hq.one_lt
  refine ⟨ofPowerSeries_apply_one' q f hf, ?_⟩
  intro m n hmn
  rw [ofPowerSeries_apply q hq.one_lt, ofPowerSeries_apply q hq.one_lt,
    ofPowerSeries_apply q hq.one_lt]
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  -- trick: ofPowerSeries_pow lemma
  by_cases hm : ∃ i, p ^ i = m
  · by_cases hn : ∃ j, p ^ j = n
    ·
      sorry
    · rw [Function.extend_apply', Pi.zero_apply, mul_comm,
        Function.extend_apply', Pi.zero_apply, zero_mul]
      · contrapose! hn
        obtain ⟨i, hi⟩ := hn
        use k * i
        rwa [pow_mul]
      · contrapose! hn
        obtain ⟨i, hi⟩ := hn
        replace hn : n ∣ p ^ (k * i) := by
          use m
          rwa [pow_mul, mul_comm]
        sorry
  · rw [Function.extend_apply', Pi.zero_apply, Function.extend_apply', Pi.zero_apply, zero_mul]
    · contrapose! hm
      obtain ⟨i, hi⟩ := hm
      use k * i
      rwa [pow_mul]
    · contrapose! hm
      obtain ⟨i, hi⟩ := hm
      replace hi : m ∣ p ^ (k * i) := by
        use n
        rwa [pow_mul]
      sorry

-- multiplicative if `IsPrimePow q`

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
