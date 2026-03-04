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
# Construction of L-functions

This file develop machinery to construct L-functions.

## Main definitions

* `ArithmeticFunction.EulerProduct`: the Euler product of a family of L-functions.

## Implementation notes

Ultimately, an L-function is constructed from a collection of polynomials. However, there are
multiple routes that one can take. We choose to pass through power series, Dirichlet series,
but not multivariate power series.

                   T=q⁻ˢ                     s ∈ ℂ
[polynomials in T] ---> [polynomials in q⁻ˢ] ---> [analytic function in s]
          |                         |                           |
          | (reciprocal)            | (reciprocal)              | (reciprocal)
          v         T=q⁻ˢ           V          s ∈ ℂ            V
[power series in T] ---> [power series in q⁻ˢ] ---> [analytic function in s] (the Euler factor)
          |                         |                           |
          | (product)               | (product)                 | (product)
          v                 T=q⁻ˢ   V               s ∈ ℂ       V
[multivariate power series] ---> [Dirichlet series] ---> [L-function in s] (the Euler product)

The first vertical map is `PowerSeries.invOfUnit`, the first horizontal map is
`ArithmeticFunction.ofPowerSeries` (in this file), the second vertical map is
`ArithmeticFunction.eulerProduct` (in this file), and the second horizontal map is `LSeries`.

-/

@[expose] public section

theorem multipliable_iff_cauchySeq_finset' {α β : Type*} [CommMonoid α] [UniformSpace α]
    [CompleteSpace α] {f : β → α} : Multipliable f ↔ CauchySeq fun s ↦ ∏ b ∈ s, f b := by
  classical exact cauchy_map_iff_exists_tendsto.symm

namespace ArithmeticFunction -- Euler product of Arithmetic Functions

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A local uniform space instance on `ArithmeticFunction` in order to define `eulerProduct` as a
`tprod`. See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : UniformSpace (ArithmeticFunction R) :=
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) <| .ofCore <|
    .mk (⨅ s : Finset ℕ, 𝓟 {(f, g) | Set.EqOn f g s})
      (by simp [Set.subset_def, Set.eqOn_refl])
      (tendsto_iInf_iInf fun _ ↦ tendsto_principal_principal.mpr fun _ ↦ Set.EqOn.symm)
      (le_iInf fun s ↦ by
        have key := iInf_le (fun t : Finset ℕ ↦ 𝓟 {(f, g) : (ℕ → R) × (ℕ → R) | Set.EqOn f g t}) s
        exact lift'_le (le_principal_iff.mp key) (by grind [principal_mono, SetRel.comp, Set.EqOn]))

/-- The uniformity on `ArithmeticFunction` required in order to define `eulerProduct` as a `tprod`.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
theorem uniformity_eq : uniformity (ArithmeticFunction R) =
    comap (fun i ↦ (i.1, i.2)) ((⨅ s : Finset ℕ, 𝓟 {((f : ℕ → R), g) | Set.EqOn f g s})) :=
  rfl

/-- The topology on `ArithmeticFunction` is the topology of pointwise convergence.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
theorem tendsto_iff {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, Filter.Tendsto (fun i ↦ f i n) F (pure (g n)) := by
  simp_rw [nhds_eq_comap_uniformity,
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    tendsto_pure, Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset, eq_comm]
  exact ⟨fun h n ↦ by simpa using h { n }, fun h s k hk ↦ h k⟩

instance : CompleteSpace (ArithmeticFunction R) where
  complete {f} hf := by
    simp_rw [Cauchy] at hf
    simp_rw [nhds_eq_comap_uniformity]
    simp_rw [uniformity_eq, comap_iInf, comap_principal, le_iInf_iff, le_principal_iff,
      Set.preimage_setOf_eq] at hf ⊢
    obtain ⟨hf0, hf⟩ := hf
    replace hf (i : ℕ) : _ := hf {i}
    simp_rw [Finset.coe_singleton, Set.eqOn_singleton, mem_prod_self_iff] at hf
    sorry

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

set_option backward.isDefEq.respectTransparency false in
/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, Tendsto (fun i ↦ f i n) cofinite (pure ((1 : ArithmeticFunction R) n))) :
    ∀ n, Tendsto (fun s : Finset ι ↦ (∏ i ∈ s, f i) n) atTop (pure (eulerProduct f n)) := by
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset', CauchySeq, cauchy_map_iff',
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset]
  intro s n hn
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ tendsto_pure.mp (hf k)
  rw [← eventually_all_finite (Set.finite_Iic n), eventually_iff_exists_mem] at hf
  obtain ⟨s, hs, hs'⟩ := hf
  let t := (mem_cofinite.mp hs).toFinset
  refine ⟨t, fun u v hu hv ↦ ?_⟩
  rw [← Finset.prod_sdiff hu, ← Finset.prod_sdiff hv]
  replace hu : ∀ i ∈ u \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  replace hv : ∀ i ∈ v \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  suffices ∀ k ≤ n, (∏ x ∈ u \ t, f x) k = (∏ x ∈ v \ t, f x) k by
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [this k.1 (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hk))]
  have key w (hw : ∀ i ∈ w, i ∈ s) : ∀ k ≤ n, (∏ x ∈ w, f x) k = (1 : ArithmeticFunction R) k := by
    induction w using Finset.induction_on
    case empty => simp
    case insert i w hi hw' =>
      intro k hk
      rw [← one_mul (1 : ArithmeticFunction R)]
      rw [Finset.prod_insert hi, mul_apply, mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
        ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
      have h2 := hw' (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) j.2
        ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
      rw [h1, h2]
  intro k hk
  rw [key (u \ t) hu k hk, key (v \ t) hv k hk]

-- todo: prove that the tendsto condition holds for arithmetic functions constructed from the
-- power series machinery (under a Northcott assumption???)

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
