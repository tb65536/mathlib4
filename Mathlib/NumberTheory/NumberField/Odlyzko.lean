/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# Odlyzko (WIP)
-/

@[expose] public section

section temp

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

-- PRed
theorem deriv_zero_of_frequently_mem_discrete {t : Set F}
    (ht : IsDiscrete t) (ht' : IsClosed t) (h : ∃ᶠ y in 𝓝[≠] x, f y ∈ t) : deriv f x = 0 := by
  sorry

end temp

theorem deriv_const_cpow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    deriv (fun x ↦ c ^ f x) = fun x ↦ c ^ f x * Complex.log c * deriv f x := by
  ext x
  by_cases hc : c = 0
  · simp only [hc, Complex.log_zero, mul_zero, zero_mul]
    let t : Set ℂ := {0, 1}
    refine deriv_zero_of_frequently_mem_discrete t.toFinite.isDiscrete t.toFinite.isClosed
      (Filter.Frequently.of_forall fun y ↦ ?_)
    by_cases hy : f y = 0 <;> simp [hy, t]
  · exact ((hf x).hasDerivAt.const_cpow (Or.inl hc)).deriv

namespace Complex -- logDeriv

theorem logDeriv_congr_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f g : 𝕜 → 𝕜'} {s : Set 𝕜} (hs : IsOpen s) (h : s.EqOn f g)
    (x : 𝕜) (hx : x ∈ s) :
    logDeriv f x = logDeriv g x := by
  simp_rw [logDeriv_apply, ← derivWithin_of_isOpen hs hx, derivWithin_congr h (h hx), h hx]

theorem logDeriv_congr {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f g : 𝕜 → 𝕜'} {s : Set 𝕜} (hs : IsOpen s) (h : s.EqOn f g) :
    s.EqOn (logDeriv f) (logDeriv g) :=
  logDeriv_congr_apply hs h

theorem logDeriv_const_cpow {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    logDeriv (fun s ↦ c ^ f s) = log c • deriv f := by
  rw [logDeriv, deriv_const_cpow hf]
  ext x
  by_cases hc : c = 0
  · simp [hc]
  · apply div_eq_of_eq_mul (cpow_ne_zero_iff.mpr (Or.inl hc))
    simp [mul_assoc, mul_comm]

theorem cpow_ne_zero' {x y : ℂ} (hx : x ≠ 0) : x ^ y ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl hx)

open scoped Real

attribute [fun_prop] Differentiable.const_cpow

theorem logDeriv_Gammaℝ (s : ℂ) (hs : ∀ n : ℕ, s ≠ -2 * n) :
    logDeriv Gammaℝ s = (digamma (s / 2) - Real.log π) / 2 := by
  replace hs : ∀ n : ℕ, s / 2 ≠ -n := by grind
  change logDeriv (fun s ↦ π ^ (-s / 2) * (Gamma ∘ (· / 2)) s) s = _
  rw [logDeriv_mul, logDeriv_const_cpow, ← ofReal_log, Pi.smul_apply, smul_eq_mul,
    deriv_div_const, deriv_neg, neg_div, mul_neg, mul_one_div, neg_add_eq_sub, logDeriv_comp,
    deriv_div_const, deriv_id'', mul_one_div, ← sub_div, digamma_def]
  · fun_prop (disch := assumption)
  · simp
  · positivity
  · fun_prop
  · simp
  · exact Gamma_ne_zero hs
  · fun_prop (disch := simp)
  · fun_prop (disch := assumption)

theorem logDeriv_Gammaℂ (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) :
    logDeriv Gammaℂ s = digamma s - (2 * π).log := by
  change logDeriv (fun s ↦ 2 * (2 * Real.pi) ^ (-s) * Gamma s) s = _
  rw [logDeriv_mul, logDeriv_const_mul, logDeriv_const_cpow, ← ofReal_ofNat, ← ofReal_mul,
    ← ofReal_log, Pi.smul_apply, smul_eq_mul, deriv_neg, mul_neg_one, neg_add_eq_sub, digamma_def]
  · positivity
  · fun_prop
  · simp
  · simp
  · exact Gamma_ne_zero hs
  · fun_prop (disch := simp)
  · fun_prop (disch := assumption)

end Complex

namespace NumberField -- dedekind zeta function

variable (K : Type*) [Field K] [NumberField K]

open InfinitePlace

section dedekindZeta

def dedekindZeta (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  sorry

theorem differentiableAt_dedekindZeta {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (dedekindZeta K) s :=
  sorry

theorem meromorphic_dedekindZeta : Meromorphic (dedekindZeta K) :=
  sorry

-- this is eventually needed (or rather, the Euler product)
theorem dedekindZeta_apply {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // I.absNorm = n}) s :=
  sorry

-- need logDeriv_dedekindZeta

end dedekindZeta

section completedDedekindZeta

open Real

def completedDedekindZeta (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  sorry

theorem differentiableAt_completedDedekindZeta {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (completedDedekindZeta K) s :=
  sorry

theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  sorry

theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  sorry

theorem completedDedekindZeta_eq_mul (s : ℂ) (hs : 1 < s.re) :
    completedDedekindZeta K s = |discr K| ^ (s / 2) * s.Gammaℝ ^ nrRealPlaces K *
      s.Gammaℂ ^ nrComplexPlaces K * dedekindZeta K s :=
  sorry

theorem logDeriv_completedDedekindZeta (s : ℂ) (hs : 1 < s.re) :
    logDeriv (completedDedekindZeta K) s =
      log (discr K) / 2 + nrRealPlaces K * (((s / 2).digamma - log π) / 2) +
        nrComplexPlaces K * (s.digamma - (2 * π).log) + logDeriv (dedekindZeta K) s := by
  let U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hs1 :  ∀ (n : ℕ), s ≠ -n := by rintro n rfl; simp at hs; grind
  have hs2 :  ∀ (n : ℕ), s ≠ -2 * n := by rintro n rfl; simp at hs; grind
  rw [Complex.logDeriv_congr_apply hU (completedDedekindZeta_eq_mul K) s (by grind)]
  have h1 : ((|discr K| : ℤ) : ℂ) ≠ 0 := by simp [discr_ne_zero]
  have h2 : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (one_pos.trans hs)
  have h3 : s.Gammaℂ ≠ 0 := sorry
  have h4 : dedekindZeta K s ≠ 0 := sorry
  have h5 : ((|discr K| : ℤ) : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero' h1
  have h6 : s.Gammaℝ ^ nrRealPlaces K ≠ 0 := pow_ne_zero _ h2
  have h7 : s.Gammaℂ ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ h3
  have h12 : Differentiable ℂ (fun s : ℂ ↦ s / 2) := by fun_prop
  have h8 : DifferentiableAt ℂ (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (s / 2)) s := by
    fun_prop (disch := simp [discr_ne_zero])
  have h13 : DifferentiableAt ℂ Complex.Gammaℝ s := sorry
  have h9 : DifferentiableAt ℂ (fun s : ℂ ↦ s.Gammaℝ ^ nrRealPlaces K) s := by fun_prop
  have h14 : DifferentiableAt ℂ Complex.Gammaℂ s := sorry
  have h10 : DifferentiableAt ℂ (fun s : ℂ ↦ s.Gammaℂ ^ nrComplexPlaces K) s := by fun_prop
  have h11 : DifferentiableAt ℂ (dedekindZeta K) s := sorry -- ((h8.mul h9).mul h10)
  rw [logDeriv_mul s (by exact mul_ne_zero (mul_ne_zero h5 h6) h7) h4
    (by exact (h8.mul h9).mul h10) h11]
  rw [logDeriv_mul s (by exact mul_ne_zero h5 h6) h7 (by exact h8.mul h9) h10]
  rw [logDeriv_mul s h5 h6 h8 h9]
  rw [Complex.logDeriv_const_cpow h12, Pi.smul_apply, deriv_div_const, logDeriv_fun_pow h13,
    logDeriv_fun_pow h14, Complex.logDeriv_Gammaℝ, Complex.logDeriv_Gammaℂ,
    ← Complex.ofReal_intCast, ← Complex.ofReal_log, Int.cast_abs, log_abs,
    deriv_id'', one_div, smul_eq_mul, ← div_eq_mul_inv]
  · simp
  · exact hs1
  · exact hs2

theorem two_mul_logDeriv_completedDedekindZeta (s : ℂ) (hs : 1 < s.re) :
    2 * logDeriv (completedDedekindZeta K) s =
      log |discr K| + nrRealPlaces K * ((s / 2).digamma - s.digamma + log 2) +
        Module.finrank ℚ K * (s.digamma - log (2 * π)) + logDeriv (dedekindZeta K) s := by
  rw [logDeriv_completedDedekindZeta K s hs, ← InfinitePlace.card_add_two_mul_card_eq_rank]
  rw [mul_add, mul_add, mul_add]
  simp only [log_mul two_ne_zero pi_ne_zero]

  simp [mul_add]

end completedDedekindZeta

section nontrivialZeros

def DedekindZeta.nontrivialZeros : Set ℂ :=
  {s : ℂ | s.re ∈ Set.Icc 0 1 ∧ dedekindZeta K s = 0}

end nontrivialZeros

section Odlyzko

open Real Complex

theorem tada (Φ : ℂ → ℂ) (hΦ1 : ∀ s, Φ (1 - s) = Φ s) (ε : ℝ) (hε : 0 < ε) :
    HasSum (fun s : DedekindZeta.nontrivialZeros K ↦ Φ s)
    (2 * Φ 0 +
      (2 * π)⁻¹ * ∫ t : ℝ, 2 * logDeriv (completedDedekindZeta K) (1 + ε + I * t) * Φ (1 + ε + I * t)) := by
  sorry

-- actually, define type of nontrivial zeros and phrase in terms of `HasSum`?
theorem contourIntegral_eq (Φ : ℂ → ℂ) (hΦ1 : ∀ s, Φ (1 - s) = Φ s) (ε : ℝ) (hε : 0 < ε) :
    (2 * π)⁻¹ * ∫ t : ℝ, logDeriv (completedDedekindZeta K) (1 + ε + I * t) * Φ (1 + ε + I * t) =
      - Φ 0 - Φ 1 + 0 := by
  sorry

end Odlyzko




end NumberField
