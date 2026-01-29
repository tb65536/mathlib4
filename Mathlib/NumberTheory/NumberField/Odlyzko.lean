/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.Analysis.Meromorphic.Complex
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# Odlyzko (WIP)
-/

@[expose] public section

namespace Complex -- digamma function, all PRed

noncomputable def digamma : ℂ → ℂ := logDeriv Gamma

theorem digamma_def : digamma = logDeriv Gamma := rfl

theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, (hasDerivAt_Gamma_one).deriv, Gamma_one, div_one]

theorem digamma_one_half : digamma (1 / 2) = - 2 * log 2 - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, (hasDerivAt_Gamma_one_half).deriv, add_comm, Gamma_one_half_eq,
    neg_mul, ← mul_neg, neg_add',  Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]
  simp

theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs0, Gamma_add_one s hs0,
    add_div, div_mul_cancel_right₀ (Gamma_ne_zero hs), mul_div_mul_left _ _ hs0, add_comm]

theorem meromorphic_digamma : Meromorphic digamma :=
  Meromorphic.Gamma.logDeriv

end Complex

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

-- this will be the function that we integrate from `1 + ε - i ∞` to `1 + ε + i ∞`
theorem two_mul_logDeriv_completedDedekindZeta (s : ℂ) (hs : 1 < s.re) :
    logDeriv (completedDedekindZeta K) s =
      log (discr K) / 2 - nrRealPlaces K * ((s / 2).digamma / 4) -
        nrComplexPlaces K * (0) + logDeriv (dedekindZeta K) s := by
  let U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have heq : U.EqOn (completedDedekindZeta K) (fun s ↦
    |discr K| ^ (s / 2) * s.Gammaℝ ^ nrRealPlaces K *
      s.Gammaℂ ^ nrComplexPlaces K * dedekindZeta K s) := by
    intro s hs
    apply completedDedekindZeta_eq_mul <;> grind
  rw [Complex.logDeriv_congr_apply hU heq s (by grind)]
  have h1 : ((|discr K| : ℤ) : ℂ) ≠ 0 := by sorry
  have h2 : s.Gammaℝ ≠ 0 := by sorry
  have h3 : s.Gammaℂ ≠ 0 := by sorry
  have h4 : dedekindZeta K s ≠ 0 := sorry
  have h5 : ((|discr K| : ℤ) : ℂ) ^ (s / 2) ≠ 0 := Complex.cpow_ne_zero' h1
  have h6 : s.Gammaℝ ^ nrRealPlaces K ≠ 0 := pow_ne_zero _ h2
  have h7 : s.Gammaℂ ^ nrComplexPlaces K ≠ 0 := pow_ne_zero _ h3
  have h12 : Differentiable ℂ (fun s : ℂ ↦ s / 2) := by fun_prop
  have h8 : DifferentiableAt ℂ (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (s / 2)) s := sorry
  have h13 : DifferentiableAt ℂ Complex.Gammaℝ s := sorry
  have h9 : DifferentiableAt ℂ (fun s : ℂ ↦ s.Gammaℝ ^ nrRealPlaces K) s := sorry
  have h14 : DifferentiableAt ℂ Complex.Gammaℂ s := sorry
  have h10 : DifferentiableAt ℂ (fun s : ℂ ↦ s.Gammaℂ ^ nrComplexPlaces K) s := sorry
  have h11 : DifferentiableAt ℂ (dedekindZeta K) s := sorry -- ((h8.mul h9).mul h10)
  rw [logDeriv_mul s (by exact mul_ne_zero (mul_ne_zero h5 h6) h7) h4
    (by exact (h8.mul h9).mul h10) h11]
  rw [logDeriv_mul s (by exact mul_ne_zero h5 h6) h7 (by exact h8.mul h9) h10]
  rw [logDeriv_mul s h5 h6 h8 h9]
  rw [Complex.logDeriv_const_cpow h12, logDeriv_fun_pow h13, logDeriv_fun_pow h14]
  simp [← div_eq_mul_inv]
  -- need logDeriv of Gammaℝ and Gammaℂ
  sorry

-- this will be the function that we integrate from `1 + ε - i ∞` to `1 + ε + i ∞`
theorem two_mul_logDeriv_completedDedekindZeta' (s : ℂ) (hs : 1 < s.re) :
    2 * logDeriv (completedDedekindZeta K) s = nrComplexPlaces K * log 2 +
      log |discr K| + nrRealPlaces K * ((s / 2).digamma - s.digamma + log 2) +
        Module.finrank ℚ K * (s.digamma - log (2 * π)) + logDeriv (dedekindZeta K) s := by
  let U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have heq : U.EqOn (completedDedekindZeta K) (fun s ↦
    |discr K| ^ (s / 2) * s.Gammaℝ ^ nrRealPlaces K *
      s.Gammaℂ ^ nrComplexPlaces K * dedekindZeta K s) := by
    intro s hs
    apply completedDedekindZeta_eq_mul <;> grind
  rw [Complex.logDeriv_congr_apply hU heq s (by grind)]
  rw [logDeriv_mul, logDeriv_mul, logDeriv_mul]
  sorry

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
