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

theorem logDeriv_const_cpow {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℂ f x) (c : ℂ) :
    logDeriv (fun s ↦ c ^ f s) x = log c * deriv f x := by
  rw [logDeriv_apply, deriv_const_cpow hf]
  by_cases hc : c = 0
  · simp [hc]
  · apply div_eq_of_eq_mul (cpow_ne_zero_iff.mpr (Or.inl hc))
    simp [mul_assoc, mul_comm]

theorem cpow_ne_zero' {x y : ℂ} (hx : x ≠ 0) : x ^ y ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl hx)

open scoped Real

attribute [fun_prop] Differentiable.const_cpow

theorem logDeriv_Gammaℝ (s : ℂ) (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    logDeriv Gammaℝ s = (digamma (s / 2) - Real.log π) / 2 := by
  replace hs : ∀ n : ℕ, s / 2 ≠ -n := by
    intro k
    specialize hs k
    grind
  change logDeriv (fun s ↦ π ^ (-s / 2) * (Gamma ∘ (· / 2)) s) s = _
  rw [logDeriv_mul, logDeriv_const_cpow, logDeriv_comp, digamma_def, ofReal_log]
  · simp
    ring
  any_goals fun_prop (disch := simp [hs])
  · positivity
  · simp -- floris's student will make this and the next `positivity`
  · exact Gamma_ne_zero hs

theorem logDeriv_Gammaℂ (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) :
    logDeriv Gammaℂ s = digamma s - (2 * π).log := by
  change logDeriv (fun s ↦ 2 * (2 * Real.pi) ^ (-s) * Gamma s) s = _
  rw [logDeriv_mul, logDeriv_const_mul, logDeriv_const_cpow, digamma_def, ofReal_log]
  · simp
    ring
  any_goals fun_prop (disch := simp [hs])
  · positivity
  · simp
  · simp
  · exact Gamma_ne_zero hs

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : s.Gammaℂ ≠ 0 := by
  simp [Gammaℂ, Gamma_ne_zero_of_re_pos hs]

@[fun_prop]
theorem differentiableAt_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    DifferentiableAt ℂ Gammaℝ s := by
  replace hs : ∀ n : ℕ, s / 2 ≠ -n := forall_imp (by grind) hs
  apply DifferentiableAt.mul <;> fun_prop (disch := simp [hs])

@[fun_prop]
theorem differentiableAt_Gammaℂ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    DifferentiableAt ℂ Gammaℂ s := by
  apply DifferentiableAt.mul <;> fun_prop (disch := simp [hs])

end Complex

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

open InfinitePlace

section dedekindZeta

def dedekindZeta (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  sorry

theorem differentiableAt_dedekindZeta {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (dedekindZeta K) s :=
  sorry

theorem differentiableOn_dedekindZeta : DifferentiableOn ℂ (dedekindZeta K) {1}ᶜ := by
  intro s hs
  exact (differentiableAt_dedekindZeta K hs).differentiableWithinAt

theorem meromorphicAt_dedekindZeta_one : MeromorphicAt (dedekindZeta K) 1 := by
  sorry

theorem meromorphic_dedekindZeta : Meromorphic (dedekindZeta K) := by
  intro s
  by_cases hs : s = 1
  · rw [hs]
    exact meromorphicAt_dedekindZeta_one K
  exact ((differentiableOn_dedekindZeta K).analyticOnNhd isOpen_compl_singleton s hs).meromorphicAt

-- this probably isn't needed
theorem dedekindZeta_apply {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // I.absNorm = n}) s :=
  sorry

-- todo: Euler product, which implies the following:

theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s ≠ 0 :=
  sorry

-- might not need actually need Euler product (since we'll just be discarding those terms ...)

end dedekindZeta

section completedDedekindZeta

open Real

def completedDedekindZeta (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  sorry

theorem differentiableAt_completedDedekindZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (completedDedekindZeta K) s :=
  sorry

theorem differentiableOn_completedDedekindZeta :
    DifferentiableOn ℂ (completedDedekindZeta K) {0, 1}ᶜ := by
  intro s hs
  rw [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hs
  exact (differentiableAt_completedDedekindZeta K hs.1 hs.2).differentiableWithinAt

theorem meromorphicAt_completedDedekindZeta_zero : MeromorphicAt (completedDedekindZeta K) 0 := by
  sorry

theorem meromorphicAt_completedDedekindZeta_one : MeromorphicAt (completedDedekindZeta K) 1 := by
  sorry

theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) := by
  intro s
  by_cases hs0 : s = 0
  · rw [hs0]
    exact meromorphicAt_completedDedekindZeta_zero K
  by_cases hs1 : s = 1
  · rw [hs1]
    exact meromorphicAt_completedDedekindZeta_one K
  refine ((differentiableOn_completedDedekindZeta K).analyticOnNhd ?_ s ?_).meromorphicAt
  · simp
  · simp [hs0, hs1]

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
  have hsℝ :  ∀ (n : ℕ), s ≠ -(2 * n) := by rintro n rfl; simp at hs; grind
  have hsℂ :  ∀ (n : ℕ), s ≠ -n := by rintro n rfl; simp at hs; grind
  have hsℝ0 : s.Gammaℝ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (one_pos.trans hs)
  have hsℂ0 : s.Gammaℂ ≠ 0 := Complex.Gammaℂ_ne_zero_of_re_pos (one_pos.trans hs)
  have h1 : dedekindZeta K s ≠ 0 := dedekindZeta_ne_zero K hs
  have h2 : DifferentiableAt ℂ (dedekindZeta K) s :=
    differentiableAt_dedekindZeta K (by contrapose! hs; simp [hs])
  rw [Complex.logDeriv_congr_apply hU (completedDedekindZeta_eq_mul K) s hs]
  rw [logDeriv_mul, logDeriv_mul, logDeriv_mul, Complex.logDeriv_const_cpow, deriv_div_const,
    deriv_id'', one_div, logDeriv_fun_pow, Complex.logDeriv_Gammaℝ s hsℝ, logDeriv_fun_pow,
    Complex.logDeriv_Gammaℂ s hsℂ, ← Complex.ofReal_intCast, ← Complex.ofReal_log, Int.cast_abs,
    log_abs, ← div_eq_mul_inv]
  any_goals simp [discr_ne_zero, hsℝ0, hsℂ0, h1]
  any_goals fun_prop (disch := simp [discr_ne_zero, hsℝ, hsℂ])

theorem two_mul_logDeriv_completedDedekindZeta (s : ℂ) (hs : 1 < s.re) :
    2 * logDeriv (completedDedekindZeta K) s =
      log |discr K| + nrRealPlaces K * ((s / 2).digamma - s.digamma + log 2) +
        Module.finrank ℚ K * (s.digamma - log (2 * π)) + 2 * logDeriv (dedekindZeta K) s := by
  rw [logDeriv_completedDedekindZeta K s hs, ← InfinitePlace.card_add_two_mul_card_eq_rank,
    mul_add, mul_add, mul_add, mul_div_cancel₀ _ two_ne_zero, ← mul_assoc, mul_comm 2, mul_assoc,
    mul_div_cancel₀ _ two_ne_zero]
  simp only [log_mul two_ne_zero pi_ne_zero, Complex.ofReal_add, log_abs]
  grind

end completedDedekindZeta

section nontrivialZeros

def DedekindZeta.nontrivialZeros : Set ℂ :=
  {s : ℂ | s.re ∈ Set.Icc 0 1 ∧ dedekindZeta K s = 0}

def GeneralizedRiemannHypothesis : Prop :=
  ∀ s, dedekindZeta K s = 0 → 0 < s.re → s.re < 1 → s = 1/2

end nontrivialZeros

section Odlyzko

open Complex Real

open scoped ComplexOrder

-- this uses the residue theorem and the functional equation:
theorem tada1 (Φ : ℂ → ℂ) (hΦ0 : ∀ s ∈ DedekindZeta.nontrivialZeros K, 0 ≤ Φ s)
    (hΦ1 : ∀ s, Φ (1 - s) = Φ s) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ 2 * Φ 1 + (2 * π)⁻¹ *
      ∫ t : ℝ, 2 * logDeriv (completedDedekindZeta K) (1 + ε + I * t) * Φ (1 + ε + I * t) := by
  sorry

theorem tada2 (Φ : ℂ → ℂ) (hΦ0 : ∀ s ∈ DedekindZeta.nontrivialZeros K, 0 ≤ Φ s)
    (hΦ1 : ∀ s, Φ (1 - s) = Φ s) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ 2 * Φ 1 + (2 * π)⁻¹ * (∫ t : ℝ, (log |discr K| +
      nrRealPlaces K * (((2⁻¹ + I * t) / 2).digamma - (2⁻¹ + I * t).digamma + (2 : ℝ).log) +
        Module.finrank ℚ K * (((2⁻¹ + I * t) / 2).digamma - (2 * π).log)) * Φ (2⁻¹ + I * t)) +
    (2 * π)⁻¹ * ∫ t : ℝ, 2 * logDeriv (dedekindZeta K) (1 + ε + I * t) * Φ (1 + ε + I * t) := by
  have := tada1 K Φ hΦ0 hΦ1 ε hε
  -- rw with `two_mul_logDeriv_completedDedekindZeta`
  -- split the integral
  -- shift the contour now that the nontrivial zeros are gone
  sorry

noncomputable def Φ (F : ℂ → ℂ) (s : ℂ) := ∫ x : ℝ, F x * Complex.exp ((s - 2⁻¹) * x)

theorem Φ_eq_integral_exp (F : ℂ → ℂ) (s : ℂ) :
    Φ F s = ∫ x : ℝ, F x * Complex.exp ((s - 2⁻¹) * x) :=
  rfl

theorem Φ_eq_integral_cosh (F : ℂ → ℂ) (hF : Function.Even F) (s : ℂ) :
    Φ F s = ∫ x : ℝ, F x * Complex.cosh ((s - 2⁻¹) * x) := by
  rw [Function.Even] at hF
  simp_rw [Complex.cosh, add_div, mul_add]
  rw [MeasureTheory.integral_add]
  · rw [add_comm, ← MeasureTheory.integral_neg_eq_self]
    simp_rw [ofReal_neg, hF, mul_neg, neg_neg]
    rw [← two_mul]
    simp_rw [mul_div, MeasureTheory.integral_div]
    rw [mul_div]
    rw [mul_div_cancel_left₀, Φ_eq_integral_exp]
    exact two_ne_zero
  · -- integrability, follows from extra assumptions on F
    sorry
  · -- integrability, follows from extra assumptions on F
    sorry

theorem tada3 (F : ℂ → ℂ) (hΦ0 : ∀ s ∈ DedekindZeta.nontrivialZeros K, 0 ≤ Φ F s)
    (hΦ1 : ∀ s, Φ F (1 - s) = Φ F s) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ 2 * Φ F 1 + (2 * π)⁻¹ * (∫ t : ℝ, (log |discr K| +
      nrRealPlaces K * (((2⁻¹ + I * t) / 2).digamma - (2⁻¹ + I * t).digamma + (2 : ℝ).log) +
        Module.finrank ℚ K * (((2⁻¹ + I * t) / 2).digamma - (2 * π).log)) * Φ F (2⁻¹ + I * t)) +
    (2 * π)⁻¹ * ∫ t : ℝ, 2 * logDeriv (dedekindZeta K) (1 + ε + I * t) * Φ F (1 + ε + I * t) := by
  have := tada1 K Φ hΦ0 hΦ1 ε hε
  -- rw with `two_mul_logDeriv_completedDedekindZeta`
  -- split the integral
  -- shift the contour now that the nontrivial zeros are gone
  sorry

noncomputable def φ (F : ℂ → ℂ) (t : ℂ) := Φ F (2⁻¹ + I * t)

theorem φ_def (F : ℂ → ℂ) (t : ℂ) : φ F t = Φ F (2⁻¹ + I * t) := rfl

theorem φ_eq_integral_exp (F : ℂ → ℂ) (t : ℂ) :
    φ F t = ∫ x : ℝ, F x * Complex.exp (I * t * x) := by
  rw [φ_def, Φ_eq_integral_exp, add_sub_cancel_left]

theorem φ_eq_integral_cosh (F : ℂ → ℂ) (hF : Function.Even F) (t : ℂ) :
    φ F t = ∫ x : ℝ, F x * Complex.cosh (I * t * x) := by
  rw [φ_def, Φ_eq_integral_cosh F hF, add_sub_cancel_left]

theorem tada3 (Φ : ℂ → ℂ) (hΦ0 : ∀ s ∈ DedekindZeta.nontrivialZeros K, 0 ≤ Φ s)
    (hΦ1 : ∀ s, Φ (1 - s) = Φ s) (ε : ℝ) (hε : 0 < ε) :
    0 ≤ 2 * Φ 1 + (2 * π)⁻¹ * (∫ t : ℝ, (log |discr K| +
      nrRealPlaces K * (((2⁻¹ + I * t) / 2).digamma - (2⁻¹ + I * t).digamma + (2 : ℝ).log) +
        Module.finrank ℚ K * (((2⁻¹ + I * t) / 2).digamma - (2 * π).log)) * Φ (2⁻¹ + I * t)) +
    (2 * π)⁻¹ * ∫ t : ℝ, 2 * logDeriv (dedekindZeta K) (1 + ε + I * t) * Φ (1 + ε + I * t) := by
  have := tada1 K Φ hΦ0 hΦ1 ε hε
  -- rw with `two_mul_logDeriv_completedDedekindZeta`
  -- split the integral
  -- shift the contour now that the nontrivial zeros are gone
  sorry


theorem integral_phi (F : ℂ → ℂ) (hF0 : F 0 = 1) (ε : ℝ) (hε : 0 < ε) :
    (2 * π)⁻¹ * ∫ t : ℝ, Φ F (2⁻¹ + I * t) = 1 := by
  simp_rw [Φ]
  sorry

end Odlyzko

end NumberField
