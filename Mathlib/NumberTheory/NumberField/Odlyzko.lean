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

namespace Complex -- gamma function

-- PRed
theorem differentiableAt_Gamma_one : DifferentiableAt ℂ Gamma 1 :=
  differentiableAt_Gamma 1 (by norm_cast; simp)

-- PRed
theorem continuousAt_Gamma (s : ℂ) (hs : ∀ (m : ℕ), s ≠ -↑m) : ContinuousAt Gamma s :=
  (differentiableAt_Gamma s hs).continuousAt

-- PRed
theorem continuousAt_Gamma_one : ContinuousAt Gamma 1 :=
  differentiableAt_Gamma_one.continuousAt

-- PRed
theorem not_continuousAt_Gamma_zero : ¬ ContinuousAt Gamma 0 := by
  intro h0
  have h1 : ContinuousAt (fun s ↦ Gamma (s + 1)) 0 := by
    refine ContinuousAt.comp' ?_ (continuous_add_right 1).continuousAt
    rw [zero_add]
    exact continuousAt_Gamma_one
  have h2 : ContinuousAt id (0 : ℂ) := continuousAt_id
  rw [continuousAt_iff_punctured_nhds] at h0 h1 h2
  have h3 (s : ℂ) (hs : s ∈ ({0}ᶜ : Set ℂ)): Gamma (s + 1) - s * Gamma s = 0 :=
    sub_eq_zero.mpr (Gamma_add_one s hs)
  simpa using tendsto_nhdsWithin_congr h3 (h1.sub (h2.mul h0))

-- PRed
theorem not_differentiableAt_Gamma_zero : ¬ DifferentiableAt ℂ Gamma 0 :=
  mt DifferentiableAt.continuousAt not_continuousAt_Gamma_zero

-- PRed
theorem not_continuousAt_Gamma_neg_nat (n : ℕ) : ¬ ContinuousAt Gamma (-n) := by
  induction n
  case zero =>
    rw [Nat.cast_zero, neg_zero]
    exact not_continuousAt_Gamma_zero
  case succ n ih =>
    contrapose! ih
    rw [Nat.cast_add, Nat.cast_one] at ih
    suffices ContinuousAt (fun s ↦ Gamma (s - 1 + 1)) (-n) by simpa using this
    suffices ContinuousAt (fun s ↦ Gamma (s + 1)) (-n - 1) from
      this.comp' (f := fun s ↦ s - 1) (by fun_prop)
    rw [← neg_add']
    have h0 : -(n + 1) ≠ (0 : ℂ) := neg_ne_zero.mpr n.cast_add_one_ne_zero
    exact ((continuousAt_id.mul ih).continuousWithinAt.congr Gamma_add_one
      (Gamma_add_one (-(n + 1)) h0)).continuousAt (compl_singleton_mem_nhds h0)

-- PRed
theorem not_differentiableAt_Gamma_neg_nat (n : ℕ) : ¬ DifferentiableAt ℂ Gamma (-n) :=
  mt DifferentiableAt.continuousAt (not_continuousAt_Gamma_neg_nat n)

-- PRed
theorem deriv_Gamma_add_one (s : ℂ) (hs : s ≠ 0) :
    deriv Gamma (s + 1) = Gamma s + s * deriv Gamma s := by
  by_cases! h : ∃ m : ℕ, s = -m
  · obtain ⟨m, rfl⟩ := h
    rw [← sub_neg_eq_add, ← neg_sub', ← Nat.cast_one, ← Nat.cast_sub,
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat m),
      deriv_zero_of_not_differentiableAt (not_differentiableAt_Gamma_neg_nat (m - 1)),
      Gamma_neg_nat_eq_zero, zero_add, mul_zero]
    rwa [neg_ne_zero, Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero] at hs
  · suffices HasDerivWithinAt (fun s ↦ Gamma (s + 1)) (Gamma s + s * deriv Gamma s) {0}ᶜ s by
      rw [← deriv_comp_add_const]
      exact (this.hasDerivAt (compl_singleton_mem_nhds hs)).deriv
    refine HasDerivWithinAt.congr ?_ Gamma_add_one (Gamma_add_one s hs)
    simpa using HasDerivWithinAt.mul (hasDerivWithinAt_id s {0}ᶜ)
      (differentiableAt_Gamma s h).hasDerivAt.hasDerivWithinAt

theorem meromorphic_Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicOn.Gamma

end Complex

section Complex -- logDeriv

protected theorem meromorphicOn.logDeriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    (f : 𝕜 → 𝕜) (s : Set 𝕜)
    (h : MeromorphicOn f s) : MeromorphicOn (logDeriv f) s :=
  h.deriv.div h

protected theorem Meromorphic.logDeriv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    (f : 𝕜 → 𝕜)
    (h : Meromorphic f) : Meromorphic (logDeriv f) :=
  h.deriv.div h

end Complex

namespace Complex -- digamma function

noncomputable def digamma : ℂ → ℂ := logDeriv Gamma

theorem digamma_def : digamma = logDeriv Gamma := rfl

theorem digamma_zero : digamma 0 = 0 :=
  logDeriv_eq_zero_of_not_differentiableAt Gamma 0 not_differentiableAt_Gamma_zero

theorem digamma_one : digamma 1 = - Real.eulerMascheroniConstant := by
  rw [digamma_def, logDeriv_apply, (hasDerivAt_Gamma_one).deriv, Gamma_one, div_one]

theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ - m) :
    digamma (s + 1) = digamma s + s⁻¹ := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  rw [digamma_def, logDeriv_apply, logDeriv_apply, deriv_Gamma_add_one s hs0, Gamma_add_one s hs0,
    add_div, div_mul_cancel_right₀ (Gamma_ne_zero hs), mul_div_mul_left _ _ hs0, add_comm]

theorem meromorphic_digamma : Meromorphic digamma :=
  meromorphic_Gamma.logDeriv

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

theorem differentiableAt_completedDedekindZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (completedDedekindZeta K) s :=
  sorry

theorem meromorphic_completedDedekindZeta : Meromorphic (completedDedekindZeta K) :=
  sorry

theorem completedDedekindZeta_one_sub (s : ℂ) :
    completedDedekindZeta K (1 - s) = completedDedekindZeta K s := by
  sorry

theorem completedDedekindZeta_eq_mul {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    completedDedekindZeta K s = |discr K| ^ (s / 2) * s.Gammaℝ ^ nrRealPlaces K *
      s.Gammaℂ ^ nrComplexPlaces K * dedekindZeta K s :=
  sorry

-- this will be the function that we integrate from `1 + ε - i ∞` to `1 + ε + i ∞`
theorem two_mul_logDeriv_completedDedekindZeta {s : ℂ} (hs : 1 < s.re) :
    2 * logDeriv (completedDedekindZeta K) s = nrComplexPlaces K * log 2 +
      log |discr K| + nrRealPlaces K * ((s / 2).digamma - s.digamma + log 2) +
        Module.finrank ℚ K * (s.digamma - log (2 * π)) + logDeriv (dedekindZeta K) s := by
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
