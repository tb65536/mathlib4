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

-- theorem nhdsWithin_of_notMem_discrete {X : Type*} [TopologicalSpace X] [T1Space X] {s : Set X}
--     (hs : IsDiscrete s) {x : X} (hx : x ∉ s) :
--     nhdsWithin x s = ⊥ := by
--   rw [eq_bot_iff]
--   intro t _
--   rw [mem_nhdsWithin]


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}
  {f' : E →L[𝕜] F} {x : E} {s : Set E} {c : F}

theorem HasFDerivWithinAt.eventually_ne' (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ c := by
  rcases eq_or_ne (f x) c with rfl | hc
  · rw [nhdsWithin, diff_eq, ← inf_principal, ← inf_assoc, eventually_inf_principal]
    have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
      isBigO_iff.2 <| hf'.imp fun C hC => Eventually.of_forall fun z => hC _
    have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.isLittleO.trans_isBigO A
    simpa [not_imp_not, sub_eq_zero] using (A.trans this.isBigO_symm).eq_zero_imp
  · exact (h.continuousWithinAt.eventually_ne hc).filter_mono <| by gcongr; apply diff_subset

/-- We need to assume that `t` is closed as otherwise `t` could accumulate to the derivative. -/
theorem HasFDerivWithinAt.eventually_notMem_discrete {t : Set F} (ht : IsDiscrete t)
    (ht' : IsClosed t)
    (h : HasFDerivWithinAt f f' s x)
    (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ∉ t := by
  refine (h.eventually_ne' (c := f x) hf').mp ?_
  apply Eventually.filter_mono (nhdsWithin_le_of_mem
    (mem_of_superset self_mem_nhdsWithin diff_subset))
  clear hf'
  replace h := h.continuousWithinAt.tendsto
  simp only [not_imp_not, ← Set.mem_preimage]
  rw [← Filter.eventually_inf_principal]
  refine (eventually_map (m := f) (P := fun y ↦ y = f x)).mp ?_
  rw [Filter.map_inf_principal_preimage]
  apply Eventually.filter_mono (inf_le_inf_right _ h)
  rw [← nhdsWithin]
  by_cases hf : f x ∈ t
  · rw [ht.nhdsWithin (f x) hf, eventually_pure]
  · rw [not_neBot.mp (mt ht'.mem_of_nhdsWithin_neBot hf)]
    exact eventually_bot

end temp

section temp

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

/-- If a function is valued in a discrete set at a set of points that accumulates to `x` in `s`,
then its derivative within `s` at `x` equals zero,
either because it has derivative zero or because it isn't differentiable at this point. -/
theorem derivWithin_zero_of_frequently_mem_discrete {t : Set F} [DiscreteTopology t]
    (h : ∃ᶠ y in 𝓝[s \ {x}] x, f y ∈ t) :
    derivWithin f s x = 0 := by
  by_cases hf : DifferentiableWithinAt 𝕜 f s x
  · contrapose! h
    have := hf.hasDerivWithinAt.eventually_ne (c :)
  · exact derivWithin_zero_of_not_differentiableWithinAt hf

end temp

theorem deriv_const_cpow {f : ℂ → ℂ} {c : ℂ} (hf : Differentiable ℂ f) :
    deriv (fun x ↦ c ^ f x) = fun x ↦ c ^ f x * Complex.log c * deriv f x := by
  by_cases hc : c = 0
  · simp [hc]
    -- function is either zero or one
    sorry
  · ext x
    exact ((hf x).hasDerivAt.const_cpow (Or.inl hc)).deriv

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

theorem logDeriv_cpow (a : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    logDeriv (fun s ↦ a ^ f s) = log a • deriv f := by
  rw [logDeriv, deriv_const_cpow hf]
  ext x
  by_cases ha : a = 0
  · simp [ha]
  apply div_eq_of_eq_mul (cpow_ne_zero_iff.mpr (Or.inl ha))
  simp only
  rw [mul_assoc, mul_comm, Pi.smul_apply, smul_eq_mul]

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
  rw [logDeriv_mul, logDeriv_mul, logDeriv_mul]
  sorry

-- this will be the function that we integrate from `1 + ε - i ∞` to `1 + ε + i ∞`
theorem two_mul_logDeriv_completedDedekindZeta (s : ℂ) (hs : 1 < s.re) :
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
