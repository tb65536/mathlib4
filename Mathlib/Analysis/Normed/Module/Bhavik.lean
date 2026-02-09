/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib


/-!
# Spectral theory of compact operators
This file develops the spectral theory of compact operators on Banach spaces.
The main result is the Fredholm alternative for compact operators.
## Main results
* `antilipschitz_of_not_hasEigenvalue`: if `T` is a compact operator and `μ ≠ 0` is not an
  eigenvalue, then `T - μI` is antilipschitz.
* `fredholm_alternative`: the Fredholm alternative for compact operators.
-/

-- let X be a Banach space
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
-- and T be a compact operator on it
variable {T : X →L[𝕜] X}

open Module End

/-- If a continuous linear map `f` satisfies `‖x‖ = 1 → 1 ≤ K * ‖f x‖`, then `f` is
antilipschitz with constant `K`. -/
lemma ContinuousLinearMap.antilipschitz_of_bound_of_norm_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {K : NNReal} (h : ∀ x, ‖x‖ = 1 → 1 ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  ContinuousLinearMap.antilipschitz_of_bound _ fun x ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    simpa [norm_smul, field] using h ((‖x‖⁻¹ : 𝕜) • x) (norm_smul_inv_norm hx)

open Filter Topology in
/-- If `T : X →L[𝕜] X` is a compact operator on a Banach space `X`, and `μ ≠ 0` is not an
eigenvalue of `T`, then `T - μ • 1` is antilipschitz.
This is a useful step in the proof of the Fredholm alternative. -/
theorem antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) (h : ¬ HasEigenvalue (T : End 𝕜 X) μ) :
    ∃ K > 0, AntilipschitzWith K (T - μ • 1 : X →L[𝕜] X) := by
  suffices ∃ c > 0, ∀ x, ‖x‖ = 1 → c ≤ ‖(T - μ • 1) x‖ by
    obtain ⟨c, hc', hc⟩ := this
    refine ⟨c.toNNReal⁻¹, by positivity, ?_⟩
    apply ContinuousLinearMap.antilipschitz_of_bound_of_norm_one
    simpa [NNReal.coe_inv, le_inv_mul_iff₀', hc'] using hc
  -- Suppose not, then we can find a sequence of unit vectors xₙ such that (T - μ • 1) xₙ → 0.
  by_contra!
  obtain ⟨φ, hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
  have (n : ℕ) : ∃ x, ‖x‖ = 1 ∧ ‖(T - μ • 1) x‖ < φ n := this (φ n) (hφ_pos n)
  choose x hx_norm hx_bound using this
  have hx_lim : Tendsto (fun n ↦ (T - μ • 1) (x n)) atTop (𝓝 0) := squeeze_zero_norm (by grind) hφ
  -- Define the sequence of vectors yₙ := T xₙ
  let y_ (n : ℕ) : X := T (x n)
  -- which are bounded away from zero.
  have hy_lower : ∀ᶠ n in atTop, ‖μ‖ / 2 ≤ ‖y_ n‖ := by
    filter_upwards [hφ.eventually_le_const (show ‖μ‖ / 2 > 0 by positivity)] with n hn
    have h₁ : ‖T (x n) - μ • x n‖ < φ n := by simpa using hx_bound n
    have h₂ : ‖μ‖ ≤ ‖T (x n)‖ + ‖T (x n) - μ • x n‖ := by
      simpa [norm_smul, hx_norm] using norm_le_norm_add_norm_sub (T (x n)) (μ • x n)
    grind
  -- The sequence yₙ is contained in the image of the closed unit ball under T, which is compact,
  -- since T is, so we can extract a convergent subsequence, and say y_ (ψ n) → y.
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (x := y_) (fun n ↦ hK' ⟨x n, by simp [*], rfl⟩)
  -- However (T - μ • 1) yₙ = T ((T - μ • 1) xₙ) → 0
  have hy_lim : Tendsto (fun n ↦ (T - μ • 1) (y_ n)) atTop (nhds 0) := by
    have : Tendsto (fun n ↦ _) _ _ := T.continuous.continuousAt.tendsto.comp hx_lim
    simpa using this
  -- so (T - μ • 1) y = 0.
  have hy_eigen' : (T - μ • 1) y = 0 := by
    apply tendsto_nhds_unique _ (hy_lim.comp hψ.tendsto_atTop)
    have : Continuous (T - μ • 1 : X →L[𝕜] X) := by fun_prop
    exact this.continuousAt.tendsto.comp hψy
  -- Since yₙ are bounded away from 0, we must have y ≠ 0.
  have hy_ne : y ≠ 0 := by
    rintro rfl
    suffices ∀ᶠ n : ℕ in atTop, False by rwa [eventually_const] at this
    rw [NormedAddCommGroup.tendsto_nhds_zero] at hψy
    specialize hψy (‖μ‖ / 2) (by positivity)
    filter_upwards [hψ.tendsto_atTop.eventually hy_lower, hψy] using by grind
  -- So y is an eigenvector of T with eigenvalue μ,
  have : HasEigenvector (T : End 𝕜 X) μ y := by
    simpa [hasEigenvector_iff, mem_genEigenspace_one, hy_ne, sub_eq_zero] using hy_eigen'
  -- which is a contradiction.
  exact h (hasEigenvalue_of_hasEigenvector this)

/-- A variation of Riesz's lemma where we get a vector `x₀` of norm exactly 1. -/
theorem riesz_lemma_one
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ∃ (x : E), x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ ∉ F, ‖x₀‖ = 1 ∧ ∀ y ∈ F, r ≤ ‖x₀ - y‖ := by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) • y‖ := by
    rw [norm_smul, norm_inv, norm_algebraMap', norm_norm]
  have h₁ := h ((‖x₀‖ : 𝕜) • y) (F.smul_mem _ hy)
  rwa [← le_inv_mul_iff₀' (by simpa), ← h₂, smul_sub, inv_smul_smul₀] at h₁
  simpa using hx₀'

/--
Given an endomorphism `S` of a normed space that's a closed embedding but not surjective, we can
find a sequence of unit vectors `f n`, such that `f n` is in the range of `S ^ n` but is at least
`1/2` away from any vector in the range of `S ^ (n + 1)`.
-/
theorem thing {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {S : End 𝕜 X}
    (hS_not_surj : ¬ (S : X → X).Surjective)
    (hS_anti : Topology.IsClosedEmbedding S)
    {r : ℝ} (hr : r < 1) :
    ∃ f : ℕ → X,
      (∀ n, ‖f n‖ = 1) ∧ (∀ n, f n ∈ (S ^ n).range) ∧
      (∀ n, ∀ y ∈ (S ^ (n + 1)).range, r ≤ ‖f n - y‖) := by
  obtain ⟨x, hx⟩ : ∃ x : X, ∀ y, S y ≠ x := by simpa [Function.Surjective] using hS_not_surj
  let V (n : ℕ) : Submodule 𝕜 X := S.iterateRange n
  have hV_succ (n : ℕ) : V (n + 1) = (V n).map (S : End 𝕜 X) := LinearMap.iterateRange_succ
  have hV_closed (n : ℕ) : IsClosed (V n : Set X) := by
    induction n with
    | zero => simp [V, Module.End.one_eq_id]
    | succ n ih =>
      rw [hV_succ]
      apply hS_anti.isClosedMap _ ih
  have x (n : ℕ) : ∃ x ∈ V n, ‖x‖ = 1 ∧ ∀ y ∈ V (n + 1), r ≤ ‖x - y‖ := by
    have h₁ : IsClosed (Submodule.comap (V n).subtype (V (n + 1)) : Set (V n)) := by
      simpa using (hV_closed (n + 1)).preimage_val
    have h₂ : ∃ x : V n, x ∉ (V (n + 1)).comap (V n).subtype := by
      simpa [iterate_succ, V, (iterate_injective hS_anti.injective n).eq_iff] using by use x
    obtain ⟨⟨x, hx⟩, hx', hxn, hxy⟩ := riesz_lemma_one h₁ h₂ hr
    simp only [Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_norm,
      AddSubgroupClass.coe_sub, Subtype.forall] at hx' hxn hxy
    exact ⟨x, hx, hxn, fun y hy ↦ hxy y (S.iterateRange.monotone (by simp) hy) hy⟩
  choose x hxv hxn hxy using x
  exact ⟨x, hxn, hxv, hxy⟩

/-- The Fredholm alternative for compact operators: if `T` is a compact operator and `μ ≠ 0`,
then either `μ` is an eigenvalue of `T`, or `μ` is in the resolvent set of `T`. -/
theorem fredholm_alternative [CompleteSpace X] (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) : HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
  by_contra!
  obtain ⟨h₁, h₂⟩ := this
  let (eq := hS) S := (T - μ • 1)
  replace h₂ : ¬ (S : X → X).Bijective := by
    rw [spectrum.mem_resolventSet_iff, ← IsUnit.neg_iff,
      ContinuousLinearMap.isUnit_iff_bijective] at h₂
    convert h₂
    ext x
    simp [S]
  obtain ⟨K, -, hK : AntilipschitzWith K S⟩ := antilipschitz_of_not_hasEigenvalue hT hμ h₁
  obtain ⟨f, hf_norm, hf_mem, hf_far⟩ := thing (mt (.intro hK.injective) h₂)
    (hK.isClosedEmbedding S.uniformContinuous) (show 2⁻¹ < 1 by norm_num)
  have hf_mem' (n : ℕ) : S (f n) ∈ ((S : End 𝕜 X) ^ (n + 1)).range := by
    rw [iterate_succ']
    rw [LinearMap.range_comp]
    exact ⟨f n, hf_mem n, rfl⟩
  have hp : Pairwise fun x₁ x₂ ↦ 2⁻¹ * ‖μ‖ ≤ ‖T (f x₁) - T (f x₂)‖ := by
    intro m n hmn
    wlog! hmn' : m < n generalizing m n
    · rw [norm_sub_rev]
      exact this hmn.symm (by order)
    let u : X := μ⁻¹ • (S (f n) - S (f m) + μ • f n)
    have hu : μ • (f m - u) = (T (f m) - T (f n)) := by
      rw [smul_sub, smul_inv_smul₀ hμ]
      simp [S]
      linear_combination (norm := module)
    have : u ∈ ((S : End 𝕜 X) ^ (m + 1)).range := by
      apply Submodule.smul_mem _ _ (Submodule.add_mem _ _ _)
      · exact Submodule.sub_mem _ ((S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem' _))
          (hf_mem' _)
      · exact Submodule.smul_mem _ μ ((S : End 𝕜 X).iterateRange.monotone (by lia) (hf_mem n))
    rw [← hu, norm_smul, mul_comm]
    grw [hf_far _ u this]
  obtain ⟨K, hK, hK'⟩ := hT.image_closedBall_subset_compact 1
  obtain ⟨y, hyK, ψ, hψ, hψy⟩ := hK.tendsto_subseq (fun n ↦ hK' ⟨f n, by simp [*], rfl⟩)
  replace hψy := hψy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hψy
  obtain ⟨N, hN⟩ := hψy (2⁻¹ * ‖μ‖) (by positivity)
  simp only [dist_eq_norm_sub, ContinuousLinearMap.coe_coe, Function.comp_apply] at hN
  have := hN (N + 1) (by simp)
  refine this.not_ge ?_
  apply hp
  simp [hψ.injective.eq_iff]

def ContinuousLinearMap.toLinearMapAlgHom
    {R₁ : Type*} [CommSemiring R₁] {M₁ : Type*}
    [TopologicalSpace M₁] [CommRing M₁] [Algebra R₁ M₁] [IsScalarTower R₁ R₁ M₁]
    [ContinuousAdd M₁] [ContinuousConstSMul R₁ M₁] [IsTopologicalAddGroup M₁] :
    (M₁ →L[R₁] M₁) →ₐ[R₁] M₁ →ₗ[R₁] M₁ where
  toRingHom := ContinuousLinearMap.toLinearMapRingHom
  commutes' r := by
    ext x
    simp

theorem ContinuousLinearMap.isUnit_toLinearMap_iff {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] {T : X →L[𝕜] X} :
    IsUnit T ↔ IsUnit (T : End 𝕜 X) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective, Module.End.isUnit_iff]
  rfl

theorem ContinuousLinearMap.spectrum_eq [CompleteSpace X] :
    spectrum 𝕜 (T : X →L[𝕜] X) = spectrum 𝕜 (T : End 𝕜 X) := by
  ext μ
  rw [spectrum, resolventSet, Set.mem_compl_iff, Set.mem_setOf,
    ContinuousLinearMap.isUnit_toLinearMap_iff]
  rfl

theorem hasEigenvalue_iff_mem_spectrum [CompleteSpace X] (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T := by
  constructor
  · intro hμ'
    rw [ContinuousLinearMap.spectrum_eq]
    exact hμ'.mem_spectrum
  · intro h
    exact (fredholm_alternative hT hμ).resolve_right h

section spectral

open Module.End

section pain

open Complex TensorProduct

theorem IsSelfAdjoint.spectralRadius_eq_nnnorm' {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] [CompleteSpace X] {T : X →L[𝕜] X} (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  by_cases h𝕜 : RCLike.im (RCLike.I : 𝕜) = 1
  · let f := RCLike.complexLinearIsometryEquiv h𝕜
    let : NormedAlgebra ℂ 𝕜 := sorry
    let : NormedSpace ℂ X := NormedSpace.restrictScalars ℂ 𝕜 X
    let : InnerProductSpace ℂ X :=
    { inner := sorry
      norm_sq_eq_re_inner := sorry
      conj_inner_symm := sorry
      add_left := sorry
      smul_left := sorry }
    let : Module ℂ X := sorry
    have : LinearMap.CompatibleSMul X X ℂ 𝕜 := sorry
    let T' : X →L[ℂ] X := T.restrictScalars ℂ
    have : spectralRadius 𝕜 T = spectralRadius ℂ T' := sorry
    let f' : (X →L[𝕜] X) →ₐ (X →L[ℂ] X) := sorry
    sorry


  let f : 𝕜 →ₐ[ℝ] ℂ :=
  { toFun x := RCLike.re x + RCLike.im x * I
    map_add' x y := by simp only [map_add, ofReal_add]; ring
    map_mul' x y := by
      simp only [RCLike.mul_re, ofReal_sub, ofReal_mul, RCLike.mul_im, ofReal_add]
      ring_nf
      rw [I_sq]
      ring
    map_one' := by simp
    map_zero' := by simp
    commutes' := by simp }
  let : Algebra 𝕜 ℂ := f.toAlgebra

  let : NormedAddCommGroup (TensorProduct 𝕜 ℂ X) :=
  { norm := sorry
    dist_self := sorry
    dist_comm := sorry
    dist_triangle := sorry
    eq_of_dist_eq_zero := sorry }
  let : InnerProductSpace ℂ (TensorProduct 𝕜 ℂ X) :=
  { norm_smul_le := sorry
    inner := sorry
    norm_sq_eq_re_inner := sorry
    conj_inner_symm := sorry
    add_left := sorry
    smul_left := sorry }
  have : CompleteSpace (TensorProduct 𝕜 ℂ X) := sorry
  let T' : TensorProduct 𝕜 ℂ X →L[ℂ] TensorProduct 𝕜 ℂ X :=
    ⟨T.toLinearMap.baseChange ℂ, sorry⟩
  have hT' : IsSelfAdjoint T' := sorry
  have h1 : spectralRadius ℂ T' = spectralRadius 𝕜 T := sorry
  have h2 : ‖T'‖₊ = ‖T‖₊ := sorry
  rw [← h1, ← h2]
  exact hT'.spectralRadius_eq_nnnorm

end pain

theorem IsCompactOperator.forall_eigenspace_ne_bot_iff_eq_zero
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
    {T : X →L[𝕜] X} (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 X) μ → μ = 0) ↔ T = 0 := by
  constructor
  · intro h
    replace h : spectrum 𝕜 T ⊆ {0} := by
      intro μ hμ
      contrapose! h
      exact ⟨μ, (hasEigenvalue_iff_mem_spectrum hT h).mpr hμ, h⟩
    rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hT'
    rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← hT'.spectralRadius_eq_nnnorm', spectralRadius]
    obtain (h | h) := Set.subset_singleton_iff_eq.mp h <;> simp [h]
  · rintro rfl μ h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    simp [hasEigenvector_iff] at hv
    grind [smul_eq_zero]

variable {X 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {T : X →L[𝕜] X}
theorem spectral_theorem_aux' [CompleteSpace X] (hT : T.IsSymmetric) (hT' : IsCompactOperator T) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 X) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ →L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ :=
  { cont := by
      simp only [LinearMap.restrict, LinearMap.codRestrict, LinearMap.domRestrict_apply,
        ContinuousLinearMap.coe_coe, AddHom.toFun_eq_coe, AddHom.coe_mk]
      fun_prop
    __ := T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant }
  have hS_compact : IsCompactOperator S :=
    hT'.restrict' hT.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT.restrict_invariant (hT.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ) μ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Subtype.ext_iff, Submodule.coe_zero, ← Submodule.mem_bot 𝕜,
      ← Submodule.inf_orthogonal_eq_bot (⨆ μ, eigenspace T μ : Submodule 𝕜 X)]
    refine ⟨Submodule.mem_iSup_of_mem μ ?_, v.2⟩
    rw [mem_eigenspace_iff] at hv ⊢
    exact Subtype.ext_iff.mp hv
  have h μ : HasEigenvalue (S : End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ) μ → μ = 0 := by
    intro hμ
    rw [hasEigenvalue_iff] at hμ
    specialize hS μ
    contradiction
  rw [IsCompactOperator.forall_eigenspace_ne_bot_iff_eq_zero hS_compact hS_symm] at h
  by_contra! hV
  rw [← Submodule.nontrivial_iff_ne_bot] at hV
  specialize hS 0
  simp [h] at hS

variable {X 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {T : X →L[𝕜] X}
theorem spectral_theorem' [CompleteSpace X] (hT : T.IsSymmetric) (hT' : IsCompactOperator T) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 X) μ) = ⊤ := by
  have := spectral_theorem_aux' hT hT'
  sorry

end spectral
