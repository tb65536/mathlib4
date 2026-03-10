import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

open Module.End

-- PRed
instance ContinuousLinearMap.isClosed_genEigenspace {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T1Space M]
    [ContinuousConstSMul R M] [IsTopologicalAddGroup M]
    (f : M →L[R] M)
    (μ : R) (n : ℕ) : IsClosed (genEigenspace (f : Module.End R M) μ n : Set M) := by
  rw [genEigenspace_nat, one_eq_id, ← coe_id, ← coe_smul, ← coe_sub, ← coe_pow]
  apply ContinuousLinearMap.isClosed_ker

-- PRed
instance ContinuousLinearMap.isClosed_eigenspace {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T1Space M]
    [ContinuousConstSMul R M] [IsTopologicalAddGroup M]
    (f : M →L[R] M)
    (μ : R) : IsClosed (eigenspace (f : Module.End R M) μ : Set M) :=
  isClosed_genEigenspace f μ 1

section spectral

open Module.End

-- PRed
section pain

open Complex TensorProduct

open InnerProductSpace RCLike

theorem ContinuousLinearMap.rayleighQuotient_le_of_mem_resolventSet
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    {T : X →L[𝕜] X} (t : ℝ) (ht : 0 < t) (hT' : (algebraMap ℝ 𝕜) t ∈ resolventSet 𝕜 T) :
    ∃ c > 0, ∀ x, T.rayleighQuotient x ≤ (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c := by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (antilipschitz_of_isEmbedding _ (isHomeomorph_of_isUnit hT').isEmbedding)
  refine ⟨min (c ^ 2 / (2 * t)) ((t ^ 2 + ‖T‖ ^ 2) / (2 * t)), by positivity, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  suffices T.rayleighQuotient x ≤ (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c ^ 2 / (2 * t) by
    grw [this, min_le_left]
  rw [rayleighQuotient, reApplyInnerSelf_apply]
  specialize hc x
  rw [← sq_le_sq₀ (by positivity) (by positivity), sub_apply, algebraMap_apply,
    norm_sub_sq (𝕜 := 𝕜), inner_re_symm] at hc
  grw [le_opNorm] at hc
  simp [inner_smul_right, norm_smul, abs_of_pos ht] at hc
  field_simp
  grind

theorem ContinuousLinearMap.rayleighQuotient_le_of_norm_mem_resolventSet
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [Nontrivial X] [InnerProductSpace 𝕜 X]
    {T : X →L[𝕜] X} (hT' : algebraMap ℝ 𝕜 ‖T‖ ∈ resolventSet 𝕜 T) :
    ∃ c > 0, ∀ x, T.rayleighQuotient x ≤ ‖T‖ - c := by
  by_cases hT0 : T = 0
  · simp [hT0, spectrum.mem_resolventSet_iff] at hT'
  obtain ⟨c, hc0, hc⟩ := T.rayleighQuotient_le_of_mem_resolventSet ‖T‖ (by positivity) hT'
  refine ⟨c, hc0, fun x ↦ ?_⟩
  grw [hc]
  field_simp
  grind

theorem ContinuousLinearMap.abs_rayleighQuotient_le_of_norm_mem_resolventSet
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [Nontrivial X] [InnerProductSpace 𝕜 X]
    {T : X →L[𝕜] X} (hT' : algebraMap ℝ 𝕜 ‖T‖ ∈ resolventSet 𝕜 T)
      (hT'' : algebraMap ℝ 𝕜 (-‖T‖) ∈ resolventSet 𝕜 T) :
    ∃ c > 0, ∀ x, |T.rayleighQuotient x| ≤ ‖T‖ - c := by
  replace hT'' : (algebraMap ℝ 𝕜) (‖-T‖) ∈ resolventSet 𝕜 (-T) := by
    rwa [resolventSet_neg, Set.mem_neg, ← map_neg, norm_neg]
  obtain ⟨c, hc0, hc⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hT'
  obtain ⟨d, hd0, hd⟩ := (-T).rayleighQuotient_le_of_norm_mem_resolventSet hT''
  refine ⟨min c d, lt_min hc0 hd0, fun x ↦ ?_⟩
  specialize hc x
  specialize hd x
  rw [rayleighQuotient_neg_apply, norm_neg] at hd
  grind

theorem ContinuousLinearMap.spectralRadius_eq_nnnorm
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] [CompleteSpace X] {T : X →L[𝕜] X} (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  cases subsingleton_or_nontrivial X
  · simp
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T)
  suffices h : algebraMap ℝ 𝕜 ‖T‖ ∈ spectrum 𝕜 T ∨ algebraMap ℝ 𝕜 (-‖T‖) ∈ spectrum 𝕜 T by
    rcases h with h | h <;> exact le_trans (by simp) (le_biSup _ h)
  simp_rw [spectrum, Set.mem_compl_iff]
  by_contra! h
  obtain ⟨c, hc0, hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
  grind [ciSup_le hc, norm_eq_iSup_rayleighQuotient T hT.isSymmetric]

end pain

open Module

variable {X 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  {T : X →L[𝕜] X}

theorem IsCompactOperator.forall_eigenspace_ne_bot_iff_eq_zero
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 X) μ → μ = 0) ↔ T = 0 := by
  constructor
  · intro h
    replace h : spectrum 𝕜 T ⊆ {0} := by
      intro μ hμ
      contrapose! h
      exact ⟨μ, (hasEigenvalue_iff_mem_spectrum hT h).mpr hμ, h⟩
    rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hT'
    rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← T.spectralRadius_eq_nnnorm hT', spectralRadius]
    obtain (h | h) := Set.subset_singleton_iff_eq.mp h <;> simp [h]
  · rintro rfl μ h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    simp [hasEigenvector_iff] at hv
    grind [smul_eq_zero]

set_option backward.isDefEq.respectTransparency false in
theorem spectral_theorem (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 X) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ →L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 X)ᗮ :=
  { cont := by
      simp only [LinearMap.restrict, LinearMap.codRestrict, LinearMap.domRestrict_apply,
        ContinuousLinearMap.coe_coe, AddHom.toFun_eq_coe, AddHom.coe_mk]
      fun_prop
    __ := T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant }
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT'.restrict_invariant (hT'.orthogonalComplement_iSup_eigenspaces_invariant)
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

theorem spectral_theorem' (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace (T : Module.End 𝕜 X) μ) := by
  have inv : ∀ x ∈ eigenspace (T : Module.End 𝕜 X) μ, T x ∈ eigenspace (T : Module.End 𝕜 X) μ := by
    intro x hx
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [hx, map_smul, hx]
  have : T.restrict inv = μ • 1 := by
    ext x
    exact mem_eigenspace_iff.mp x.2
  have h2 := hT.restrict' inv
  rw [this, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at h2
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end spectral

-- goal: prove that characters separate points
-- If G is a nontrivial group, then convolving with a function h gives a compact operator on L^2(G)
-- and the spectral theorem gives a decomposition of L^2(G) into finite-dimensional representations
-- and as long as one of these is nontrivial, then we can get a non-trivial irreducible
-- representation which must be one dimensional by Schur's lemma.
