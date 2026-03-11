import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

open Module End

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
