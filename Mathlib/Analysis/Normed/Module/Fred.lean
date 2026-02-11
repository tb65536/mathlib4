import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.Bhavik
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.LinearAlgebra.Eigenspace.Basic

section spectral

open Module.End

section pain

open Complex TensorProduct

theorem ContinuousLinearMap.rayleighQuotient_le_norm
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (x : E) :
    |T.rayleighQuotient x| ≤ ‖T‖ := by
  sorry

theorem ContinuousLinearMap.iSup_rayleighQuoteint_eq_norm
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (x : E) :
    (⨆ x, T.rayleighQuotient x) = ‖T‖ := by
  sorry

theorem IsSelfAdjoint.spectralRadius_eq_nnnorm' {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] [CompleteSpace X] {T : X →L[𝕜] X} (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  cases subsingleton_or_nontrivial X
  · simp
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T)
  -- can also shift the minus sign
  suffices h : algebraMap ℝ 𝕜 ‖T‖ ∈ spectrum 𝕜 T ∨ -algebraMap ℝ 𝕜 ‖T‖ ∈ spectrum 𝕜 T by
    rcases h with h | h <;> exact le_trans (by simp) (le_biSup _ h)
  -- norm or its negative is approximated by Rayleigh quotients
  simp_rw [spectrum, Set.mem_compl_iff, spectrum.mem_resolventSet_iff]
  -- cannot be invertible
  sorry

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
    rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← hT'.spectralRadius_eq_nnnorm', spectralRadius]
    obtain (h | h) := Set.subset_singleton_iff_eq.mp h <;> simp [h]
  · rintro rfl μ h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    simp [hasEigenvector_iff] at hv
    grind [smul_eq_zero]

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

end spectral
