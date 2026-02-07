import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.LinearAlgebra.Eigenspace.Basic

section fredholm

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable {T : X →L[𝕜] X}
theorem fredholm_alternative [CompleteSpace X] (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T : Module.End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T := by
  sorry

end fredholm
section spectral

open Module.End

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {T : X →L[ℂ] X}
theorem spectral_theorem_aux [CompleteSpace X] (hT : T.IsSymmetric) (hT' : IsCompactOperator T) :
    (⨆ μ, eigenspace (T : Module.End ℂ X) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule ℂ X)ᗮ →L[ℂ] (⨆ μ, eigenspace T μ : Submodule ℂ X)ᗮ :=
  { cont := by
      simp only [LinearMap.restrict, LinearMap.codRestrict, LinearMap.domRestrict_apply,
        ContinuousLinearMap.coe_coe, AddHom.toFun_eq_coe, AddHom.coe_mk]
      fun_prop
    __ := T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant }
  have hS_compact : IsCompactOperator S :=
    hT'.restrict' hT.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT.restrict_invariant (hT.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End ℂ (⨆ μ, eigenspace T μ : Submodule ℂ X)ᗮ) μ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Subtype.ext_iff, Submodule.coe_zero, ← Submodule.mem_bot ℂ,
      ← Submodule.inf_orthogonal_eq_bot (⨆ μ, eigenspace T μ : Submodule ℂ X)]
    refine ⟨Submodule.mem_iSup_of_mem μ ?_, v.2⟩
    rw [mem_eigenspace_iff] at hv ⊢
    exact Subtype.ext_iff.mp hv
  have h μ : μ ∈ spectrum ℂ S → μ = 0 := by
    rw [spectrum, Set.mem_compl_iff, not_imp_comm]
    intro hμ
    apply (fredholm_alternative hS_compact hμ).resolve_left
    rw [hasEigenvalue_iff, not_ne_iff]
    apply hS
  by_contra! hV
  rw [← Submodule.nontrivial_iff_ne_bot] at hV
  replace h : spectrum ℂ S = {0} :=
    Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨spectrum.nonempty S, h⟩
  obtain ⟨μ, hμ1, hμ2⟩ := spectrum.exists_nnnorm_eq_spectralRadius S
  rw [h, Set.mem_singleton_iff] at hμ1
  rw [hμ1, nnnorm_zero, ENNReal.coe_zero] at hμ2
  replace h := hS_symm.isSelfAdjoint.toReal_spectralRadius_complex_eq_norm.symm
  rw [← hμ2, ENNReal.toReal_zero, norm_eq_zero] at h
  specialize hS 0
  simp [h] at hS

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {T : X →L[ℂ] X}
theorem spectral_theorem [CompleteSpace X] (hT : T.IsSymmetric) (hT' : IsCompactOperator T) :
    (⨆ μ, eigenspace (T : Module.End ℂ X) μ) = ⊤ := by
  have := spectral_theorem_aux hT hT'
  sorry

end spectral
