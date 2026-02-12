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

@[rclike_simps]
theorem RCLike.re_mul_ofReal {K : Type*} [RCLike K] (z : K) (r : ℝ) : re (z * ↑r) = re z * r := by
  rw [mul_comm, re_ofReal_mul, mul_comm]

theorem parallelogram_law_with_norm_sq (𝕜 : Type*) {E : Type*}
    [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simpa only [sq] using parallelogram_law_with_norm 𝕜 x y

namespace ContinuousLinearMap

open InnerProductSpace RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E)

theorem rayleighQuotient_le_norm (x : E) :
    |T.rayleighQuotient x| ≤ ‖T‖ := by
  grw [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_sq, abs_re_le_norm,
    norm_inner_le_norm, le_opNorm, mul_assoc, ← sq, mul_div_assoc]
  exact mul_le_of_le_one_right T.opNorm_nonneg (div_self_le_one (‖x‖ ^ 2))

theorem bddAbove_rayleighQuotient : BddAbove (Set.range fun x ↦ |T.rayleighQuotient x|) :=
  ⟨‖T‖, fun _ ⟨y, h⟩ ↦ h ▸ T.rayleighQuotient_le_norm y⟩

theorem norm_eq_iSup_rayleighQuotient (hT : T.IsSymmetric) :
    ‖T‖ = ⨆ x, |T.rayleighQuotient x| := by
  set M := ⨆ x, |T.rayleighQuotient x|
  have nonneg : 0 ≤ M := le_ciSup_of_le T.bddAbove_rayleighQuotient 0 (abs_nonneg _)
  replace hM x : |re ⟪T x, x⟫_𝕜| ≤ M * ‖x‖ ^ 2 := by
    have hM : |T.rayleighQuotient x| ≤ M := le_ciSup T.bddAbove_rayleighQuotient x
    by_cases hx : 0 < ‖x‖ ^ 2
    · rwa [rayleighQuotient, abs_div, abs_sq, reApplyInnerSelf, div_le_iff₀ hx] at hM
    · simp_all
  refine le_antisymm ?_ (ciSup_le T.rayleighQuotient_le_norm)
  refine opNorm_le_of_unit_norm nonneg fun x hx ↦ ?_
  have key x y (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : |re ⟪T x, y⟫_𝕜| ≤ M := by
    transitivity M * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 4
    · have key := congrArg re (add_conj ⟪T x, y⟫_𝕜)
      rw [map_add, conj_inner_symm, ← coe_coe, ← hT, coe_coe, re_mul_ofReal, ofNat_re] at key
      grind [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    · rw [parallelogram_law_with_norm_sq 𝕜 x y, hx, hy]
      grind
  by_cases hTx : ‖T x‖ = 0
  · rwa [hTx]
  specialize key x (((‖T x‖⁻¹ : ℝ) : 𝕜) • T x) hx (by simp [norm_smul, hTx])
  rwa [inner_smul_right, inner_self_eq_norm_sq_to_K, ← ofReal_pow, ← ofReal_mul, ofReal_re,
    inv_mul_eq_div, sq, mul_self_div_self, abs_norm] at key

end ContinuousLinearMap

section spectral

open Module.End

section pain

open Complex TensorProduct

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
