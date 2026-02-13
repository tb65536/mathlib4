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

-- PRed
theorem ContinuousLinearMap.isHomeomorph_of_isUnit
    {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] {T : X →L[𝕜] X} (hT : IsUnit T) :
    IsHomeomorph T := by
  obtain ⟨u, rfl⟩ := hT
  let f : X ≃ₜ X :=
  { toFun := u.1
    invFun := u⁻¹.1
    left_inv x := by rw [← mul_apply, Units.inv_mul, one_apply]
    right_inv x := by rw [← mul_apply, Units.mul_inv, one_apply] }
  exact f.isHomeomorph

-- PRed, with name change
theorem parallelogram_law_with_norm_sq (𝕜 : Type*) {E : Type*}
    [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  simpa only [sq] using parallelogram_law_with_norm 𝕜 x y

-- PRed
@[simp]
theorem ContinuousLinearMap.rayleighQuotient_zero_apply
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x : E) :
    rayleighQuotient (0 : E →L[𝕜] E) x = 0 := by
  simp [reApplyInnerSelf_apply]

-- PRed
@[simp]
theorem ContinuousLinearMap.rayleighQuotient_apply_zero
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) :
    rayleighQuotient T 0 = 0 := by
  simp [reApplyInnerSelf_apply]

-- PRed
@[simp]
theorem ContinuousLinearMap.rayleighQuotient_neg_apply {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (x : E) :
    rayleighQuotient (-T) x = -rayleighQuotient T x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, neg_div]

-- PRed
@[simp]
theorem ContinuousLinearMap.rayleighQuotient_apply_neg {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E) (x : E) :
    rayleighQuotient T (-x) = rayleighQuotient T x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply]

-- PRed
theorem resolventSet_neg (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] (a : A) :
    resolventSet R (-a) = -resolventSet R a := by
  simp_rw [Set.ext_iff, Set.mem_neg, spectrum.mem_resolventSet_iff, sub_neg_eq_add, map_neg,
    ← neg_add', IsUnit.neg_iff, implies_true]

namespace ContinuousLinearMap

open InnerProductSpace RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E)

-- waiting on parallelogram law
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
  rwa [inner_smul_right, re_ofReal_mul, ← norm_sq_eq_re_inner,
    inv_mul_eq_div, sq, mul_self_div_self, abs_norm] at key

end ContinuousLinearMap

section spectral

open Module.End

section pain

open Complex TensorProduct

open InnerProductSpace RCLike

theorem ContinuousLinearMap.rayleighQuotient_le_of_mem_resolventSet
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    {T : X →L[𝕜] X} (t : ℝ) (ht : 0 < t) (hT' : (algebraMap ℝ 𝕜) t ∈ resolventSet 𝕜 T) :
    ∃ c > 0, ∀ x, T.rayleighQuotient x ≤ (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c := by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := (antilipschitzWith_iff_exists_mul_le_mul _).mp
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
  apply le_antisymm (spectrum.spectralRadius_le_nnnorm T) -- does this actually require complete?
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
theorem isCompactOperator_id_iff_locallyCompactSpace
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] :
    IsCompactOperator (id : G → G) ↔ LocallyCompactSpace G :=
  ⟨fun ⟨_, hK, hK0⟩ ↦ hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ ↦ exists_compact_mem_nhds 0⟩

-- PRed
theorem LinearMap.isCompactOperator_one_iff_finiteDimensional {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
    [LocallyCompactSpace 𝕜] :
    IsCompactOperator (1 : E →ₗ[𝕜] E) ↔ FiniteDimensional 𝕜 E := by
  rw [Module.End.coe_one, isCompactOperator_id_iff_locallyCompactSpace]
  exact ⟨fun _ ↦ FiniteDimensional.of_locallyCompactSpace 𝕜,
    fun h ↦ LocallyCompactSpace.of_finiteDimensional_of_complete 𝕜 E⟩

-- PRed
theorem ContinuousLinearMap.isCompactOperator_one_iff_finiteDimensional
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace 𝕜] [LocallyCompactSpace 𝕜] :
    IsCompactOperator (1 : E →L[𝕜] E) ↔ FiniteDimensional 𝕜 E := by
  exact LinearMap.isCompactOperator_one_iff_finiteDimensional

theorem ContinuousLinearMap.isClosed_genEigenspace {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T1Space M]
    [ContinuousConstSMul R M] [IsTopologicalAddGroup M]
    (f : M →L[R] M)
    (μ : R) (n : ℕ) : IsClosed (genEigenspace (f : Module.End R M) μ n : Set M) := by
  rw [genEigenspace_nat, one_eq_id, ← coe_id, ← coe_smul, ← coe_sub, ← coe_pow]
  apply ContinuousLinearMap.isClosed_ker

theorem ContinuousLinearMap.isClosed_eigenspace {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [T1Space M]
    [ContinuousConstSMul R M] [IsTopologicalAddGroup M]
    (f : M →L[R] M)
    (μ : R) : IsClosed (eigenspace (f : Module.End R M) μ : Set M) := by
  rw [Module.End.eigenspace_def]
  exact (f - μ • (1 : M →L[R] M) : M →L[R] M).isClosed_ker

theorem spectral_theorem' (hT : IsCompactOperator T) (hT' : T.IsSymmetric) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace (T : Module.End 𝕜 X) μ) := by
  -- this should be a lemma...
  have : IsClosed (eigenspace (T : Module.End 𝕜 X) μ : Set X) := by
    rw [Module.End.eigenspace_def]
    exact (T - μ • 1).isClosed_ker
  have inv : ∀ x ∈ eigenspace (T : Module.End 𝕜 X) μ, T x ∈ eigenspace (T : Module.End 𝕜 X) μ := by
    intro x hx
    rw [mem_eigenspace_iff, ContinuousLinearMap.coe_coe] at hx ⊢
    rw [hx, map_smul, hx]
  have : T.restrict inv = μ • 1 := by
    ext x
    exact mem_eigenspace_iff.mp x.2
  have h2 := hT.restrict' inv
  have h3 := hT'.restrict_invariant inv
  rw [this] at h2
  replace h2 := (IsCompactOperator.smul_iff₀ hμ).mp h2
  rw [LinearMap.isCompactOperator_one_iff_finiteDimensional] at h2
  exact h2

end spectral

-- goal: prove that characters separate points
-- If G is a nontrivial group, then convolving with a function h gives a compact operator on L^2(G)
-- and the spectral theorem gives a decomposition of L^2(G) into finite-dimensional representations
-- and as long as one of these is nontrivial, then we can get a non-trivial irreducible
-- representation which must be one dimensional by Schur's lemma.
