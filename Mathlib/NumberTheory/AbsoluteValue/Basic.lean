/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Subadditive
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Extensions of absolute values
-/

@[expose] public section

-- PRed
namespace AbsoluteValue

instance {F1 F2 F3 : Type*} [Field F1] [Field F2] [Field F3]
    [Algebra F1 F2] [Algebra F1 F3] [Algebra F2 F3] [IsScalarTower F1 F2 F3]
    (v1 : AbsoluteValue F1 ℝ) (v2 : AbsoluteValue F2 ℝ) (v3 : AbsoluteValue F3 ℝ)
    [v2.LiesOver v1] [v3.LiesOver v1] [v3.LiesOver v2]
    [Algebra v1.Completion v2.Completion] [IsScalarTower F1 v1.Completion v2.Completion]
    [Algebra v1.Completion v3.Completion] [IsScalarTower F1 v1.Completion v3.Completion]
    [Algebra v2.Completion v3.Completion] [IsScalarTower F2 v2.Completion v3.Completion]
    [ContinuousSMul v1.Completion v2.Completion]
    [ContinuousSMul v1.Completion v3.Completion]
    [ContinuousSMul v2.Completion v3.Completion] :
    IsScalarTower v1.Completion v2.Completion v3.Completion := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [AbsoluteValue.Completion.algebraMap_eq, UniformSpace.Completion.mapRingHom_comp,
    ← WithAbs.map_comp, ← IsScalarTower.algebraMap_eq]

section localDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v] [Algebra v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

noncomputable def localDegree (K : Type*) [Field K] [Algebra K L] : ℕ :=
  letI v := w.under K
  letI := Completion.algebraOfLiesOver v w
  Module.finrank v.Completion w.Completion

theorem localDegree_eq : w.localDegree K = Module.finrank v.Completion w.Completion := by
  have := LiesOver.under_eq w v
  rw [localDegree, Completion.algebra_eq v w]
  subst this
  rfl

theorem localDegree_mul_localDegree (F : Type*) [Field F] [Algebra F K] [Algebra F L]
    [IsScalarTower F K L] : v.localDegree F * w.localDegree K = w.localDegree F := by
  let v₀ := v.under F
  let : Algebra v₀.Completion v.Completion := Completion.algebraOfLiesOver v₀ v
  have : w.LiesOver v₀ := LiesOver.trans v₀ v w -- maybe this could be an instance
  let : Algebra v₀.Completion w.Completion := Completion.algebraOfLiesOver v₀ w
  rw [localDegree_eq v₀ v, localDegree_eq v w, localDegree_eq v₀ w]
  rw [Module.finrank_mul_finrank]

end localDegree

end AbsoluteValue

-- todo: PR
instance (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue K)) :=
  IsometryEquiv.completeSpace
  { __ := WithAbs.equiv (NormedField.toAbsoluteValue K)
    isometry_toFun := by simp [AddMonoidHomClass.isometry_iff_norm, WithAbs.norm_eq_apply_ofAbs] }

open TensorProduct

namespace AbsoluteValue

section PRed

variable {K L : Type*} [SeminormedCommRing K] [DivisionRing L] [Algebra K L]
  [Algebra.IsIntegral K L]

/-- A power-multiplicative norm on an algebraic extension of a trivially normed field is trivial. -/
theorem AlgebraNorm.eq_one_of_trivial
    (hK : ∀ x : K, ‖x‖ ≤ 1) (f : AlgebraNorm K L) (hf : IsPowMul f)
    (x : L) (hx : x ≠ 0) : f x = 1 := by
  sorry

end PRed

section algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v]

variable [Algebra v.Completion w.Completion] [ContinuousSMul v.Completion w.Completion]
  [IsScalarTower K v.Completion w.Completion]

theorem closed_span_singleton_normedField
    {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    IsClosed (Submodule.span 𝕜 {x} : Set E) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [Submodule.span_singleton_eq_range]
  have ha : AntilipschitzWith ‖x‖₊⁻¹ (fun c : 𝕜 => c • x) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    simp only [dist_eq_norm, ← sub_smul, norm_smul,
      NNReal.coe_inv, coe_nnnorm]
    rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx),
      mul_one]
  exact ha.isClosed_range
    (ContinuousLinearMap.toSpanSingleton 𝕜 x).uniformContinuous

theorem closed_fg_normedField
    {𝕜 E : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (S : Submodule 𝕜 E) (hS : S.FG) :
    IsClosed (S : Set E) := by
  induction S, hS using Submodule.fg_sup_span_induction with
  | bot => simp
  | sup S x hS ih =>
    let : IsClosed (S : Set E) := ih
    rw [← Submodule.comap_map_mkQ,
      Submodule.map_span, Set.image_singleton]
    exact (closed_span_singleton_normedField (S.mkQ x)).preimage
      S.continuous_mkQ

instance [Module.Finite K L] : Module.Finite v.Completion w.Completion := by
  have hi : Isometry (algebraMap v.Completion w.Completion) := by
    rw [AbsoluteValue.Completion.algebraMap_eq v w]
    exact UniformSpace.Completion.isometry_mapRingHom
      (WithAbs.isometry_map v w)
  let : NormedAlgebra v.Completion w.Completion :=
    { (inferInstance : Algebra v.Completion w.Completion) with
      norm_smul_le := fun a b => by
        rw [Algebra.smul_def, norm_mul,
          (AddMonoidHomClass.isometry_iff_norm _).mp hi a] }
  let f : L →ₗ[K] w.Completion :=
    (IsScalarTower.toAlgHom K L w.Completion).toLinearMap
  let S : Submodule v.Completion w.Completion :=
    Submodule.span v.Completion (f.range : Set w.Completion)
  have hS : S.FG :=
    (Submodule.FG.of_finite (N := f.range)).span
  have hclosed : IsClosed (S : Set w.Completion) :=
    closed_fg_normedField S hS
  have htop : S = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    refine UniformSpace.Completion.induction_on x hclosed ?_
    intro a
    exact Submodule.subset_span ⟨a.ofAbs, rfl⟩
  rw [Module.finite_def]
  exact htop ▸ hS

end algebra

section absoluteValuesOver

variable {K S : Type*} [Field K] [PartialOrder S] [Semiring S] (v : AbsoluteValue K S)
  (L : Type*) [CommRing L] [Nontrivial L] [Algebra K L]

def absoluteValuesOver : Set (AbsoluteValue L S) :=
  {w | w.LiesOver v}

variable {v L}

@[simp]
theorem mem_absoluteValuesOver {w : AbsoluteValue L S} :
    w ∈ v.absoluteValuesOver L ↔ w.LiesOver v :=
  .rfl

instance (w : absoluteValuesOver v L) : w.val.LiesOver v := w.2

end absoluteValuesOver

section completion

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The extended absolute value on `v.Completion`. -/
noncomputable def completion : AbsoluteValue v.Completion ℝ :=
  NormedField.toAbsoluteValue v.Completion

theorem uniformContinuous_completion : UniformContinuous v.completion := uniformContinuous_norm

variable {v}

theorem completion_apply (x : v.Completion) : v.completion x = ‖x‖ :=
  rfl

instance : v.completion.LiesOver v where
  under_eq := by
    ext x
    exact UniformSpace.Completion.norm_coe (WithAbs.toAbs v x)

instance : CompleteSpace (WithAbs v.completion) :=
  inferInstanceAs (CompleteSpace (WithAbs (NormedField.toAbsoluteValue v.Completion)))

end completion

section extension


open scoped Topology

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]

-- spectral norm stuff
def extension [Module.Finite K L] [CompleteSpace (WithAbs v)] : AbsoluteValue L ℝ := by
  sorry

-- spectral norm stuff
instance [Module.Finite K L] [CompleteSpace (WithAbs v)] : (v.extension L).LiesOver v where
  under_eq := by
    sorry

-- spectral norm stuff
instance [Module.Finite K L] [CompleteSpace (WithAbs v)] :
    CompleteSpace (WithAbs (v.extension L)) := by
  sorry

-- once you have extensions of absolute values on complete fields, the Artinian machinery
-- let's you pick an arbitrary extension if desired

end extension

section sum

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

instance : IsArtinianRing (v.Completion ⊗[K] L) := .of_finite v.Completion (v.Completion ⊗[K] L)

instance : Finite (PrimeSpectrum (v.Completion ⊗[K] L)) := inferInstance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def absoluteValuesOverEquiv : v.absoluteValuesOver L ≃ PrimeSpectrum (v.Completion ⊗[K] L) where
  toFun w :=
    letI K_v := v.Completion
    letI L_w := w.val.Completion
    letI : Algebra K_v L_w := Completion.algebraOfLiesOver v w.val
    letI φ : K_v ⊗[K] L →ₐ[K_v] L_w := -- can weaken to be over K if desired
      Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K_v L_w) (Algebra.algHom K L L_w)
    ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  invFun p :=
    letI K_v := v.Completion
    letI L_w := (K_v ⊗[K] L) ⧸ p.asIdeal
    letI : Field L_w := Ideal.Quotient.field p.asIdeal
    letI w : AbsoluteValue L_w ℝ := v.completion.extension L_w
    ⟨w.under L, (under_liesOver_iff _).mpr (.trans v v.completion w)⟩
  left_inv w := by
    let K_v := v.Completion
    let L_w := w.val.Completion
    let : Algebra K_v L_w := Completion.algebraOfLiesOver v w.val
    let φ : K_v ⊗[K] L →ₐ[K_v] L_w :=
      Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K_v L_w) (Algebra.algHom K L L_w)
    let p := RingHom.ker φ
    have : p.IsPrime := RingHom.ker_isPrime φ
    let L_w' := K_v ⊗[K] L ⧸ p
    let : Field L_w' := Ideal.Quotient.field p
    ext1
    change (v.completion.extension L_w').under L = w
    let φ' : L_w' →ₐ[K_v] L_w := Ideal.kerLiftAlg φ
    let : Algebra L_w' L_w := φ'.toAlgebra
    have : Module.Finite L_w' L_w := .of_restrictScalars_finite K_v L_w' L_w
    have key : (v.completion.extension L_w').extension L_w = w.val.completion := by
      -- both lie over v.completion
      sorry
    -- RHS lies over w, so LHS also lies over w
    sorry
  right_inv p := by
    let K_v := v.Completion
    let L_w := (K_v ⊗[K] L) ⧸ p.asIdeal
    let : Field L_w := Ideal.Quotient.field p.asIdeal
    let w : AbsoluteValue L_w ℝ := v.completion.extension L_w
    have : w.LiesOver v := (under_liesOver_iff _).mpr (.trans v v.completion w)
    let L_w' := w.Completion
    let : Algebra K_v L_w' := Completion.algebraOfLiesOver v w
    let φ : K_v ⊗[K] L →ₐ[K_v] L_w' :=
      Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K_v L_w') (Algebra.algHom K L L_w')
    ext1
    simp
    -- change RingHom.ker φ = p.asIdeal
    have key : RingHom.ker φ = p.asIdeal := sorry
    convert key
    congr
    -- claim is that ring hom from
    sorry

-- `A = L ⊗[K] K_v = ∏ A_m` is an Artinian ring
-- absolutes values over `L` are in bijection with maximal ideals of `A`
-- `L_w ≃ A_m/m`
-- `∑_w [L_w : K_v] = ∑_m dim_(K_v) (A_m/m) ≤ ∑_m dim_(K_v) A_m = dim_(K_v) A = [L : K]`

instance : Finite (v.absoluteValuesOver L) := Finite.of_equiv _ (v.absoluteValuesOverEquiv L).symm

instance : Nonempty (v.absoluteValuesOver L) := (v.absoluteValuesOverEquiv L).nonempty

/-- The fundamental inequality. -/
theorem sum_localDegree_le [Fintype (v.absoluteValuesOver L)]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], Algebra v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], ContinuousSMul v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], IsScalarTower K v.Completion w.Completion] :
    ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤ Module.finrank K L := by
  let A := v.Completion ⊗[K] L
  have : Fintype (PrimeSpectrum A) := Fintype.ofEquiv _ (v.absoluteValuesOverEquiv L)
  rw [← Module.finrank_baseChange (R := v.Completion), IsArtinianRing.finrank_eq_sum_primeSpectrum]
  change ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤
    ∑ p : PrimeSpectrum A, Module.finrank v.Completion (Localization.AtPrime p.asIdeal)
  transitivity ∑ p : PrimeSpectrum A, Module.finrank v.Completion (A ⧸ p.asIdeal)
  · sorry
  · apply Finset.sum_le_sum
    intro i hi
    -- surjection from A to A ⧸ p factors through the localization
    sorry

end sum

section ramification

end ramification

end AbsoluteValue
