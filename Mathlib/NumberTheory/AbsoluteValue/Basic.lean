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

/-!
# Extensions of absolute values
-/

@[expose] public noncomputable section

-- todo: PR
instance (K : Type*) [NormedField K] [CompleteSpace K] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue K)) :=
  IsometryEquiv.completeSpace
  { __ := WithAbs.equiv (NormedField.toAbsoluteValue K)
    isometry_toFun := by simp [AddMonoidHomClass.isometry_iff_norm, WithAbs.norm_eq_apply_ofAbs] }

open TensorProduct

namespace AbsoluteValue

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) (T : Type*) [CommSemiring T] [Algebra T R] [FaithfulSMul T R]

-- #42566
def under : AbsoluteValue T S :=
  v.comp (FaithfulSMul.algebraMap_injective T R)

end AbsoluteValue

-- #42542
namespace AbsoluteValue

section algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) [w.LiesOver v]

theorem WithAbs.isometry_map : Isometry (WithAbs.map v w (algebraMap K L)) := by
  rw [← LiesOver.comp_eq w v]
  exact AddMonoidHomClass.isometry_of_norm _ fun x ↦ rfl

@[instance_reducible]
def algebraOfLiesOver : Algebra v.Completion w.Completion :=
  (UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
    (WithAbs.isometry_map v w).continuous).toAlgebra

instance : letI := algebraOfLiesOver v w
    ContinuousSMul v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  continuousSMul_of_algebraMap v.Completion w.Completion
    (UniformSpace.Completion.isometry_mapRingHom (WithAbs.isometry_map v w)).continuous

instance : letI := algebraOfLiesOver v w
    IsScalarTower K v.Completion w.Completion :=
  let := algebraOfLiesOver v w
  IsScalarTower.of_algebraMap_eq fun x ↦ (UniformSpace.Completion.mapRingHom_coe
    (WithAbs.isometry_map v w).continuous (WithAbs.toAbs v x)).symm

variable [Algebra v.Completion w.Completion] [ContinuousSMul v.Completion w.Completion]
  [IsScalarTower K v.Completion w.Completion]

theorem algebraMap_eq_mapRingHom :
    algebraMap v.Completion w.Completion =
      UniformSpace.Completion.mapRingHom (WithAbs.map v w (algebraMap K L))
        (WithAbs.isometry_map v w).continuous := by
  symm
  apply DFunLike.ext'
  apply UniformSpace.Completion.extension_unique
  · exact (UniformSpace.Completion.uniformContinuous_coe (WithAbs w)).comp
      (WithAbs.isometry_map v w).uniformContinuous
  · apply uniformContinuous_addMonoidHom_of_continuous
    apply continuous_algebraMap
  · intro x
    exact IsScalarTower.algebraMap_apply K v.Completion w.Completion x.ofAbs

theorem algebra_eq : ‹_› = algebraOfLiesOver v w := by
  apply Algebra.algebra_ext
  rw [algebraMap_eq_mapRingHom v w]
  intro r
  rw [UniformSpace.Completion.mapRingHom_apply]
  rfl

instance [Module.Finite K L] : Module.Finite v.Completion w.Completion := by
  sorry

end algebra

section localDegree

variable {L : Type*} [Field L] (w : AbsoluteValue L ℝ) (K : Type*) [Field K] [Algebra K L]

-- #42566
instance : w.LiesOver (w.under K) := ⟨rfl⟩

def localDegree : ℕ :=
  letI v := w.under K
  letI := algebraOfLiesOver v w
  Module.finrank v.Completion w.Completion

end localDegree

section localDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v] [Algebra v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]

theorem localDegree_eq : w.localDegree K = Module.finrank v.Completion w.Completion := by
  have := LiesOver.comp_eq w v
  rw [localDegree, algebra_eq v w]
  subst this
  rfl

end localDegree

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
def completion : AbsoluteValue v.Completion ℝ := NormedField.toAbsoluteValue v.Completion

-- this might just be a bad lemma
theorem coe_completion : ⇑v.completion = UniformSpace.Completion.extension (v ∘ WithAbs.ofAbs) :=
  rfl

theorem uniformContinuous_completion : UniformContinuous v.completion := uniformContinuous_norm

variable {v}

theorem completion_apply (x : v.Completion) : v.completion x = ‖x‖ :=
  rfl

instance : v.completion.LiesOver v where
  comp_eq := by
    ext x
    exact UniformSpace.Completion.norm_coe (WithAbs.toAbs v x)

instance : CompleteSpace (WithAbs v.completion) :=
  inferInstanceAs (CompleteSpace (WithAbs (NormedField.toAbsoluteValue v.Completion)))

end completion

section extension


open scoped Topology

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (L : Type*) [Field L] [Algebra K L]

def extension [Module.Finite K L] [CompleteSpace (WithAbs v)] : AbsoluteValue L ℝ := by
  sorry

instance [Module.Finite K L] [CompleteSpace (WithAbs v)] : (v.extension L).LiesOver v where
  comp_eq := by
    sorry

-- once you have extensions of absolute values on complete fields, the Artinian machinery
-- let's you pick an arbitrary extension if desired

end extension

section liesOver_iff

variable {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L] [PartialOrder S]
  [Nontrivial L] [Semiring S]

/-- An absolute value `w` of `L / K` lies over the absolute value `v` of `K` if `v` is the
restriction of `w` to `K`. -/
theorem liesOver_iff {w : AbsoluteValue L S} {v : AbsoluteValue K S} :
    w.LiesOver v ↔ w.under K = v :=
  ⟨fun h ↦ h.comp_eq, fun h ↦ ⟨h⟩⟩

end liesOver_iff

section under_under

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S]
    (v : AbsoluteValue R S) (T : Type*) [CommSemiring T] [Algebra T R] [FaithfulSMul T R]
    (U : Type*) [CommSemiring U] [Algebra U R] [Algebra U T] [IsScalarTower U T R]
    [FaithfulSMul U T] [FaithfulSMul U R]

variable {T} in
theorem under_apply (x : T) : v.under T x = v (algebraMap T R x) := rfl

-- #42566
theorem under_under : (v.under T).under U = v.under U := by
  ext x
  simp [under_apply, ← IsScalarTower.algebraMap_apply]

theorem LiesOver.trans
    {R S T U : Type*} [Field R] [Semiring S] [PartialOrder S]
    [Field T] [Algebra T R]
    [Field U] [Algebra U R] [Algebra U T] [IsScalarTower U T R]
    (vU : AbsoluteValue U S) (vT : AbsoluteValue T S) (vR : AbsoluteValue R S)
    [vR.LiesOver vT] [vT.LiesOver vU] : vR.LiesOver vU := by
  rw [liesOver_iff] at *
  rw [← vR.under_under T]
  grind

end under_under

section sum

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

instance : IsArtinianRing (v.Completion ⊗[K] L) := .of_finite v.Completion (v.Completion ⊗[K] L)

instance : Finite (PrimeSpectrum (v.Completion ⊗[K] L)) := inferInstance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
def absoluteValuesOverEquiv : v.absoluteValuesOver L ≃ PrimeSpectrum (v.Completion ⊗[K] L) where
  toFun w := by
    letI := algebraOfLiesOver v w.val
     -- can weaken to be over K if desired
    letI φ : v.Completion ⊗[K] L →ₐ[v.Completion] w.val.Completion := by
      apply Algebra.TensorProduct.productLeftAlgHom
      · apply Algebra.ofId
      · apply IsScalarTower.toAlgHom
    exact ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩
  invFun p := by
    letI K_v := v.Completion
    letI L_w := (K_v ⊗[K] L) ⧸ p.asIdeal
    haveI : p.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p.asIdeal
    letI : Field L_w := Ideal.Quotient.field p.asIdeal
    letI w : AbsoluteValue L_w ℝ := v.completion.extension L_w -- extend valuation on K_v to L_w
    refine ⟨w.under L, ?_⟩
    rw [mem_absoluteValuesOver, liesOver_iff, under_under w L K, ← liesOver_iff]
    exact LiesOver.trans v v.completion w
  left_inv w := by
    let := algebraOfLiesOver v w.val
    let K_v := v.Completion
    let L_w := w.val.Completion
    let φ : K_v ⊗[K] L →ₐ[K_v] L_w := by
      apply Algebra.TensorProduct.productLeftAlgHom
      · apply Algebra.ofId
      · apply IsScalarTower.toAlgHom
    let p := RingHom.ker φ
    have : p.IsPrime := RingHom.ker_isPrime φ
    have : p.IsMaximal := IsArtinianRing.isMaximal_of_isPrime p
    let L_w' := K_v ⊗[K] L ⧸ p
    let : Field L_w' := Ideal.Quotient.field p
    ext1
    change (v.completion.extension L_w').under L = w
    suffices (v.completion.extension L_w).under L = w by
      sorry
    ext x
    sorry
  right_inv p := by
    ext1
    simp
    sorry

-- `A = L ⊗[K] K_v = ∏ A_m` is an Artinian ring
-- absolutes values over `L` are in bijection with maximal ideals of `A`
-- `L_w ≃ A_m/m`
-- `∑_w [L_w : K_v] = ∑_m dim_(K_v) (A_m/m) ≤ ∑_m dim_(K_v) A_m = dim_(K_v) A = [L : K]`

instance : Finite (v.absoluteValuesOver L) := Finite.of_equiv _ (v.absoluteValuesOverEquiv L).symm

instance : Nonempty (v.absoluteValuesOver L) := (v.absoluteValuesOverEquiv L).nonempty

/-- The fundamental inequality. -/
theorem sum_eq [Fintype (v.absoluteValuesOver L)]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], Algebra v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], ContinuousSMul v.Completion w.Completion]
    [∀ (w : AbsoluteValue L ℝ) [w.LiesOver v], IsScalarTower K v.Completion w.Completion] :
    ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤ Module.finrank K L := by
  let A := v.Completion ⊗[K] L
  have : Fintype (PrimeSpectrum A) := Fintype.ofEquiv _ (v.absoluteValuesOverEquiv L)
  rw [← Module.finrank_baseChange (R := v.Completion), IsArtinianRing.finrank_eq_sum_primeSpectrum]
  change ∑ w : v.absoluteValuesOver L, w.val.localDegree L ≤
    ∑ p : PrimeSpectrum A, Module.finrank v.Completion (Localization.AtPrime p.asIdeal)
  -- these are both finranks, want map injective `L_w → A_m`
  sorry

end sum

section ramification

end ramification

end AbsoluteValue
