/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!

# Compact Hausdorff Rings

## Main results
- `IsArtinianRing.finite_of_compactSpace_of_t2Space`:
  Compact Hausdorff Artinian rings are finite (and thus discrete).
- `Ideal.isOpen_of_isMaximal`:
  Maximal ideals are open in compact Hausdorff Noetherian rings.
- `IsLocalRing.isOpen_iff_finite_quotient`:
  An ideal in a compact Hausdorff Noetherian local ring is open iff it has finite index.
- `IsDedekindDomain.isOpen_iff`:
  An ideal in a compact Hausdorff Dedekind domain (that is not a field) is open iff it is non-zero.

## Future projects
Show that compact Hausdorff rings are totally disconnected and linearly topologized.
See https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite

-/

@[expose] public section

attribute [local instance] Ideal.Quotient.field Fintype.ofFinite finite_of_compact_of_discrete
  DivisionRing.finite_of_compactSpace_of_t2Space

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] [CompactSpace R] [T2Space R]

namespace IsArtinianRing

/-- Compact Hausdorff Artinian (commutative) rings are finite. This is not an instance, as it would
apply to every `Finite` goal, causing slowly failing typeclass search in some cases. -/
theorem finite_of_compactSpace_of_t2Space [IsArtinianRing R] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    gcongr
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal, le_sInf_iff]
    exact fun I hI ↦ Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ ↦ IsNoetherian.noetherian _) (fun _ _ ↦ inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

end IsArtinianRing

section IsNoetherianRing

variable [IsNoetherianRing R]

lemma Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X := R) I :=
  have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))

lemma Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : ℕ) :
    IsOpen (X := R) ↑(I ^ n) :=
  have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

-- Note: this is only by infer_instance because of the opened local instances.
instance (priority := low) (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := inferInstance

end IsNoetherianRing

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
lemma isOpen_maximalIdeal_pow (n : ℕ) :
    IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  Ideal.isOpen_pow_of_isMaximal _ _

variable (R) in
lemma isOpen_maximalIdeal : IsOpen (X := R) ↑(maximalIdeal R) :=
  Ideal.isOpen_of_isMaximal _

instance finite_residueField_of_compactSpace : Finite (ResidueField R) :=
  inferInstanceAs (Finite (R ⧸ _))

lemma isOpen_iff_finite_quotient {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

end IsLocalRing

section IsDedekindDomain

lemma IsDedekindDomain.isOpen_of_ne_bot
    [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) :
    IsOpen (X := R) I := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI,
    finprod_eq_finset_prod_of_mulSupport_subset _
      (s := (Ideal.finite_mulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ ↦ IsNoetherian.noetherian _) fun _ _ ↦ ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

lemma IsDedekindDomain.isOpen_iff
    [IsDedekindDomain R] (hR : ¬ IsField R) {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ := by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

lemma IsDiscreteValuationRing.isOpen_iff
    [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ :=
  IsDedekindDomain.isOpen_iff (not_isField R)

end IsDedekindDomain

section CompactHausdorff

@[to_additive] -- todo: to_additivize `instIsMulTorsionFree` in `Algebra/Group/Subgroup/Basic`.
instance instIsMulTorsionFree
    {G : Type*} [Group G] (H : Subgroup G) [IsMulTorsionFree G] : IsMulTorsionFree H where
  pow_left_injective n hn a b := by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

open Pointwise in
def Ideal.connectedComponentOfZero
    (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] : Ideal R where
  __ := AddSubgroup.connectedComponentOfZero R
  smul_mem' := by
    intro c x h
    let f : R → R := fun y ↦ c * y
    have key : Continuous f := continuous_mul_left c
    suffices f '' connectedComponent (0 : R) ⊆ connectedComponent (0 : R) from this ⟨x, h, rfl⟩
    apply IsConnected.subset_connectedComponent
    · exact isConnected_connectedComponent.image _ key.continuousOn
    · exact ⟨0, mem_connectedComponent, mul_zero c⟩

instance (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    (Ideal.connectedComponentOfZero R).IsTwoSided where
  mul_mem_of_left := by
    intro x c h
    let f : R → R := fun y ↦ y * c
    have key : Continuous f := continuous_mul_right c
    suffices f '' connectedComponent (0 : R) ⊆ connectedComponent (0 : R) from this ⟨x, h, rfl⟩
    apply IsConnected.subset_connectedComponent
    · exact isConnected_connectedComponent.image _ key.continuousOn
    · exact ⟨0, mem_connectedComponent, zero_mul c⟩

-- this might not even need abelian?
@[to_additive]
noncomputable def Group.rootable
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [ConnectedSpace A] : RootableBy A ℕ := by
  apply rootableByOfPowLeftSurj
  intro n hn0

  -- quotient is compact, connected, abelian, exponent n, which should imply trivial

  -- might require the existence of a nontrivial character on the compact abelian quotient
  -- image of the character is a connected, exponent n subgroup of torus, hence trivial

  -- in general true for torsion groups by the same argument or by Baire category theorem

  sorry

@[to_additive]
theorem ContinuousMonoidHom.mul_apply {A B : Type*} [Monoid A] [CommMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul B]
    (f g : ContinuousMonoidHom A B) (a : A) : (f * g) a = f a * g a := by
  rfl

@[to_additive]
theorem ContinuousMonoidHom.pow_apply {A B : Type*} [Monoid A] [CommMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul B]
    (f : ContinuousMonoidHom A B) (n : ℕ) (a : A) : (f ^ n) a = (f a) ^ n := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [pow_succ, ContinuousMonoidHom.mul_apply, ih]

@[to_additive]
theorem CommGroup.foo {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [ConnectedSpace A] (K : Subgroup (ContinuousMonoidHom A A))
    (hK : IsCompact (K : Set (ContinuousMonoidHom A A))) :
    K = ⊥ := by
  have A_rootable : RootableBy A ℕ := Group.rootable A
  have : IsMulTorsionFree (ContinuousMonoidHom A A) := by
    constructor
    intro n hn0 χ χ' h
    rw [DFunLike.ext_iff] at h ⊢
    intro x
    specialize h (RootableBy.root x n)
    simp only [ContinuousMonoidHom.pow_apply, ← map_pow, A_rootable.root_cancel x hn0] at h
    exact h
  -- K is compact
  -- but K cannot be discrete (else finite, hence trivial by torsion-free)
  -- pick n * f → 0 in topology of uniform convergence
  -- so n * f eventually inside U
  -- but image of f is divisible group, so image of f is inside U
  -- but this holds for any nbhd, so image is 0
  sorry

instance {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] : TotallyDisconnectedSpace R := by
  let C₀ : Ideal R := Ideal.connectedComponentOfZero R
  suffices C₀ = ⊥ by
    replace this : connectedComponent (0 : R) = {0} := SetLike.ext'_iff.mp this
    rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
    intro x
    have key := (continuous_add_left (-x)).image_connectedComponent_subset x
    rw [neg_add_cancel, this, Set.image_subset_iff] at key
    -- this can probably be done more cleanly...
    exact Set.subsingleton_of_forall_eq x (by simpa using key)
  have C₀_isClosed : IsClosed (C₀ : Set R) := isClosed_connectedComponent
  have C₀_isCompact : IsCompact (C₀ : Set R) := C₀_isClosed.isCompact
  have : CompactSpace C₀ := isCompact_iff_compactSpace.mp C₀_isCompact
  have C₀_isConnected : IsConnected (C₀ : Set R) := isConnected_connectedComponent
  have : ConnectedSpace C₀ := isConnected_iff_connectedSpace.mp C₀_isConnected
  have : Ideal.IsTwoSided C₀ := inferInstance

  let E := ContinuousAddMonoidHom C₀ C₀
  let f : ContinuousAddMonoidHom R E := -- technically also a ring hom, but not needed here
  { toFun := fun r ↦ { toFun := fun c ↦ r • c
                       map_zero' := by simp
                       map_add' := by simp [smul_add]
                       continuous_toFun := by fun_prop }
    map_zero' := by apply DFunLike.ext; intros; apply zero_smul
    map_add' := by intros; apply DFunLike.ext; intros; apply add_smul
    continuous_toFun := by
      -- should be doable
      sorry }

  have key := AddCommGroup.foo f.range (isCompact_range f.continuous)
  replace key : f 1 = 0 := by
    rw [← AddSubgroup.mem_bot, ← key]
    exact ⟨1, rfl⟩
  rw [eq_bot_iff]
  intro c hc
  replace key : f 1 ⟨c, hc⟩ = (0 : E) ⟨c, hc⟩ := by rw [key]
  rw [Ideal.mem_bot]
  rw [Subtype.ext_iff] at key
  change 1 • c = 0 at key
  rwa [one_smul] at key

end CompactHausdorff
