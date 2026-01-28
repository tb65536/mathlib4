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
    [CompactSpace A] [ConnectedSpace A] [T2Space A] : RootableBy A ℕ := by
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
    rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

open Pointwise in
theorem CommGroup.bar {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] (f : A) (U : Set A) (hU : U ∈ nhds 1) : ∃ n > 0, f ^ n ∈ U := by
  obtain ⟨V, hV1, -, hV, hVU⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  let g : ℕ → A := fun n ↦ f ^ n
  let F : Filter A := Filter.map g Filter.atTop
  have hF : F ≤ Filter.principal Set.univ := by
    simp
  obtain ⟨q, hqK, hqF⟩ := isCompact_univ hF
  rw [clusterPt_iff_frequently] at hqF
  specialize hqF (q • V) (smul_mem_nhds_self.mpr hV1)
  rw [Filter.frequently_map] at hqF
  have hq := Filter.Frequently.forall_exists_of_atTop hqF
  obtain ⟨j, -, hj⟩ := hq 0
  obtain ⟨k, hjk : j < k, hk⟩ := hq (j + 1)
  have key : g k * (g j)⁻¹ ∈ U := by
    have key := Set.div_mem_div hk hj
    rw [Set.smul_div_smul_comm, div_self', one_smul, div_eq_mul_inv, div_eq_mul_inv, hV] at key
    exact hVU key
  rw [← pow_sub _ hjk.le] at key
  exact ⟨k - j, Nat.sub_pos_of_lt hjk, key⟩

open Pointwise in
theorem AddCommGroup.bar {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [CompactSpace A] (f : A) (U : Set A) (hU : U ∈ nhds 0) : ∃ n > 0, n • f ∈ U := by
  obtain ⟨V, hV0, -, hV, hVU⟩ := exists_closed_nhds_zero_neg_eq_add_subset hU
  let g : ℕ → A := fun n ↦ n • f
  let F : Filter A := Filter.map g Filter.atTop
  have hF : F ≤ Filter.principal Set.univ := by
    simp
  obtain ⟨q, hqK, hqF⟩ := isCompact_univ hF
  rw [clusterPt_iff_frequently] at hqF
  specialize hqF (q +ᵥ V) (vadd_mem_nhds_self.mpr hV0)
  rw [Filter.frequently_map] at hqF
  have hq := Filter.Frequently.forall_exists_of_atTop hqF
  obtain ⟨j, -, hj⟩ := hq 0
  obtain ⟨k, hjk : j < k, hk⟩ := hq (j + 1)
  have key : g k + - g j ∈ U := by
    have key := Set.sub_mem_sub hk hj
    rw [Set.vadd_sub_vadd_comm, sub_self, zero_vadd, sub_eq_add_neg, sub_eq_add_neg, hV] at key
    exact hVU key
  rw [← sub_nsmul _ hjk.le] at key
  exact ⟨k - j, Nat.sub_pos_of_lt hjk, key⟩

open Pointwise in
@[to_additive]
theorem CommGroup.foo {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [ConnectedSpace A] [T2Space A] (K : Subgroup (ContinuousMonoidHom A A))
    (hK : IsCompact (K : Set (ContinuousMonoidHom A A))) :
    K = ⊥ := by
  have A_rootable : RootableBy A ℕ := Group.rootable A
  rw [eq_bot_iff]
  intro f hf
  ext a
  rw [ContinuousMonoidHom.one_toFun]
  by_contra! ha
  let U : Set A := {f a}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hU1 : 1 ∈ U := ha.symm
  let W : Set (A →ₜ* A) := {f | Set.MapsTo f Set.univ U}
  have hW : IsOpen W :=
    (ContinuousMonoidHom.isInducing_toContinuousMap A A).continuous.isOpen_preimage _
      (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hU)
  have hW1 : 1 ∈ W := by simpa [W]
  replace hW1 : W ∈ nhds 1 := hW.mem_nhds hW1
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨n, hn0, hnf⟩ := CommGroup.bar ⟨f, hf⟩ (Subtype.val ⁻¹' W)
    (continuousAt_subtype_val.preimage_mem_nhds (by simpa))
  rw [Set.mem_preimage, Subgroup.coe_pow, Subtype.coe_mk] at hnf
  rw [Set.mem_setOf_eq, Set.mapsTo_univ_iff, ← Set.range_subset_iff] at hnf
  change (f ^ n).range ≤ U at hnf
  suffices f.range ≤ (f ^ n).range by
    exact (Set.Subset.trans this hnf) ⟨a, rfl⟩ rfl
  rintro - ⟨b, rfl⟩
  use RootableBy.root b n
  simp [ContinuousMonoidHom.pow_apply,
    ← map_pow, RootableBy.root_cancel b hn0.ne']

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
  let f : ContinuousAddMonoidHom R (ContinuousAddMonoidHom C₀ C₀) :=
  { toFun r :=
    { toFun := fun c ↦ r • c
      map_zero' := by simp
      map_add' := by simp [smul_add]
      continuous_toFun := by fun_prop }
    map_zero' := by apply DFunLike.ext; intros; apply zero_smul
    map_add' := by intros; apply DFunLike.ext; intros; apply add_smul
    continuous_toFun := ContinuousAddMonoidHom.continuous_of_continuous_uncurry _ continuous_smul }
  have key := AddCommGroup.foo f.range (isCompact_range f.continuous)
  refine eq_bot_iff.mpr fun c hc ↦ ?_
  replace key : f.toAddMonoidHom 1 ⟨c, hc⟩ = (0 : ContinuousAddMonoidHom C₀ C₀) ⟨c, hc⟩ := by
    rw [AddMonoidHom.range_eq_bot_iff.mp key, AddMonoidHom.zero_apply]
  replace key : (1 : R) • c = 0 := Subtype.ext_iff.mp key
  rwa [one_smul] at key

end CompactHausdorff
